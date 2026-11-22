/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Inkproof.Gpu
import Inkproof.Scene.DisplayList

open Inkproof.Gpu

def sample : List Cmd := [
  ⟨0, [.u32 7]⟩,
  ⟨1, [.u32 7, .words [1, 2, 0xFFFFFFFF]]⟩,
  ⟨4, [.u32 0, .words []]⟩,
  ⟨5, [.u32 7, .u32 3, .u32 2]⟩,
  ⟨6, [.u32 0x11223344]⟩
]

def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"FAIL: {msg}"
  return 1

/-- The generated decoder, run under node, must agree with the Lean decoder. -/
def jsDecodes (dir : System.FilePath) (cs : List Cmd) : IO Bool := do
  let mod := dir / "gpu.mjs"
  IO.FS.writeFile mod js
  let bytes := ", ".intercalate ((encode cs).map (toString ·.toNat))
  let script := s!"import \{ decode } from \"{mod}\";
const cmds = decode(new Uint8Array([{bytes}]));
console.log(JSON.stringify(cmds.map(c => [c.op, c.args.map(a => typeof a === \"number\" ? a : Array.from(a))])));"
  IO.FS.writeFile (dir / "run.mjs") script
  let out ← IO.Process.output { cmd := "node", args := #[(dir / "run.mjs").toString] }
  let arg : Arg → String
    | .u32 n => toString n
    | .words ws => "[" ++ ",".intercalate (ws.map toString) ++ "]"
  let expected := "[" ++ ",".intercalate (cs.map fun c =>
    s!"[{c.op},[" ++ ",".intercalate (c.args.map arg) ++ "]]") ++ "]"
  return out.exitCode == 0 && out.stdout.trimAscii.toString == expected

def one : UInt32 := 0x3F800000
def minusOne : UInt32 := 0xBF800000
def eight : UInt32 := 0x41000000
def eighth : UInt32 := 0x3E000000

/-- Creates the program, uploads a triangle covering the centre as `words`, sets the uniforms and draws it with vertices of `stride` words. -/
def triangleOf (words : List UInt32) (stride : UInt32) : List Cmd := [
  ⟨6, [.u32 0x000000FF]⟩,
  ⟨7, [.u32 1]⟩,
  ⟨0, [.u32 2]⟩,
  ⟨1, [.u32 2, .words words]⟩,
  ⟨3, [.u32 1]⟩,
  ⟨4, [.u32 0, .words [one, one]]⟩,
  ⟨4, [.u32 1, .words [0, 0]]⟩,
  ⟨4, [.u32 2, .words [0]]⟩,
  ⟨4, [.u32 3, .words [eight, eight, eighth, eighth]]⟩,
  ⟨4, [.u32 4, .words [one, 0, 0, one]]⟩,
  ⟨5, [.u32 2, .u32 3, .u32 stride]⟩
]

/-- A triangle of bare positions, so that the direction and the corner take their defaults. -/
def triangle : List Cmd := triangleOf [minusOne, minusOne, one, minusOne, 0, one] 2

/-- The same triangle with a direction and a zero corner on every vertex. -/
def triangle6 : List Cmd :=
  triangleOf [minusOne, minusOne, one, 0, 0, 0, one, minusOne, one, 0, 0, 0, 0, one, one, 0, 0, 0] 6

/-- The commands with a scissor, given as words, set just before the draw. -/
def scissored (cs : List Cmd) (ws : List Int) : List Cmd :=
  cs.flatMap fun c => if c.op == 5 then [⟨8, [.words (ws.map fun v => UInt32.ofNat (Int.toNat v))]⟩, c] else [c]

/-- Runs the generated interpreter on a WebGL2 context in headless Chromium and reads back the centre pixel. -/
def drawsTriangle (dir : System.FilePath) (cs : List Cmd) (expected : String) : IO Bool := do
  IO.FS.writeFile (dir / "gpu.mjs") js
  let bytes := ", ".intercalate ((encode cs).map (toString ·.toNat))
  let script := s!"import \{ chromium } from \"playwright\";
import \{ readFileSync } from \"node:fs\";
const browser = await chromium.launch();
const page = await browser.newPage();
await page.setContent(\"<canvas id=c width=16 height=16></canvas>\");
const src = readFileSync(\"{dir / "gpu.mjs"}\", \"utf8\");
const px = await page.evaluate(async (\{ src, bytes }) => \{
  const gpu = await import(URL.createObjectURL(new Blob([src], \{ type: \"text/javascript\" })));
  const gl = document.getElementById(\"c\").getContext(\"webgl2\", \{ preserveDrawingBuffer: true });
  const state = gpu.newState();
  gpu.run(gl, state, new Uint8Array(bytes));
  const out = new Uint8Array(4);
  gl.readPixels(8, 8, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, out);
  const bufs = Array.from(state.buffers.values());
  const progs = Array.from(state.programs.values(), p => p.program);
  gpu.releaseState(gl, state);
  const alive = bufs.filter(o => gl.isBuffer(o)).length + progs.filter(o => gl.isProgram(o)).length;
  const empty = state.buffers.size + state.programs.size === 0;
  return \{ px: Array.from(out), err: gl.getError(), released: bufs.length > 0 && progs.length > 0 && alive === 0 && empty };
}, \{ src, bytes: [{bytes}] });
await browser.close();
console.log(JSON.stringify(px));"
  let out ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
  IO.eprint out.stderr
  return out.exitCode == 0 && out.stdout.trimAscii.toString == expected

/-- Runs the frame `frame` on a `w` by `h` canvas in headless Chromium and reads back every pixel as rows from the top, each pixel red, green, blue and alpha. -/
def rendersBytes (dir : System.FilePath) (w h : Nat) (frame : ByteArray) :
    IO (Option (Array Nat)) := do
  IO.FS.writeFile (dir / "gpu.mjs") js
  let bytes := ", ".intercalate (frame.data.toList.map (toString ·.toNat))
  let script := s!"import \{ chromium } from \"playwright\";
import \{ readFileSync } from \"node:fs\";
const browser = await chromium.launch();
const page = await browser.newPage();
await page.setContent(\"<canvas id=c width={w} height={h}></canvas>\");
const src = readFileSync(\"{dir / "gpu.mjs"}\", \"utf8\");
const px = await page.evaluate(async (\{ src, bytes }) => \{
  const gpu = await import(URL.createObjectURL(new Blob([src], \{ type: \"text/javascript\" })));
  const gl = document.getElementById(\"c\").getContext(\"webgl2\", \{ preserveDrawingBuffer: true });
  const state = gpu.newState();
  gpu.run(gl, state, new Uint8Array(bytes));
  const out = new Uint8Array({w} * {h} * 4);
  gl.readPixels(0, 0, {w}, {h}, gl.RGBA, gl.UNSIGNED_BYTE, out);
  return gl.getError() === 0 ? Array.from(out) : [];
}, \{ src, bytes: [{bytes}] });
await browser.close();
console.log(JSON.stringify(px));"
  let out ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
  IO.eprint out.stderr
  if out.exitCode != 0 then return none
  match Lean.Json.parse out.stdout with
  | .ok (.arr a) =>
    let vs := a.filterMap fun j => (j.getNat?).toOption
    -- readPixels counts rows from the bottom.
    let rows := (List.range h).reverse.flatMap fun r => (vs.toList.drop (r * w * 4)).take (w * 4)
    return if vs.size == w * h * 4 then some rows.toArray else none
  | _ => return none

/-- A frame of `list` on a `w` by `h` canvas, as `rendersBytes`. -/
def renders (dir : System.FilePath) (w h : Nat) (list : Inkproof.Scene.DisplayList) :
    IO (Option (Array Nat)) :=
  rendersBytes dir w h (frameBytes w h list ⟨255, 255, 255, 255⟩)

open Inkproof.Scene in
/-- A display list of gradient and flat commands that overlap, on a 32 by 8 target. -/
def gradientList : DisplayList :=
  #[⟨0, .gradient .x ⟨4, ⟨255, 0, 0, 255⟩⟩ [⟨33 / 2, ⟨0, 255, 0, 255⟩⟩, ⟨28, ⟨0, 0, 255, 255⟩⟩],
      .rect ⟨0, 0, 32, 8⟩⟩,
    ⟨1, .gradient .y ⟨1, ⟨255, 255, 0, 255⟩⟩ [⟨7, ⟨0, 0, 0, 255⟩⟩], .rect ⟨8, 2, 24, 7⟩⟩,
    ⟨2, .flat ⟨255, 0, 255, 255⟩, .rect ⟨0, 0, 4, 2⟩⟩]

open Inkproof.Scene in
/-- Steps along x and y on a 32 by 8 target, with a stop at a pixel centre and another between two. -/
def stepsList : DisplayList :=
  #[⟨0, .steps .x ⟨4, ⟨255, 0, 0, 255⟩⟩ [⟨25 / 2, ⟨0, 255, 0, 255⟩⟩, ⟨20, ⟨0, 0, 255, 255⟩⟩],
      .rect ⟨0, 0, 32, 8⟩⟩,
    ⟨1, .steps .y ⟨1, ⟨255, 255, 0, 255⟩⟩ [⟨3, ⟨0, 0, 0, 255⟩⟩], .rect ⟨24, 0, 32, 8⟩⟩]

open Inkproof.Scene in
/-- The colour that Scene's raster model gives a pixel: that of the last command whose rectangle holds it. -/
def expectedPixel (list : DisplayList) (col row : Nat) : Color :=
  list.toList.foldl (fun acc c =>
    match c.shape with
    | .rect b =>
      if b.x0 ≤ col ∧ (col : Rat) < b.x1 ∧ b.y0 ≤ row ∧ (row : Rat) < b.y1
      then c.color.at ⟨col, row⟩ else acc
    | _ => acc) ⟨255, 255, 255, 255⟩

/-- Whether every pixel of the render is within `tol` of the colour Scene's raster model gives it. -/
def matchesModel (list : Inkproof.Scene.DisplayList) (w tol : Nat) (px : Array Nat) : Bool :=
  (List.range px.size).all fun i =>
    let p := i / 4
    let want := expectedPixel list (p % w) (p / w)
    let want := [want.r, want.g, want.b, want.a][i % 4]!.toNat
    let got := px[i]!
    (if got ≥ want then got - want else want - got) ≤ tol

open Inkproof.Scene in
/-- Two translucent rectangles that overlap in the middle columns of a 12 by 2 target. -/
def translucentList : DisplayList :=
  #[⟨0, .flat ⟨255, 0, 0, 128⟩, .rect ⟨0, 0, 8, 2⟩⟩, ⟨1, .flat ⟨0, 0, 255, 128⟩, .rect ⟨4, 0, 12, 2⟩⟩]

/-- Source-over of straight colour `c` with alpha `a` (0 to 255) on the opaque channel value `d`. -/
def overChannel (c a d : Nat) : Nat := (c * a + d * (255 - a) + 127) / 255

/-- Whether each pixel of the render is the translucent rectangles source-over white, to 2 in 255. -/
def mixesTranslucent (px : Array Nat) : Bool :=
  (List.range 12).all fun col =>
    let layers : List (Nat × Nat × Nat) :=
      (if col < 8 then [(255, 0, 0)] else []) ++ (if col ≥ 4 then [(0, 0, 255)] else [])
    let want := layers.foldl (fun (r, g, b) (cr, cg, cb) =>
      (overChannel cr 128 r, overChannel cg 128 g, overChannel cb 128 b)) (255, 255, 255)
    let near (x y : Nat) := (if x ≥ y then x - y else y - x) ≤ 2
    near px[col * 4]! want.1 && near px[col * 4 + 1]! want.2.1 && near px[col * 4 + 2]! want.2.2 &&
      px[col * 4 + 3]! == 255

open Inkproof.Scene in
/-- An area on a 16 by 16 target whose series runs from (0, 2) to (16, 14) across its baseline `y = 8`. -/
def crossingList : DisplayList :=
  #[⟨0, .flat ⟨255, 0, 0, 255⟩, .area 8 [.val ⟨0, 2⟩, .val ⟨16, 14⟩]⟩]

/-- Whether every pixel whose centre is more than a pixel from the line or the baseline is red exactly when it lies between them. -/
def fillsBetween (px : Array Nat) : Bool :=
  (List.range 256).all fun i =>
    let x : Rat := (i % 16 : Nat) + 1 / 2
    let y : Rat := (i / 16 : Nat) + 1 / 2
    let line : Rat := 2 + 3 / 4 * x
    let dist := if y ≥ line then y - line else line - y
    let base := if y ≥ 8 then y - 8 else 8 - y
    let inside := (line ≤ y ∧ y ≤ 8) ∨ (8 ≤ y ∧ y ≤ line)
    dist ≤ 1 || base ≤ 1 || ((px[i * 4 + 1]! == 0) == inside)

open Inkproof.Scene in
/-- Seven vertical and seven horizontal translucent strokes 2 pixels wide on a 64 by 160 target, each at a different sub-pixel offset, with data y upwards: the vertical ones run over rows 30 to 59. -/
def strokeList : DisplayList :=
  let colour : Color := ⟨0, 0, 0, 128⟩
  let verticals := (List.range 7).map fun (i : Nat) =>
    let x : Rat := 4 + 8 * i + (i : Rat) / 9
    (⟨i, .flat colour, .strip 1 [.val ⟨x, 100⟩, .val ⟨x, 130⟩]⟩ : Command)
  let horizontals := (List.range 7).map fun (i : Nat) =>
    let y : Rat := 4 + 12 * i + (i : Rat) / 7
    (⟨7 + i, .flat colour, .strip 1 [.val ⟨10, y⟩, .val ⟨40, y⟩]⟩ : Command)
  (verticals ++ horizontals).toArray

/-- Whether every vertical stroke of `strokeList` has the same ink in each row from its first to its last, and every horizontal one in each column. A stroke whose end is drawn twice is darker there when translucent. -/
def evenInk (px : Array Nat) : Bool :=
  let ink (col row : Nat) : Nat := 255 - px[(row * 64 + col) * 4]!
  let level (xs : List Nat) : Bool :=
    xs.all fun v => v ≤ xs.foldl max 0 && xs.foldl max 0 ≤ v + 3
  (List.range 7).all (fun i =>
    let x := 4 + 8 * i
    level ((List.range 30).map fun r => (List.range 6).foldl (fun a c => a + ink (x - 2 + c) (30 + r)) 0)) &&
  (List.range 7).all fun i =>
    let row := 160 - (4 + 12 * i) - 3
    level ((List.range 30).map fun c => (List.range 6).foldl (fun a r => a + ink (10 + c) (row + r)) 0)

open Inkproof.Scene in
/-- Seven vertical and seven horizontal opaque strokes of half width 3 on a 64 by 160 target, each at a different sub-pixel offset, with rows counted down from the top. -/
def opaqueList : DisplayList :=
  let colour : Color := ⟨0, 0, 0, 255⟩
  let verticals := (List.range 7).map fun (i : Nat) =>
    let x : Rat := 8 + 8 * i + (i : Rat) / 9
    (⟨i, .flat colour, .strip 3 [.val ⟨x, 20⟩, .val ⟨x, 60⟩]⟩ : Command)
  let horizontals := (List.range 7).map fun (i : Nat) =>
    let y : Rat := 80 + 11 * i + (i : Rat) / 7
    (⟨7 + i, .flat colour, .strip 3 [.val ⟨16, y⟩, .val ⟨48, y⟩]⟩ : Command)
  (verticals ++ horizontals).toArray

/-- Whether no row of a vertical stroke of `opaqueList`, nor column of a horizontal one, holds more ink than the stroke is wide (twice its half width, to 3 in 255), and the middle holds all of it. A stroke drawn wider than its half width, or with an end wider than its stem, fails. -/
def exactWidth (px : Array Nat) : Bool :=
  let ink (col row : Nat) : Nat := 255 - px[(row * 64 + col) * 4]!
  let width := 6 * 255
  (List.range 7).all (fun i =>
    let x := 8 + 8 * i
    let rows := (List.range 50).map fun r => (List.range 8).foldl (fun a c => a + ink (x - 4 + c) (15 + r)) 0
    rows.all (· ≤ width + 3) && rows.getD 25 0 + 3 ≥ width) &&
  (List.range 7).all fun i =>
    let y := 80 + 11 * i
    let cols := (List.range 40).map fun c => (List.range 8).foldl (fun a r => a + ink (11 + c) (y - 4 + r)) 0
    cols.all (· ≤ width + 3) && cols.getD 20 0 + 3 ≥ width

/-- Builds `Browser.lean` for the browser and runs it in headless Chromium, where the stack is far shallower than under node. -/
def encodesInBrowser (dir : System.FilePath) : IO Bool := do
  let out := dir / "browser"
  if ← out.pathExists then IO.FS.removeDirAll out
  let build ← IO.Process.output
    { cmd := "node_modules/.bin/lasm"
      args := #["build", "Browser.lean", "--target", "browser", "--dev", "--output", out.toString]
      env := #[("LASM_EDITOR", some "0")] }
  if build.exitCode != 0 then
    IO.eprint build.stderr
    return false
  let script := s!"import \{ chromium } from \"playwright\";
import \{ createServer } from \"node:http\";
import \{ readFileSync } from \"node:fs\";
import \{ extname, join } from \"node:path\";
const types = \{ \".js\": \"text/javascript\", \".html\": \"text/html\", \".wasm\": \"application/wasm\" };
const server = createServer((q, r) => \{
  try \{
    const p = join(\"{out}\", q.url === \"/\" ? \"index.html\" : q.url.split(\"?\")[0]);
    r.setHeader(\"content-type\", types[extname(p)] ?? \"application/octet-stream\");
    r.end(readFileSync(p));
  } catch \{ r.statusCode = 404; r.end(); }
}).listen(0);
const browser = await chromium.launch();
const page = await browser.newPage();
const lines = [];
page.on(\"console\", m => lines.push(m.text()));
page.on(\"pageerror\", e => lines.push(e.message));
await page.goto(`http://localhost:$\{server.address().port}/`);
const deadline = Date.now() + 60000;
while (Date.now() < deadline && !lines.some(l => l.startsWith(\"frame bytes\") || l.includes(\"stopped\")))
  await page.waitForTimeout(200);
await browser.close();
server.close();
console.log(lines.find(l => l.startsWith(\"frame bytes\")) ?? lines.join(\"; \"));"
  let r ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
  IO.eprint r.stderr
  return r.exitCode == 0 && r.stdout.trimAscii.toString.startsWith "frame bytes"

def main : IO UInt32 := do
  let dir : System.FilePath := "/tmp/inkproof-gpu-test"
  IO.FS.createDirAll dir
  if !(← jsDecodes dir sample) then return ← fail "generated JavaScript decoder"
  if !(← drawsTriangle dir triangle "{\"px\":[255,0,0,255],\"err\":0,\"released\":true}") then
    return ← fail "triangle drawn in headless Chromium"
  if !(← drawsTriangle dir triangle6 "{\"px\":[255,0,0,255],\"err\":0,\"released\":true}") then
    return ← fail "triangle of positions, directions and corners drawn in headless Chromium"
  if !(← drawsTriangle dir (scissored triangle [0, 0, 4, 4]) "{\"px\":[0,0,0,255],\"err\":0,\"released\":true}") then
    return ← fail "scissor excludes the centre"
  if !(← drawsTriangle dir (scissored triangle [4, 4, 8, 8]) "{\"px\":[255,0,0,255],\"err\":0,\"released\":true}") then
    return ← fail "scissor keeps the centre"
  match ← renders dir 32 8 gradientList with
  | some px =>
    if !matchesModel gradientList 32 1 px then
      return ← fail "gradient fills match the raster model to 1 in 255 in headless Chromium"
  | none => return ← fail "gradient frame rendered in headless Chromium"
  match ← renders dir 32 8 stepsList with
  | some px =>
    if !matchesModel stepsList 32 1 px then
      return ← fail "steps fills match the raster model to 1 in 255 in headless Chromium"
  | none => return ← fail "steps frame rendered in headless Chromium"
  match ← renders dir 12 2 translucentList with
  | some px =>
    if !mixesTranslucent px then
      return ← fail "overlapping translucent fills mix by source-over in headless Chromium"
  | none => return ← fail "translucent frame rendered in headless Chromium"
  match ← renders dir 16 16 crossingList with
  | some px =>
    if !fillsBetween px then
      return ← fail "an area that crosses its baseline fills only between the line and the baseline"
  | none => return ← fail "crossing area frame rendered in headless Chromium"
  let strokeView : Inkproof.Gpu.View := ⟨0, 64, 0, 160⟩
  match ← rendersBytes dir 64 160
      (viewFrameBytes 64 160 strokeView ⟨0, 0, 64, 160⟩ strokeList ⟨255, 255, 255, 255⟩) with
  | some px =>
    if !evenInk px then
      return ← fail "a translucent stroke has the same ink along its length, ends included"
  | none => return ← fail "translucent strokes rendered in headless Chromium"
  match ← rendersBytes dir 64 160 (strokeFrameBytes 64 160 opaqueList ⟨255, 255, 255, 255⟩) with
  | some px =>
    if !exactWidth px then
      return ← fail "an opaque stroke is as wide as twice its half width, ends included"
  | none => return ← fail "opaque strokes rendered in headless Chromium"
  if !(← encodesInBrowser dir) then
    return ← fail "a frame of 40000 commands under Lasm in headless Chromium"
  for (name, text) in [("gpu.js", js), ("vertex.glsl", vertexShader.glsl),
      ("fragment.glsl", fragmentShader.glsl)] do
    if (← IO.FS.readFile s!"../generated/{name}") != text then
      return ← fail s!"generated/{name} is stale; run lake exe gen generated"
  IO.println "ok"
  return 0
