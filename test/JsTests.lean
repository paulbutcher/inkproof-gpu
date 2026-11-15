/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu

open Inkproof.Gpu

def sample : List Cmd := [
  ⟨0, [.u32 7]⟩,
  ⟨1, [.u32 7, .words [1, 2, 0xFFFFFFFF]]⟩,
  ⟨4, [.u32 0, .words []]⟩,
  ⟨5, [.u32 7, .u32 3]⟩,
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

/-- Creates the program, uploads a triangle covering the centre, sets the uniforms and draws it. -/
def triangle : List Cmd := [
  ⟨6, [.u32 0x000000FF]⟩,
  ⟨7, [.u32 1]⟩,
  ⟨0, [.u32 2]⟩,
  ⟨1, [.u32 2, .words [minusOne, minusOne, one, minusOne, 0, one]]⟩,
  ⟨3, [.u32 1]⟩,
  ⟨4, [.u32 0, .words [one, one]]⟩,
  ⟨4, [.u32 1, .words [0, 0]]⟩,
  ⟨4, [.u32 2, .words [one, 0, 0, one]]⟩,
  ⟨5, [.u32 2, .u32 3]⟩
]

/-- Runs the generated interpreter on a WebGL2 context in headless Chromium and reads back the centre pixel. -/
def drawsTriangle (dir : System.FilePath) (cs : List Cmd) : IO Bool := do
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
  gpu.run(gl, gpu.newState(), new Uint8Array(bytes));
  const out = new Uint8Array(4);
  gl.readPixels(8, 8, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, out);
  return \{ px: Array.from(out), err: gl.getError() };
}, \{ src, bytes: [{bytes}] });
await browser.close();
console.log(JSON.stringify(px));"
  let out ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
  IO.eprint out.stderr
  return out.exitCode == 0 && out.stdout.trimAscii.toString == "{\"px\":[255,0,0,255],\"err\":0}"

def main : IO UInt32 := do
  let dir : System.FilePath := "/tmp/inkproof-gpu-test"
  IO.FS.createDirAll dir
  if !(← jsDecodes dir sample) then return ← fail "generated JavaScript decoder"
  if !(← drawsTriangle dir triangle) then return ← fail "triangle drawn in headless Chromium"
  for (name, text) in [("gpu.js", js), ("vertex.glsl", vertexShader.glsl),
      ("fragment.glsl", fragmentShader.glsl)] do
    if (← IO.FS.readFile s!"../generated/{name}") != text then
      return ← fail s!"generated/{name} is stale; run lake exe gen generated"
  IO.println "ok"
  return 0
