/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu
import Inkproof.Scene.DisplayList
import InkproofTools.Test.Platform

open InkproofTools.Test Inkproof.Gpu

def sample : List Cmd := [
  ⟨0, [.u32 7]⟩,
  ⟨1, [.u32 7, .words [1, 2, 0xFFFFFFFF]]⟩,
  ⟨4, [.u32 0, .words []]⟩,
  ⟨8, [.words [1, 2, 3, 4]]⟩,
  ⟨5, [.u32 7, .u32 3, .u32 2]⟩,
  ⟨6, [.u32 0x11223344]⟩
]

open Shader in
def badShader : Shader :=
  { vertexShader with decls := [⟨"p", 4, .var "a_position"⟩] }

open Shader in
def ragged : Expr := .bin .add (.var "a_position") (.vec4 (.lit 0) (.lit 0) (.lit 0) (.lit 0))

open Inkproof.Scene in
def cmd (layer : Nat) (x : Int) : Command :=
  ⟨layer, .flat ⟨0, 0, 0, 255⟩, .rect ⟨x, 0, x + 1, 1⟩⟩

def tess (c : Inkproof.Scene.Command) : List UInt32 := [UInt32.ofNat c.layer, 0, 1, 1, 2, 2]

open Inkproof.Scene in
def inTri (t : Tri) (p : Pt) : Bool :=
  let d (a b : Pt) : Rat := (p.x - b.x) * (a.y - b.y) - (a.x - b.x) * (p.y - b.y)
  let (d1, d2, d3) := (d t.a t.b, d t.b t.c, d t.c t.a)
  !((d1 < 0 || d2 < 0 || d3 < 0) && (d1 > 0 || d2 > 0 || d3 > 0))

open Inkproof.Scene in
def discPoints (c : Pt) (r : Int) : List Pt :=
  let ks : List Int := (List.range (2 * r.toNat + 1)).map fun (i : Nat) => (i : Int) - r
  (ks.flatMap fun i => ks.map fun j => (i, j)).filterMap fun (i, j) =>
    if i * i + j * j ≤ r * r then some ⟨c.x + i, c.y + j⟩ else none

def discRadii : List Int := [1, 2, 3, 5, 10, 30, 60]

open Inkproof.Scene in
def shapes : List Shape :=
  [.rect ⟨1, 2, 5, 9⟩, .marker .circle ⟨3, 4⟩ 2, .marker .square ⟨3, 4⟩ 2,
   .strip 1 [.val ⟨0, 0⟩, .val ⟨4, 1⟩, .gap, .val ⟨6, 6⟩],
   .area 0 [.val ⟨0, 3⟩, .val ⟨2, 5⟩], .envelope [.val ⟨0, 1, 3⟩, .val ⟨2, 2, 6⟩],
   .text ⟨0, 0, 3, 3⟩ "a", .clipped ⟨0, 0, 1, 1⟩ (.rect ⟨0, 0, 4, 4⟩)]

def tiles (u : UInt32) : List Tile :=
  [⟨#[cmd 2 0, cmd 0 1], [u], [0], [], 2, fun _ => [0], fun _ => [], ⟨0, 0⟩, none⟩,
   ⟨#[cmd 1 2], [u + 1], [0], [], 2, fun _ => [0], fun _ => [], ⟨0, 0⟩, none⟩]

def isUpload : Op → Bool
  | .create _ | .upload _ _ => true
  | _ => false

def drawHandles (ops : List Op) : List Nat :=
  ops.filterMap fun | .draw h _ _ => some h | _ => none

def uploadsCmd (cmds : List Cmd) : Bool := cmds.any fun c => c.op == 0 || c.op == 1

open Inkproof.Scene in
def zoomList : DisplayList :=
  #[⟨0, .flat ⟨0, 0, 0, 255⟩, .rect ⟨10, 20, 30, 40⟩⟩, ⟨1, .flat ⟨0, 0, 0, 255⟩, .marker .circle ⟨12, 33⟩ 2⟩]

def zoomPlot : Inkproof.Scene.Rect := ⟨50, 20, 450, 320⟩

def zoomViews : List View := [⟨5, 35, 15, 45⟩, ⟨8, 20, 18, 38⟩, ⟨-1000, 1000, -1000, 1000⟩]

def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

open Inkproof.Scene in
/-- A strip over x 1 to 7 and y 40 to 80 of half width half a pixel, and a marker of radius 3 pixels of each kind. -/
def strokeList : DisplayList :=
  #[⟨0, .flat ⟨0, 0, 0, 255⟩, .strip (1 / 2) [.val ⟨1, 40⟩, .val ⟨3, 80⟩, .val ⟨5, 50⟩, .gap, .val ⟨7, 60⟩]⟩,
    ⟨1, .flat ⟨0, 0, 0, 255⟩, .marker .circle ⟨4, 55⟩ 3⟩,
    ⟨2, .flat ⟨0, 0, 0, 255⟩, .marker .square ⟨2, 70⟩ 3⟩]

def strokePlot : Inkproof.Scene.Rect := ⟨40, 30, 440, 330⟩

def strokeViews : List View := [⟨0, 8, 30, 90⟩, ⟨1, 3, 40, 80⟩, ⟨-20, 30, 0, 200⟩]

def toFloat32s (ws : List UInt32) : List Float32 := ws.map Float32.ofBits

def chunks6 : List UInt32 → List (List UInt32)
  | a :: b :: c :: d :: e :: f :: rest => [a, b, c, d, e, f] :: chunks6 rest
  | _ => []

/-- Where the vertex shader puts each vertex of `words`, in pixels from the top left of a `w` by `h` target. -/
def shaderPixels (w h : Nat) (st : State) (words : List UInt32) : List (Float × Float) :=
  (chunks6 words).filterMap fun v =>
    let env : String → Option (List Float32) := fun n =>
      if n == "a_position" then some (toFloat32s (v.take 2))
      else if n == "a_dir" then some (toFloat32s ((v.drop 2).take 2))
      else if n == "a_corner" then some (toFloat32s (v.drop 4))
      else if n == "u_slope" then some (toFloat32s st.slope)
      else if n == "u_offset" then some (toFloat32s st.offset)
      else if n == "u_size" then some (toFloat32s st.size)
      else if n == "u_view" then some (toFloat32s st.view)
      else none
    match vertexShader.run env with
    | some [(_, [x, y, _, _]), _] =>
      some ((x.toFloat + 1) / 2 * w.toFloat, (1 - y.toFloat) / 2 * h.toFloat)
    | _ => none

/-- The corners of the rectangle of half width `hw` about the segment from `a` to `b` in pixels, computed exactly. -/
def segCorners (hw : Float) (a b : Float × Float) : List (Float × Float) :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let len := Float.sqrt (dx * dx + dy * dy)
  let (tx, ty) := if len == 0 then (1.0, 0.0) else (dx / len, dy / len)
  [(a.1 - hw * ty, a.2 + hw * tx), (a.1 + hw * ty, a.2 - hw * tx),
   (b.1 - hw * ty, b.2 + hw * tx), (b.1 + hw * ty, b.2 - hw * tx)]

/-- The unit direction from `a` to `b`, along x when they coincide. -/
def unitDir (a b : Float × Float) : Float × Float :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let len := Float.sqrt (dx * dx + dy * dy)
  if len == 0 then (1.0, 0.0) else (dx / len, dy / len)

/-- The corners of the octagon of circumradius `hw / cos (π / 8)` about `c`, with edges parallel and perpendicular to the unit direction `t`, and diagonals. -/
def octagonCorners (hw : Float) (c : Float × Float) (t : Float × Float) : List (Float × Float) :=
  let k := 0.41421356
  let corner := fun (u v : Float) => (c.1 + hw * (u * t.1 - v * t.2), c.2 + hw * (u * t.2 + v * t.1))
  [corner 1 (-k), corner 1 k, corner k 1, corner (-k) 1, corner (-1) k, corner (-1) (-k), corner (-k) (-1), corner k (-1)]

/-- The corners of the half of that octagon ahead of `c` along `t`, whose straight edge lies on the corners of the rectangle at `c`. -/
def capCorners (hw : Float) (c : Float × Float) (t : Float × Float) : List (Float × Float) :=
  let k := 0.41421356
  let corner := fun (u v : Float) => (c.1 + hw * (u * t.1 - v * t.2), c.2 + hw * (u * t.2 + v * t.1))
  [corner 1 (-k), corner 1 k, corner k 1, corner k (-1), corner 0 1, corner 0 (-1)]

open Inkproof.Scene in
/-- The corners of a strip's segments, of a cap beyond each end of a run, and of an octagon about each value between two, each turned to the direction of the segment beside it. -/
def stripCorners (hw : Float) (prev : Option (Float × Float)) : List (Item (Float × Float)) → List (Float × Float)
  | [] => []
  | .gap :: rest => stripCorners hw none rest
  | .val a :: rest =>
    match rest with
    | .val b :: _ =>
      let t := unitDir a b
      (match prev with
        | none => capCorners hw a (-t.1, -t.2)
        | some _ => octagonCorners hw a t) ++ segCorners hw a b ++ stripCorners hw (some t) rest
    | _ =>
      (match prev with
        | none => octagonCorners hw a (1, 0)
        | some t => capCorners hw a t) ++ stripCorners hw none rest

open Inkproof.Scene in
/-- The corners of the shape in pixels under the view: those of a strip are exact, and the others are the corners of the triangles. -/
def pixelCorners (v : View) (plot : Rect) : Shape → List (Float × Float)
  | .strip hw items => stripCorners (ratToFloat hw) none (items.map fun
      | .val p => .val (ratToFloat ((viewX v plot).apply p.x), ratToFloat ((viewY v plot).apply p.y))
      | .gap => .gap)
  | .marker k c r =>
    (Inkproof.Gpu.triangles (.marker k ⟨(viewX v plot).apply c.x, (viewY v plot).apply c.y⟩ r)).flatMap fun t =>
      [t.a, t.b, t.c].map fun p => (ratToFloat p.x, ratToFloat p.y)
  | _ => []

/-- Whether every point is within half a pixel of one of the others. -/
def within (ps qs : List (Float × Float)) : Bool :=
  ps.all fun p => qs.any fun q => (p.1 - q.1).abs ≤ 0.5 && (p.2 - q.2).abs ≤ 0.5

open Inkproof.Scene in
/-- The vertices of the shader's triangles agree to half a pixel with the corners of the shapes in pixels. A strip is exact: Scene's triangles for a strip have square caps and are wider. -/
def strokeAgrees (w h : Nat) (v : View) : Bool :=
  let tile := viewTile w h v strokePlot strokeList
  tile.list.paintOrder.all fun c =>
    let got := shaderPixels w h (tile.stateOf c) (tessellateStroke ⟨0, 0⟩ c)
    let want := pixelCorners v strokePlot (match c.shape with | .clipped _ s => s | s => s)
    !got.isEmpty && within got want && within want got

/-- The distance from `p` to the segment from `a` to `b`. -/
def segDist (p a b : Float × Float) : Float :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let l2 := dx * dx + dy * dy
  let t := if l2 == 0 then 0.0 else max 0.0 (min 1.0 (((p.1 - a.1) * dx + (p.2 - a.2) * dy) / l2))
  let ex := p.1 - (a.1 + t * dx)
  let ey := p.2 - (a.2 + t * dy)
  Float.sqrt (ex * ex + ey * ey)

open Inkproof.Scene in
/-- Every vertex of a strip's triangles is within `hw / cos (π / 8)` of the strip's polyline, so the strip is no wider than the thickened polyline by more than about 8% of its half width. -/
def stripWithinJoins (w h : Nat) (v : View) (hw : Rat) (items : List (Item Pt)) : Bool :=
  let cmd : Command := ⟨0, .flat ⟨0, 0, 0, 255⟩, .strip hw items⟩
  let tile := viewTile w h v strokePlot #[cmd]
  let px : List (Item (Float × Float)) := items.map fun
    | .val p => .val (ratToFloat ((viewX v strokePlot).apply p.x), ratToFloat ((viewY v strokePlot).apply p.y))
    | .gap => .gap
  let pts := px.filterMap fun | .val p => some p | .gap => none
  let segs := (Item.runs px).flatMap fun r => r.zip (r.drop 1)
  let bound := ratToFloat hw * 1.0825 + 0.01
  let got := shaderPixels w h (tile.stateOf cmd) (tessellateStroke ⟨0, 0⟩ cmd)
  !got.isEmpty && got.all fun p =>
    (pts.any fun a => segDist p a a ≤ bound) || segs.any fun (a, b) => segDist p a b ≤ bound

/-- The values in `xs` with duplicates removed. -/
def distinctFloats (xs : List Float) : List Float :=
  xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []

open Inkproof.Scene in
/-- A two point stroke has its vertices on five lines across it, its axis, its two edges and the two sides of the octagon between them, at both ends, so no end is wider than the stroke. The test is exact: an end that differs by a rounding error shows as a step of a pixel where an edge falls on a pixel centre. -/
def strokeEndsFlush (w h : Nat) (v : View) (vertical : Bool) (offset : Rat) : Bool :=
  let items : List (Item Pt) :=
    if vertical then [.val ⟨2 + offset, 40⟩, .val ⟨2 + offset, 90 + offset⟩] else [.val ⟨2, 40 + offset⟩, .val ⟨6 + offset, 40 + offset⟩]
  let cmd : Command := ⟨0, .flat ⟨0, 0, 0, 255⟩, .strip 1 items⟩
  let tile := viewTile w h v strokePlot #[cmd]
  let got := shaderPixels w h (tile.stateOf cmd) (tessellateStroke ⟨0, 0⟩ cmd)
  !got.isEmpty &&
    (distinctFloats (got.map fun p => if vertical then p.1 else p.2)).length == 5

def main (args : List String) : IO UInt32 :=
  runTests [
    platformTest (args.contains "--expect-wasm"),
    ⟨"encoded sample decodes to itself", check (decode (encode sample) == some sample) "round trip"⟩,
    ⟨"truncated buffer is rejected", check (decode ((encode sample).take 9) == none) "accepted"⟩,
    ⟨"shader declaring the wrong dimension is not well typed",
      check (!decide badShader.WellTyped) "accepted"⟩,
    ⟨"vectors of different dimension do not combine",
      check (ragged.eval (fun _ => some [1, 2]) == none) "evaluated"⟩,
    ⟨"first frame uploads and draws each tile in paint order",
      let (_, ops) := compile tess {} (tiles 0)
      check (ops.any isUpload && drawHandles ops == [0, 1, 2]) "wrong order or no uploads"⟩,
    ⟨"pan frame only sets uniforms and draws",
      let (c, _) := compile tess {} (tiles 0)
      let (_, ops) := compile tess c (tiles 5)
      check (!ops.any isUpload && drawHandles ops == [0, 1, 2]) "uploaded again"⟩,
    ⟨"a strip does not protrude past round joins and caps by more than a tenth of its half width",
      check (strokeViews.all fun v => stripWithinJoins 500 400 v 1 [.val ⟨1, 40⟩, .val ⟨3, 80⟩, .val ⟨5, 40⟩, .val ⟨5, 40⟩, .gap, .val ⟨7, 60⟩])
        "protrudes"⟩,
    ⟨"vertical and horizontal strokes have ends as wide as the stroke at any sub-pixel offset",
      let offsets : List Rat := (List.range 120).map fun (i : Nat) => (i : Rat) / 37
      check (strokeViews.all fun v => offsets.all fun o =>
        strokeEndsFlush 500 400 v true o && strokeEndsFlush 500 400 v false o) "an end is wider than the stroke"⟩,
    ⟨"changed tile content is uploaded and the stale buffers deleted",
      let (c, _) := compile tess {} (tiles 0)
      let (_, ops) := compile tess c [⟨#[cmd 3 9], [0], [0], [], 2, fun _ => [0], fun _ => [], ⟨0, 0⟩, none⟩]
      check (ops.any isUpload && ops.any (fun | .delete _ => true | _ => false)) "no re-upload"⟩,
    ⟨"compiled frame survives the wire",
      let (_, cmds) := compileCmds tess {} (tiles 0)
      check (decode (encode cmds) == some cmds) "round trip"⟩,
    ⟨"every shape tessellates to whole triangles",
      check (shapes.all fun sh =>
        (tessellate ⟨0, 0⟩ ⟨0, .flat ⟨0, 0, 0, 255⟩, sh⟩).length % 6 == 0 &&
        !(tessellate ⟨0, 0⟩ ⟨0, .flat ⟨0, 0, 0, 255⟩, sh⟩).isEmpty) "ragged or empty"⟩,
    ⟨"moving the origin to the shape gives the shape at the origin",
      check (tessellate ⟨4, 8⟩ ⟨0, .flat ⟨0, 0, 0, 255⟩, .rect ⟨5, 9, 7, 10⟩⟩ ==
        tessellate ⟨0, 0⟩ ⟨0, .flat ⟨0, 0, 0, 255⟩, .rect ⟨1, 1, 3, 2⟩⟩) "differs"⟩,
    ⟨"a circle's polygon contains the disc",
      check (discRadii.all fun r =>
        (discPoints ⟨3, -2⟩ r).all fun p =>
          (Inkproof.Gpu.triangles (.marker .circle ⟨3, -2⟩ r)).any (inTri · p)) "point outside"⟩,
    ⟨"a circle's edges are never inside the circle and its corners at most the tolerance outside it",
      check (discRadii.all fun r =>
        let c : Inkproof.Scene.Pt := ⟨3, -2⟩
        (Inkproof.Gpu.triangles (.marker .circle c r)).all fun t =>
          let sq (p : Inkproof.Scene.Pt) : Rat := (p.x - c.x) ^ 2 + (p.y - c.y) ^ 2
          let cross := (t.b.x - c.x) * (t.c.y - c.y) - (t.b.y - c.y) * (t.c.x - c.x)
          let len2 := (t.c.x - t.b.x) ^ 2 + (t.c.y - t.b.y) ^ 2
          cross ^ 2 ≥ r ^ 2 * len2 && sq t.b ≤ (r + Inkproof.Gpu.discTolerance) ^ 2) "edge or corner off"⟩,
    ⟨"a circle drawn by the vertex shader is the same polygon, scaled by its radius",
      check (discRadii.all fun r =>
        let vs := Inkproof.Gpu.strokeVertices (.marker .circle ⟨3, -2⟩ r)
        vs.length == 3 * (Inkproof.Gpu.triangles (.marker .circle ⟨3, -2⟩ r)).length &&
        (Inkproof.Gpu.triangles (.marker .circle ⟨3, -2⟩ r)).flatMap (fun t => [t.a, t.b, t.c]) ==
          vs.map fun v => (⟨v.pos.x + r * v.kx, v.pos.y + r * v.ky⟩ : Inkproof.Scene.Pt)) "differs"⟩,
    ⟨"a small circle has no more triangles than an octagon",
      check ([1, 2, 3].all fun (r : Rat) =>
        (Inkproof.Gpu.triangles (.marker .circle ⟨0, 0⟩ r)).length ≤ 8) "more than eight"⟩,
    ⟨"each draw is set up with its colour and scissor",
      let t : Tile := ⟨#[⟨0, .flat ⟨255, 0, 0, 255⟩, .clipped ⟨0, 0, 1, 1⟩ (.rect ⟨0, 0, 4, 4⟩)⟩,
        ⟨1, .flat ⟨0, 0, 0, 0⟩, .rect ⟨0, 0, 1, 1⟩⟩], [0], [0], [], 2, fun _ => [0], fun _ => [7, 7, 7, 7], ⟨0, 0⟩, none⟩
      let (_, ops) := compile tess {} [t]
      check (ops.filter (fun | .scissor _ => true | _ => false) ==
          [.scissor [7, 7, 7, 7], .scissor []] &&
        ops.filter (fun | .uniform 4 _ => true | _ => false) ==
          [.uniform 4 [0x3F800000, 0, 0, 0x3F800000], .uniform 4 [0, 0, 0, 0]]) "wrong state"⟩,
    ⟨"a gradient command is drawn with its stops as uniforms, relative to the tile origin",
      let g : Inkproof.Scene.Command := ⟨0, .gradient .y ⟨10, ⟨255, 0, 0, 255⟩⟩
        [⟨14, ⟨0, 0, 255, 255⟩⟩], .rect ⟨0, 0, 1, 1⟩⟩
      let t : Tile := ⟨#[g], [0], [0], [], 2, fun _ => [0], fun _ => [7, 7, 7, 7], ⟨3, 4⟩, none⟩
      let (_, ops) := compile tess {} [t]
      let one : UInt32 := 0x3F800000
      check (ops.contains (.scissor []) && ops.contains (.uniform 5 [0, one]) &&
        ops.contains (.uniform 6 [(ratToFloat32 6).toBits, 0, 0, 0]) &&
        ops.contains (.uniform 7 [(ratToFloat32 (1 / 4)).toBits, 0, 0, 0]) &&
        ops.contains (.uniform 8 [(ratToFloat32 (-1)).toBits, 0, one, 0])) "wrong state"⟩,
    ⟨"gradient uniforms are set again only when they change, and a flat colour after a gradient resets them",
      let g : Inkproof.Scene.Command := ⟨1, .gradient .x ⟨0, ⟨255, 0, 0, 255⟩⟩ [⟨4, ⟨0, 0, 255, 255⟩⟩], .rect ⟨0, 0, 1, 1⟩⟩
      let t : Tile := ⟨#[cmd 0 0, g, ⟨2, g.color, .rect ⟨1, 1, 2, 2⟩⟩, ⟨3, .flat ⟨0, 0, 0, 255⟩, .rect ⟨2, 2, 3, 3⟩⟩],
        [0], [0], [], 2, fun _ => [0], fun _ => [], ⟨0, 0⟩, none⟩
      let (_, ops) := compile tess {} [t]
      let d0 := ops.filterMap fun | .uniform 8 ws => some ws | _ => none
      check (d0.length == 3 && d0.getLast? == some [0, 0, 0, 0]) "wrong uniforms"⟩,
    ⟨"a gradient with descending stops is drawn with an empty scissor",
      let g : Inkproof.Scene.Command := ⟨0, .gradient .x ⟨5, ⟨255, 0, 0, 255⟩⟩
        [⟨1, ⟨0, 0, 255, 255⟩⟩], .rect ⟨0, 0, 1, 1⟩⟩
      let t : Tile := ⟨#[g], [0], [0], [], 2, fun _ => [0], fun _ => [7, 7, 7, 7], ⟨0, 0⟩, none⟩
      let (_, ops) := compile tess {} [t]
      check (ops.contains (.scissor [0, 0, 0, 0]) && !ops.contains (.scissor [7, 7, 7, 7])) "drawn"⟩,
    ⟨"a gradient with too many stops is drawn with an empty scissor",
      let stops : List Inkproof.Scene.Stop := (List.range 5).map fun (i : Nat) => ⟨(i : Rat) + 1, ⟨0, 0, 0, 255⟩⟩
      let g : Inkproof.Scene.Command := ⟨0, .gradient .x ⟨0, ⟨255, 0, 0, 255⟩⟩ stops, .rect ⟨0, 0, 1, 1⟩⟩
      let t : Tile := ⟨#[g], [0], [0], [], 2, fun _ => [0], fun _ => [7, 7, 7, 7], ⟨0, 0⟩, none⟩
      let (_, ops) := compile tess {} [t]
      check (ops.contains (.scissor [0, 0, 0, 0]) && !ops.contains (.scissor [7, 7, 7, 7])) "drawn"⟩,
    ⟨"a frame of 40000 commands encodes",
      let list : Inkproof.Scene.DisplayList := (Array.range 40000).map fun (i : Nat) =>
        ⟨0, .flat ⟨0, 0, 0, 255⟩, .marker .circle ⟨((i : Nat) : Int), 0⟩ 2⟩
      let bytes := frameBytes 1920 600 list ⟨255, 255, 255, 255⟩
      check (bytes.size > 0 && (bytes.data.toList.take 4 == le32 (4 + 9 * 40000 + 7))) "wrong frame"⟩,
    ⟨"zooming a frame uploads nothing",
      let (c, _) := viewFrame (tessellate ⟨0, 0⟩) {} true 500 400 (zoomViews.getD 0 ⟨0, 1, 0, 1⟩) zoomPlot zoomList ⟨255, 255, 255, 255⟩
      check (zoomViews.all fun v =>
        !uploadsCmd (viewFrame (tessellate ⟨0, 0⟩) c false 500 400 v zoomPlot zoomList ⟨255, 255, 255, 255⟩).2) "uploaded"⟩,
    ⟨"a zoomed frame places vertices within half a pixel of the pixel-coordinate frame",
      check (zoomViews.all fun v =>
        let ops := (compile (tessellate ⟨0, 0⟩) {} [viewTile 500 400 v zoomPlot zoomList]).2
        let ux := ops.filterMap fun | .uniform 0 ws => some ws | _ => none
        let uo := ops.filterMap fun | .uniform 1 ws => some ws | _ => none
        (zoomList.toList.zip (ux.zip uo)).all fun (c, ws, wo) =>
          match ws, wo with
          | [sx, sy], [ox, oy] =>
            (Inkproof.Gpu.triangles c.shape).all fun t => [t.a, t.b, t.c].all fun p =>
              let fx := Float32.ofBits (sx) ; let fy := Float32.ofBits sy
              let cx := (ratToFloat32 p.x) * fx + Float32.ofBits ox
              let cy := (ratToFloat32 p.y) * fy + Float32.ofBits oy
              let px := (cx.toFloat + 1) / 2 * 500
              let py := (1 - cy.toFloat) / 2 * 400
              (px - ratToFloat ((viewX v zoomPlot).apply p.x)).abs ≤ 0.5 &&
                (py - ratToFloat ((viewY v zoomPlot).apply p.y)).abs ≤ 0.5
          | _, _ => false) "off by more than half a pixel"⟩,
    ⟨"strokes keep their size in pixels under views with different scales",
      check (strokeViews.all (strokeAgrees 500 400)) "off by more than half a pixel"⟩,
    ⟨"zooming strokes uploads nothing",
      let ts := Inkproof.Gpu.tessellateStroke ⟨0, 0⟩
      let (c, _) := viewFrame ts {} true 500 400 (strokeViews.getD 0 ⟨0, 1, 0, 1⟩) strokePlot strokeList ⟨255, 255, 255, 255⟩
      check (strokeViews.all fun v =>
        !uploadsCmd (viewFrame ts c false 500 400 v strokePlot strokeList ⟨255, 255, 255, 255⟩).2) "uploaded"⟩,
    ⟨"zooming a frame with an overlay uploads nothing new for the data",
      let ts := Inkproof.Gpu.tessellateStroke ⟨0, 0⟩
      let white : Inkproof.Scene.Color := ⟨255, 255, 255, 255⟩
      let axes : Inkproof.Scene.DisplayList :=
        #[⟨0, .flat ⟨0, 0, 0, 255⟩, .strip 1 [.val ⟨40, 330⟩, .val ⟨440, 330⟩]⟩]
      let (c, _) := viewOverlayFrame ts {} true 500 400 (strokeViews.getD 0 ⟨0, 1, 0, 1⟩) strokePlot strokeList axes white
      check (strokeViews.all fun v =>
        !uploadsCmd (viewOverlayFrame ts c false 500 400 v strokePlot strokeList axes white).2) "uploaded"⟩,
    ⟨"hiding and showing a held layer uploads nothing and draws what its frame did",
      let ts := Inkproof.Gpu.tessellateStroke ⟨0, 0⟩
      let white : Inkproof.Scene.Color := ⟨255, 255, 255, 255⟩
      let v : View := strokeViews.getD 0 ⟨0, 1, 0, 1⟩
      let ls := [Layer.stroke strokeList, Layer.stroke #[⟨0, .flat ⟨0, 0, 255, 255⟩, .marker .circle ⟨0.5, 0.5⟩ 3⟩]]
      let frame (c : Cache) (shown : List Layer) :=
        viewLayersFrame ts c false 500 400 v strokePlot shown ls #[] white
      let (c1, all) := frame {} ls
      let (c2, hidden) := frame c1 (ls.take 1)
      let (_, again) := frame c2 ls
      check (uploadsCmd all && !uploadsCmd hidden && !uploadsCmd again && hidden.length < again.length
        && again == (frame c1 ls).2) "uploaded or changed"⟩,
    ⟨"layers draw as the concatenated display list does",
      let ts := Inkproof.Gpu.tessellateStroke ⟨0, 0⟩
      let white : Inkproof.Scene.Color := ⟨255, 255, 255, 255⟩
      let v : View := strokeViews.getD 0 ⟨0, 1, 0, 1⟩
      let a : Inkproof.Scene.DisplayList := strokeList.map fun c => { c with layer := 0 }
      let b : Inkproof.Scene.DisplayList := #[⟨1, .flat ⟨0, 0, 255, 255⟩, .marker .circle ⟨0.5, 0.5⟩ 3⟩]
      let layered := (viewLayersFrame ts {} false 500 400 v strokePlot [Layer.stroke a, Layer.stroke b] [] #[] white).2
      let whole := (viewOverlayFrame ts {} false 500 400 v strokePlot (a ++ b) #[] white).2
      check (layered == whole) "different commands"⟩,
    ⟨"retained layers draw what the commands of their frame draw, and replay them",
      let ts := Inkproof.Gpu.tessellateStroke ⟨0, 0⟩
      let white : Inkproof.Scene.Color := ⟨255, 255, 255, 255⟩
      let v : View := strokeViews.getD 0 ⟨0, 1, 0, 1⟩
      let ls := [Layer.stroke strokeList, Layer.stroke #[⟨0, .flat ⟨0, 0, 255, 255⟩, .marker .circle ⟨0.5, 0.5⟩ 3⟩]]
      let draws (bs : ByteArray) : Option (List Cmd) :=
        (decode bs.data.toList).map (·.filter (·.op == 5))
      let frame (r : Retained) (shown : List Layer) :=
        viewLayersBytes ts r false 500 400 v strokePlot shown ls #[] white
      let (r1, b1) := frame {} ls
      let (r2, b2) := frame r1 (ls.take 1)
      let (r3, b3) := frame r2 ls
      let plain (shown : List Layer) :=
        (viewLayersFrame ts {} false 500 400 v strokePlot shown ls #[] white).2.filter (·.op == 5)
      check (draws b1 == some (plain ls) && draws b2 == some (plain (ls.take 1)) && draws b3 == some (plain ls)
        && r3.streams.length == 2 && b3.size > b2.size && b3.size < b1.size
        && (match decode b3.data.toList with | some cs => !uploadsCmd cs | none => false)) "different draws"⟩,
    ⟨"an overlay is drawn in pixels with stroke vertices",
      let ts := Inkproof.Gpu.tessellateStroke ⟨0, 0⟩
      let axes : Inkproof.Scene.DisplayList :=
        #[⟨0, .flat ⟨0, 0, 0, 255⟩, .strip 1 [.val ⟨40, 330⟩, .val ⟨440, 330⟩]⟩]
      let ops := (compile ts {} [viewTile 500 400 (strokeViews.getD 0 ⟨0, 1, 0, 1⟩) strokePlot strokeList,
        pixelStrokeTile 500 400 axes]).2
      let ux := ops.filterMap fun | .uniform 0 ws => some ws | _ => none
      let uo := ops.filterMap fun | .uniform 1 ws => some ws | _ => none
      let ur := ops.filterMap fun | .draw _ _ k => some k | _ => none
      match ux.getLast?, uo.getLast?, ur.getLast? with
      | some [sx, sy], some [ox, oy], some 6 =>
        let px := ((ratToFloat32 40) * Float32.ofBits sx + Float32.ofBits ox).toFloat
        let py := ((ratToFloat32 330) * Float32.ofBits sy + Float32.ofBits oy).toFloat
        check ((((px + 1) / 2 * 500) - 40).abs ≤ 0.5 && (((1 - py) / 2 * 400) - 330).abs ≤ 0.5) "off"
      | _, _, _ => check false "no stroke draw"⟩,
    ⟨"retained layers of tens of thousands of markers are encoded",
      let white : Inkproof.Scene.Color := ⟨255, 255, 255, 255⟩
      let layers := [0, 1, 2, 3].map fun (k : Int) => Layer.stroke <| (Array.range 10000).map fun i =>
        (⟨0, .flat ⟨0, 0, 0, 255⟩, Inkproof.Scene.Shape.marker .circle ⟨Int.ofNat i + k, 0⟩ 2⟩ : Inkproof.Scene.Command)
      let v : View := strokeViews.getD 0 ⟨0, 1, 0, 1⟩
      let (_, a) := strokeLayersBytes {} true 1920 600 layers layers white
      let (_, b) := viewLayersBytes (Inkproof.Gpu.tessellateStroke ⟨0, 0⟩) {} true 1920 600 v strokePlot layers layers #[] white
      check (a.size > 20000000 && b.size > 20000000) s!"{a.size} {b.size}"⟩,
    ⟨"unknown opcode is rejected", check (decode (encode [⟨200, []⟩]) == none) "accepted"⟩
  ]
