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
  ⟨5, [.u32 7, .u32 3]⟩,
  ⟨6, [.u32 0x11223344]⟩
]

open Shader in
def badShader : Shader :=
  { vertexShader with decls := [⟨"p", 4, .var "a_position"⟩] }

open Shader in
def ragged : Expr := .bin .add (.var "a_position") (.vec4 (.lit 0) (.lit 0) (.lit 0) (.lit 0))

open Inkproof.Scene in
def cmd (layer : Nat) (x : Int) : Command :=
  ⟨layer, ⟨0, 0, 0, 255⟩, .rect ⟨x, 0, x + 1, 1⟩⟩

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

open Inkproof.Scene in
def shapes : List Shape :=
  [.rect ⟨1, 2, 5, 9⟩, .marker .circle ⟨3, 4⟩ 2, .marker .square ⟨3, 4⟩ 2,
   .strip 1 [.val ⟨0, 0⟩, .val ⟨4, 1⟩, .gap, .val ⟨6, 6⟩],
   .area 0 [.val ⟨0, 3⟩, .val ⟨2, 5⟩], .envelope [.val ⟨0, 1, 3⟩, .val ⟨2, 2, 6⟩],
   .text ⟨0, 0, 3, 3⟩ "a", .clipped ⟨0, 0, 1, 1⟩ (.rect ⟨0, 0, 4, 4⟩)]

def tiles (u : UInt32) : List Tile :=
  [⟨#[cmd 2 0, cmd 0 1], [u], [0], fun _ => []⟩, ⟨#[cmd 1 2], [u + 1], [0], fun _ => []⟩]

def isUpload : Op → Bool
  | .create _ | .upload _ _ => true
  | _ => false

def drawHandles (ops : List Op) : List Nat :=
  ops.filterMap fun | .draw h _ => some h | _ => none

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
    ⟨"changed tile content is uploaded and the stale buffers deleted",
      let (c, _) := compile tess {} (tiles 0)
      let (_, ops) := compile tess c [⟨#[cmd 3 9], [0], [0], fun _ => []⟩]
      check (ops.any isUpload && ops.any (fun | .delete _ => true | _ => false)) "no re-upload"⟩,
    ⟨"compiled frame survives the wire",
      let (_, cmds) := compileCmds tess {} (tiles 0)
      check (decode (encode cmds) == some cmds) "round trip"⟩,
    ⟨"every shape tessellates to whole triangles",
      check (shapes.all fun sh =>
        (tessellate ⟨0, 0⟩ ⟨0, ⟨0, 0, 0, 255⟩, sh⟩).length % 6 == 0 &&
        !(tessellate ⟨0, 0⟩ ⟨0, ⟨0, 0, 0, 255⟩, sh⟩).isEmpty) "ragged or empty"⟩,
    ⟨"moving the origin to the shape gives the shape at the origin",
      check (tessellate ⟨4, 8⟩ ⟨0, ⟨0, 0, 0, 255⟩, .rect ⟨5, 9, 7, 10⟩⟩ ==
        tessellate ⟨0, 0⟩ ⟨0, ⟨0, 0, 0, 255⟩, .rect ⟨1, 1, 3, 2⟩⟩) "differs"⟩,
    ⟨"the octagon contains the circle",
      check ((discPoints ⟨3, -2⟩ 10).all fun p =>
        (Inkproof.Gpu.triangles (.marker .circle ⟨3, -2⟩ 10)).any (inTri · p)) "point outside"⟩,
    ⟨"each draw is set up with its colour and scissor",
      let t : Tile := ⟨#[⟨0, ⟨255, 0, 0, 255⟩, .clipped ⟨0, 0, 1, 1⟩ (.rect ⟨0, 0, 4, 4⟩)⟩,
        ⟨1, ⟨0, 0, 0, 0⟩, .rect ⟨0, 0, 1, 1⟩⟩], [0], [0], fun _ => [7, 7, 7, 7]⟩
      let (_, ops) := compile tess {} [t]
      check (ops.filter (fun | .scissor _ => true | _ => false) ==
          [.scissor [7, 7, 7, 7], .scissor []] &&
        ops.filter (fun | .uniform 2 _ => true | _ => false) ==
          [.uniform 2 [0x3F800000, 0, 0, 0x3F800000], .uniform 2 [0, 0, 0, 0]]) "wrong state"⟩,
    ⟨"a frame of 40000 commands encodes",
      let list : Inkproof.Scene.DisplayList := (Array.range 40000).map fun (i : Nat) =>
        ⟨0, ⟨0, 0, 0, 255⟩, .marker .circle ⟨((i : Nat) : Int), 0⟩ 2⟩
      let bytes := frameBytes 1920 600 list ⟨255, 255, 255, 255⟩
      check (bytes.size > 0 && (bytes.data.toList.take 4 == le32 (4 + 7 * 40000))) "wrong frame"⟩,
    ⟨"unknown opcode is rejected", check (decode (encode [⟨200, []⟩]) == none) "accepted"⟩
  ]
