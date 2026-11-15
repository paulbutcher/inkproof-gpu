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

def tiles (u : UInt32) : List Tile :=
  [⟨#[cmd 2 0, cmd 0 1], [u]⟩, ⟨#[cmd 1 2], [u + 1]⟩]

def isUpload : Op → Bool
  | .create _ | .upload _ _ => true
  | _ => false

def drawLayers (ops : List Op) : List Nat :=
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
    ⟨"first frame uploads and draws in layer order",
      let (_, ops) := compile tess {} (tiles 0)
      check (ops.any isUpload && drawLayers ops == [1, 2, 0]) "wrong order or no uploads"⟩,
    ⟨"pan frame only sets uniforms and draws",
      let (c, _) := compile tess {} (tiles 0)
      let (_, ops) := compile tess c (tiles 5)
      check (!ops.any isUpload && drawLayers ops == [1, 2, 0]) "uploaded again"⟩,
    ⟨"changed tile content is uploaded and the stale buffers deleted",
      let (c, _) := compile tess {} (tiles 0)
      let (_, ops) := compile tess c [⟨#[cmd 3 9], [0]⟩]
      check (ops.any isUpload && ops.any (fun | .delete _ => true | _ => false)) "no re-upload"⟩,
    ⟨"compiled frame survives the wire",
      let (_, cmds) := compileCmds tess {} (tiles 0)
      check (decode (encode cmds) == some cmds) "round trip"⟩,
    ⟨"unknown opcode is rejected", check (decode (encode [⟨200, []⟩]) == none) "accepted"⟩
  ]
