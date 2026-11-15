/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu
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

def main (args : List String) : IO UInt32 :=
  runTests [
    platformTest (args.contains "--expect-wasm"),
    ⟨"encoded sample decodes to itself", check (decode (encode sample) == some sample) "round trip"⟩,
    ⟨"truncated buffer is rejected", check (decode ((encode sample).take 9) == none) "accepted"⟩,
    ⟨"shader declaring the wrong dimension is not well typed",
      check (!decide badShader.WellTyped) "accepted"⟩,
    ⟨"vectors of different dimension do not combine",
      check (ragged.eval (fun _ => some [1, 2]) == none) "evaluated"⟩,
    ⟨"unknown opcode is rejected", check (decode (encode [⟨200, []⟩]) == none) "accepted"⟩
  ]
