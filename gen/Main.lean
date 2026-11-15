/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu

open Inkproof.Gpu

def generated : List (String × String) := [
  ("gpu.js", js),
  ("vertex.glsl", vertexShader.glsl),
  ("fragment.glsl", fragmentShader.glsl)
]

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] =>
    for (name, text) in generated do
      IO.FS.writeFile (System.FilePath.mk dir / name) text
    return 0
  | _ =>
    IO.eprintln "usage: gen <output directory>"
    return 1
