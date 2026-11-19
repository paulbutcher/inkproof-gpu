/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu

open Inkproof.Gpu

def main : IO UInt32 := do
  let list : Inkproof.Scene.DisplayList := (Array.range 40000).map fun (i : Nat) =>
    ⟨0, ⟨0, 0, 0, 255⟩, .marker .circle ⟨((i : Nat) : Int), 0⟩ 2⟩
  let bytes := frameBytes 1920 600 list ⟨255, 255, 255, 255⟩
  IO.println s!"frame bytes {bytes.size}"
  return 0
