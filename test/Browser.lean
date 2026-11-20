/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu

open Inkproof.Gpu

def frameSize (n : Nat) (shape : Nat → Inkproof.Scene.Shape) : Nat :=
  let list : Inkproof.Scene.DisplayList := (Array.range n).map fun i =>
    ⟨i % 3, .flat ⟨0, 0, 0, 255⟩, shape i⟩
  (frameBytes 1920 600 list ⟨255, 255, 255, 255⟩).size

def main : IO UInt32 := do
  let markers := frameSize 100000 fun i => .marker .circle ⟨(i : Int), 0⟩ 2
  let rects := frameSize 100000 fun i => .rect ⟨i, 0, i + 1, 1⟩
  IO.println s!"frame bytes {markers} {rects}"
  return 0
