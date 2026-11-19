/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Compile
import Inkproof.Gpu.Tessellate
import Inkproof.Scale.Affine

namespace Inkproof.Gpu

/-- The map from pixel columns of a `w` pixel wide target to clip x, before rounding to Float32. -/
def pixelX (w : Nat) : Scale.Affine Rat := ⟨2 / w, -1⟩

/-- The map from pixel rows of a `h` pixel high target, counted down from the top, to clip y, before rounding to Float32. -/
def pixelY (h : Nat) : Scale.Affine Rat := ⟨-2 / h, 1⟩

/-- The box (x, y, width, height) in device pixels from the bottom left that covers every pixel of a `w` by `h` target meeting `r`, a rectangle in pixels from the top left. -/
def pixelBox (w h : Nat) (r : Scene.Rect) : Nat × Nat × Nat × Nat :=
  let xl := max 0 r.x0.floor
  let xr := min (w : Int) r.x1.ceil
  let yt := max 0 r.y0.floor
  let yb := min (h : Int) r.y1.ceil
  (xl.toNat, (h - yb).toNat, (xr - xl).toNat, (yb - yt).toNat)

/-- The scissor words for a rectangle in pixels from the top left of a `w` by `h` target. -/
def pixelScissor (w h : Nat) (r : Scene.Rect) : List UInt32 :=
  let b := pixelBox w h r
  [b.1.toUInt32, b.2.1.toUInt32, b.2.2.1.toUInt32, b.2.2.2.toUInt32]

/-- A tile of a display list in device pixels from the top left of a `w` by `h` target. Its vertices are relative to the origin of the grid, and its scissor flips y. -/
def pixelTile (w h : Nat) (list : Scene.DisplayList) : Tile where
  list := list
  slope := [(ratToFloat32 (pixelX w).slope).toBits, (ratToFloat32 (pixelY h).slope).toBits]
  offset := [(ratToFloat32 (pixelX w).offset).toBits, (ratToFloat32 (pixelY h).offset).toBits]
  scissor := pixelScissor w h

/-- A colour packed as red, green, blue and alpha from the most significant byte, the operand of `clear`. -/
def clearWord (c : Scene.Color) : UInt32 :=
  c.r.toUInt32 * 16777216 + c.g.toUInt32 * 65536 + c.b.toUInt32 * 256 + c.a.toUInt32

/-- The handle of the renderer's program. -/
def programHandle : UInt32 := 0

/-- The commands that make the renderer's program current and clear the target to `bg`; with `fresh` they first build the program, which a context needs once. The scissor is lifted first, since clearing respects it. -/
def frameSetup (fresh : Bool) (bg : Scene.Color) : List Cmd :=
  (if fresh then [⟨7, [.u32 programHandle]⟩] else []) ++
    [⟨3, [.u32 programHandle]⟩, ⟨8, [.words []]⟩, ⟨6, [.u32 (clearWord bg)]⟩]

/-- The commands of one frame of `list` on a `w` by `h` target: setup, then `compile` of the one tile. -/
def frame (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (list : Scene.DisplayList) (bg : Scene.Color) : Cache × List Cmd :=
  let r := compileCmds tess c [pixelTile w h list]
  (r.1, frameSetup fresh bg ++ r.2)

/-- The wire bytes of a fresh frame of `list` on a `w` by `h` target cleared to `bg`, for the interpreter to run on a new context. -/
def frameBytes (w h : Nat) (list : Scene.DisplayList) (bg : Scene.Color) : ByteArray :=
  ⟨(encode (frame (tessellate ⟨0, 0⟩) {} true w h list bg).2).toArray⟩

end Inkproof.Gpu
