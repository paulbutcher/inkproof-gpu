/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Compile
import Inkproof.Gpu.Tessellate
import Inkproof.Scale.Affine
import Inkproof.Scale.Linear

namespace Inkproof.Gpu

/-- The map from pixel columns of a `w` pixel wide target to clip x, before rounding to Float32. -/
def pixelX (w : Nat) : Scale.Affine Rat := ⟨2 / w, -1⟩

/-- The map from pixel rows of a `h` pixel high target, counted down from the top, to clip y, before rounding to Float32. -/
def pixelY (h : Nat) : Scale.Affine Rat := ⟨-2 / h, 1⟩

/-- The view uniform of a `w` by `h` target: half its width and height, then their reciprocals doubled, which is the factor from clip space to pixels and back. -/
def viewWords (w h : Nat) : List UInt32 :=
  [(ratToFloat32 (w / 2)).toBits, (ratToFloat32 (h / 2)).toBits,
   (ratToFloat32 (2 / w)).toBits, (ratToFloat32 (2 / h)).toBits]

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
  view := viewWords w h
  stride := 2
  size := fun _ => [0]
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

/-- The intervals of data a view shows: `x0` to `x1` across, `y0` to `y1` upwards. -/
structure View where
  x0 : Rat
  x1 : Rat
  y0 : Rat
  y1 : Rat

/-- The map from data x to a pixel column that sends the view's `x0` and `x1` to the left and right of `plot`, a rectangle in pixels from the top left. -/
def viewX (v : View) (plot : Scene.Rect) : Scale.Affine Rat :=
  (Scale.Linear.mk v.x0 v.x1 plot.x0 plot.x1).toAffine

/-- The map from data y to a pixel row from the top that sends the view's `y0` and `y1` to the bottom and top of `plot`. -/
def viewY (v : View) (plot : Scene.Rect) : Scale.Affine Rat :=
  (Scale.Linear.mk v.y0 v.y1 plot.y1 plot.y0).toAffine

/-- The scissor for a rectangle in data coordinates: its image in pixels, corners in ascending order. -/
def viewScissor (w h : Nat) (v : View) (plot : Scene.Rect) (r : Scene.Rect) : List UInt32 :=
  let ax := (viewX v plot).apply r.x0
  let bx := (viewX v plot).apply r.x1
  let ay := (viewY v plot).apply r.y0
  let by_ := (viewY v plot).apply r.y1
  pixelScissor w h ⟨min ax bx, min ay by_, max ax bx, max ay by_⟩

/-- The display list with every shape clipped to the view, so that nothing is drawn outside the plot. -/
def View.clip (v : View) (list : Scene.DisplayList) : Scene.DisplayList :=
  list.map fun c => { c with shape := .clipped ⟨v.x0, v.y0, v.x1, v.y1⟩ c.shape }

/-- A tile of a display list in data coordinates, drawn so that the view fills `plot`, a rectangle in pixels from the top left of a `w` by `h` target. Only the uniforms and scissors depend on the view, so the vertex words are those of the list itself. The half width of a strip and the radius of a marker are in pixels, whatever the view: the vertex words must be `tessellateStroke`'s. -/
def viewTile (w h : Nat) (v : View) (plot : Scene.Rect) (list : Scene.DisplayList) : Tile where
  list := v.clip list
  slope := [(ratToFloat32 ((pixelX w).comp (viewX v plot)).slope).toBits,
    (ratToFloat32 ((pixelY h).comp (viewY v plot)).slope).toBits]
  offset := [(ratToFloat32 ((pixelX w).comp (viewX v plot)).offset).toBits,
    (ratToFloat32 ((pixelY h).comp (viewY v plot)).offset).toBits]
  view := viewWords w h
  stride := 6
  size := strokeSizeWords
  scissor := viewScissor w h v plot

/-- The commands of one frame of `list`, in data coordinates, under `v` on a `w` by `h` target cleared to `bg`. A later frame of the same list under another view uploads nothing. -/
def viewFrame (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (v : View) (plot : Scene.Rect) (list : Scene.DisplayList) (bg : Scene.Color) :
    Cache × List Cmd :=
  let r := compileCmds tess c [viewTile w h v plot list]
  (r.1, frameSetup fresh bg ++ r.2)

/-- A tile of a display list in device pixels whose vertices are `tessellateStroke`'s, so that it can be compiled beside a `viewTile` and its strips and markers are sized in pixels as theirs are. -/
def pixelStrokeTile (w h : Nat) (list : Scene.DisplayList) : Tile :=
  { pixelTile w h list with stride := 6, size := strokeSizeWords }

/-- The commands of one frame of `list`, in data coordinates, under `v`, and `overlay`, in device pixels from the top left, such as axes and gridlines, on a `w` by `h` target cleared to `bg`. Both are compiled together, so zooming uploads nothing for `list`. -/
def viewOverlayFrame (tess : Scene.Command → List UInt32) (c : Cache) (fresh : Bool) (w h : Nat)
    (v : View) (plot : Scene.Rect) (list overlay : Scene.DisplayList) (bg : Scene.Color) :
    Cache × List Cmd :=
  let r := compileCmds tess c [viewTile w h v plot list, pixelStrokeTile w h overlay]
  (r.1, frameSetup fresh bg ++ r.2)

/-- The wire bytes of a fresh frame of `list`, in data coordinates, under `v`, with strips and markers sized in pixels. -/
def viewFrameBytes (w h : Nat) (v : View) (plot : Scene.Rect) (list : Scene.DisplayList)
    (bg : Scene.Color) : ByteArray :=
  ⟨(encode (viewFrame (tessellateStroke ⟨0, 0⟩) {} true w h v plot list bg).2).toArray⟩

/-- The wire bytes of a fresh frame of `list` under `v` and `overlay` in device pixels, with strips and markers of both sized in pixels. -/
def viewOverlayFrameBytes (w h : Nat) (v : View) (plot : Scene.Rect)
    (list overlay : Scene.DisplayList) (bg : Scene.Color) : ByteArray :=
  ⟨(encode (viewOverlayFrame (tessellateStroke ⟨0, 0⟩) {} true w h v plot list overlay bg).2).toArray⟩

end Inkproof.Gpu
