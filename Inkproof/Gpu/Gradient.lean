/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Tessellate
import Inkproof.Scene.Shading

namespace Inkproof.Gpu

open Scene

/-- The number of segments between stops that a gradient can have. -/
def gradientSegments : Nat := 4

/-- The Float32 words of the fragment shader's gradient uniforms: the unit vector of the axis, the start coordinate and the reciprocal length of each of the four segments, and the change of colour (red, green, blue and alpha, each in 0 to 1) across each segment. A segment that a gradient does not use has zeros, and a flat colour has zero changes. -/
structure Gradient where
  axis : List UInt32 := []
  starts : List UInt32 := []
  invs : List UInt32 := []
  d0 : List UInt32 := []
  d1 : List UInt32 := []
  d2 : List UInt32 := []
  d3 : List UInt32 := []
  deriving DecidableEq

/-- The gradient of a flat colour: nothing varies. -/
def Gradient.flat : Gradient :=
  { axis := [0, 0], starts := [0, 0, 0, 0], invs := [0, 0, 0, 0], d0 := [0, 0, 0, 0],
    d1 := [0, 0, 0, 0], d2 := [0, 0, 0, 0], d3 := [0, 0, 0, 0] }

/-- The reciprocal length used for a segment of no length, which makes it a step. -/
def stepInv : UInt32 := (ratToFloat32 (10 ^ 30)).toBits

/-- The change of colour from `a` to `b`, each channel in 0 to 1. -/
def deltaWords (a b : Color) : List UInt32 :=
  [(a.r, b.r), (a.g, b.g), (a.b, b.b), (a.a, b.a)].map fun (x, y) =>
    (ratToFloat32 (((y.toNat : Int) - x.toNat : Int) / 255)).toBits

/-- The uniforms of the gradient along `axis` through the stops `s :: rest`, with positions taken relative to the tile origin `o`. The stops must have at most `gradientSegments + 1` and ascend. -/
def Gradient.ofStops (o : Pt) (axis : GradientAxis) (s : Stop) (rest : List Stop) : Gradient :=
  let segs := (s :: rest).zip rest
  let rel (p : Rat) : Rat := match axis with | .x => p - o.x | .y => p - o.y
  let pad (ws : List UInt32) : List UInt32 := ws ++ List.replicate (gradientSegments - ws.length) 0
  let delta (i : Nat) : List UInt32 :=
    (segs[i]?.map fun (a, b) => deltaWords a.color b.color).getD [0, 0, 0, 0]
  { axis := match axis with | .x => [(1 : Float32).toBits, 0] | .y => [0, (1 : Float32).toBits]
    starts := pad (segs.map fun (a, _) => (ratToFloat32 (rel a.pos)).toBits)
    invs := pad (segs.map fun (a, b) =>
      if a.pos = b.pos then stepInv else (ratToFloat32 (1 / (b.pos - a.pos))).toBits)
    d0 := delta 0, d1 := delta 1, d2 := delta 2, d3 := delta 3 }

/-- Whether stops ascend, adjacent ones possibly sharing a position. -/
def stopsAscend : List Stop → Bool
  | a :: b :: rest => decide (a.pos ≤ b.pos) && stopsAscend (b :: rest)
  | _ => true

/-- The colour at the first stop and the gradient of a shading, relative to the tile origin `o`; `none` for a gradient that the renderer cannot draw, which has too many stops or stops that descend. -/
def shadingState (o : Pt) : Shading → Option (Color × Gradient)
  | .flat c => some (c, .flat)
  | .gradient axis s rest =>
    if rest.length ≤ gradientSegments ∧ stopsAscend (s :: rest) = true
    then some (s.color, .ofStops o axis s rest) else none

end Inkproof.Gpu
