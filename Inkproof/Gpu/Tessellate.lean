/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Line

namespace Inkproof.Gpu

open Scene

/-- The two triangles of the rectangle with opposite corners `(x0, y0)` and `(x1, y1)`. -/
def boxTriangles (x0 y0 x1 y1 : Rat) : List Tri :=
  [⟨⟨x0, y0⟩, ⟨x1, y0⟩, ⟨x0, y1⟩⟩, ⟨⟨x1, y1⟩, ⟨x0, y1⟩, ⟨x1, y0⟩⟩]

/-- The two triangles of the quadrilateral swept by the vertical segment that runs from `l0` to `h0` at `x0` and from `l1` to `h1` at `x1`. The diagonal joins `(x0, h0)` to `(x1, l1)`. -/
def spanTriangles (x0 x1 l0 l1 h0 h1 : Rat) : List Tri :=
  [⟨⟨x0, l0⟩, ⟨x0, h0⟩, ⟨x1, l1⟩⟩, ⟨⟨x1, h1⟩, ⟨x1, l1⟩, ⟨x0, h0⟩⟩]

/-- The triangles of a chain of items: those of each value and of each pair of adjacent values, with none across a gap. -/
def chainTriangles {α : Type} (single : α → List Tri) (join : α → α → List Tri) :
    List (Item α) → List Tri
  | [] => []
  | .gap :: rest => chainTriangles single join rest
  | .val a :: rest =>
    single a ++
      (match rest with
        | .val b :: _ => join a b
        | _ => []) ++ chainTriangles single join rest

/-- The corner offset of the octagon around a circle, as a fraction of the radius. It is `tan (π / 8)`, rounded up. -/
private def octagonSlope : Rat := 4143 / 10000

/-- The regular octagon around the circle of radius `r` about `c`, as a fan from the centre. It contains the circle, and its corners lie up to about 8% of the radius outside it. Containment is checked by a test, not proved: it needs a case split over the eight sectors, each with a nonlinear bound on `x² + y² ≤ r²` that `grind` and `nlinarith`-style attempts did not close in a few tries. -/
def octagonTriangles (c : Pt) (r : Rat) : List Tri :=
  let k := octagonSlope * r
  let v : List Pt :=
    [⟨c.x + r, c.y - k⟩, ⟨c.x + r, c.y + k⟩, ⟨c.x + k, c.y + r⟩, ⟨c.x - k, c.y + r⟩,
     ⟨c.x - r, c.y + k⟩, ⟨c.x - r, c.y - k⟩, ⟨c.x - k, c.y - r⟩, ⟨c.x + k, c.y - r⟩]
  (v.zip (v.drop 1 ++ v.take 1)).map fun (a, b) => ⟨c, a, b⟩

/-- The triangles that cover a shape, in grid coordinates. A clipped shape gives the triangles of what it clips, so a scissor is needed to keep the drawing inside the box. A circle is drawn as an octagon about it and text as its box. -/
def triangles : Shape → List Tri
  | .strip hw items => stripTriangles hw items
  | .envelope items =>
    chainTriangles (fun c => spanTriangles c.x c.x c.lo c.lo c.hi c.hi)
      (fun a b => spanTriangles a.x b.x a.lo b.lo a.hi b.hi) items
  | .area y0 items =>
    chainTriangles (fun a => spanTriangles a.x a.x y0 y0 a.y a.y)
      (fun a b => spanTriangles a.x b.x y0 y0 a.y b.y) items
  | .rect b => boxTriangles b.x0 b.y0 b.x1 b.y1
  | .marker .square c r => boxTriangles (c.x - r) (c.y - r) (c.x + r) (c.y + r)
  | .marker .circle c r => octagonTriangles c r
  | .text b _ => boxTriangles b.x0 b.y0 b.x1 b.y1
  | .clipped _ s => triangles s

/-- A Float32 near `q`: the quotient of its numerator and denominator, each rounded to Float32 first. -/
def ratToFloat32 (q : Rat) : Float32 := Float32.ofInt q.num / Float32.ofNat q.den

/-- A vertex as the two words of its Float32 coordinates relative to `origin`, which the vertex shader reads. The subtraction is exact. -/
def vertexWords (origin p : Pt) : List UInt32 :=
  [(ratToFloat32 (p.x - origin.x)).toBits, (ratToFloat32 (p.y - origin.y)).toBits]

/-- The vertex words of a triangle. -/
def triWords (origin : Pt) (t : Tri) : List UInt32 :=
  vertexWords origin t.a ++ vertexWords origin t.b ++ vertexWords origin t.c

/-- The vertex words of a command, three vertices per triangle, with coordinates relative to `origin`. `tessellate origin` is the `tess` that `compile` takes, with `origin` the tile origin that the transform uniform is rebased to. -/
def tessellate (origin : Pt) (c : Command) : List UInt32 :=
  ((triangles c.shape).map (triWords origin)).flatten

end Inkproof.Gpu
