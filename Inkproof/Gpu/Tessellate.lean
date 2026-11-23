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

/-- The triangles of the area between the segment from `(x0, ya)` to `(x1, yb)` and the line `y = y0`. A pair on one side of the line is a quadrilateral of two triangles; a pair that crosses it is split at the crossing into one triangle each side, since the quadrilateral would be a bow-tie. -/
def areaTriangles (x0 x1 y0 ya yb : Rat) : List Tri :=
  if (ya - y0) * (yb - y0) < 0 then
    let xc := x0 + (ya - y0) / (ya - yb) * (x1 - x0)
    [⟨⟨x0, y0⟩, ⟨x0, ya⟩, ⟨xc, y0⟩⟩, ⟨⟨x1, y0⟩, ⟨x1, yb⟩, ⟨xc, y0⟩⟩]
  else spanTriangles x0 x1 y0 y0 ya yb

/-- The triangles of a chain of items: those of each value and of each pair of adjacent values, with none across a gap. -/
def chainTriangles {α : Type} (single : α → List Tri) (join : α → α → List Tri)
    (items : List (Item α)) : List Tri :=
  (Item.fold single join items).flatten

/-- The corner offset of the octagon around a circle, as a fraction of the radius. It is `tan (π / 8)`, rounded up. -/
private def octagonSlope : Rat := 4143 / 10000

/-- How far, in the units of the radius, a circle's drawn edge may lie outside it. -/
def discTolerance : Rat := 1 / 4

/-- The number of tangent points in each quarter of the polygon about a circle of radius `r`: the fewest, from two to 64, with `5 r / 4 ≤ m²`, for which its corners lie within `discTolerance` of the circle (a corner of a regular polygon of `4m` sides is `r * π² / (32 m²)` out), so a radius of up to about 3 has the eight triangles of an octagon. -/
def discQuarter (r : Rat) : Nat :=
  ((List.range' 2 63).find? fun (m : Nat) => r * 5 / 4 ≤ (m : Rat) * (m : Rat)).getD 64

/-- A rational approximation of `tan x` for `0 ≤ x ≤ π / 4`, within 0.0003 (Padé). -/
private def tanApprox (x : Rat) : Rat := x * (15 - x ^ 2) / (15 - 6 * x ^ 2)

/-- The `4m` points of the unit circle at which the polygon is tangent to it, from `(1, 0)` anticlockwise and evenly spaced in angle to within the approximation of `tanApprox`. A point of angle `2 * atan t` is `((1 - t²) / (1 + t²), 2t / (1 + t²))`, so it is rational and exactly on the circle. -/
def discTangents (m : Nat) : List (Rat × Rat) :=
  let q := (List.range m).map fun (j : Nat) =>
    let t := tanApprox ((355 / 113 : Rat) * (j : Rat) / (4 * (m : Rat)))
    ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))
  q ++ q.map (fun p => (-p.2, p.1)) ++ q.map (fun p => (-p.1, -p.2)) ++ q.map (fun p => (p.2, -p.1))

/-- The corners of the polygon about the unit circle that is tangent to it at `discTangents m`, in order: the corner between tangent points `a` and `b` is `(a + b) / (1 + a . b)`, where their tangent lines meet. The polygon contains the disc. -/
def discRing (m : Nat) : List (Rat × Rat) :=
  let t := discTangents m
  (t.zip (t.drop 1 ++ t.take 1)).map fun (a, b) =>
    let k := 1 + a.1 * b.1 + a.2 * b.2
    ((a.1 + b.1) / k, (a.2 + b.2) / k)

/-- The triangles of the polygon about the circle of radius `r` about `c`, a fan from the centre over `discRing`. It contains the disc, and its corners lie at most `discTolerance` outside it. That it contains the disc is checked by a test, not proved: the fan is `4m` triangles for a count that depends on `r`, and a point of the disc must be placed in the sector of its angle, which needs the cyclic order of the corners; no proof of that for every `m` was found, and the tangent lines alone give only that the disc lies in the polygon, not in the fan. -/
def discTriangles (c : Pt) (r : Rat) : List Tri :=
  let v := (discRing (discQuarter r)).map fun p => (⟨c.x + r * p.1, c.y + r * p.2⟩ : Pt)
  (v.zip (v.drop 1 ++ v.take 1)).map fun (a, b) => ⟨c, a, b⟩

/-- The triangles that cover a shape, in grid coordinates. A clipped shape gives the triangles of what it clips, so a scissor is needed to keep the drawing inside the box. A circle is drawn as a polygon about it and text as its box. -/
def triangles : Shape → List Tri
  | .strip hw items => stripTriangles hw items
  | .envelope items =>
    chainTriangles (fun c => spanTriangles c.x c.x c.lo c.lo c.hi c.hi)
      (fun a b => spanTriangles a.x b.x a.lo b.lo a.hi b.hi) items
  | .area y0 items =>
    chainTriangles (fun a => spanTriangles a.x a.x y0 y0 a.y a.y)
      (fun a b => areaTriangles a.x b.x y0 a.y b.y) items
  | .rect b => boxTriangles b.x0 b.y0 b.x1 b.y1
  | .marker .square c r => boxTriangles (c.x - r) (c.y - r) (c.x + r) (c.y + r)
  | .marker .circle c r => discTriangles c r
  | .text b _ => boxTriangles b.x0 b.y0 b.x1 b.y1
  | .clipped _ s => triangles s

/-- A Float32 near `q`: the quotient of its numerator and denominator, each rounded to Float32 first. -/
def ratToFloat32 (q : Rat) : Float32 := Float32.ofInt q.num / Float32.ofNat q.den

/-- A vertex of a stroke: a position, a direction in the same coordinates, and a corner. The vertex shader moves the position by the corner times the stroke size in pixels, along the direction as it appears on screen (`kx`) and across it (`ky`), so the geometry does not depend on the view. -/
structure Vtx where
  pos : Pt
  dir : Pt
  kx : Rat
  ky : Rat

/-- The six words of a vertex: its position relative to `origin`, its direction and its corner, each coordinate a Float32. The subtraction is exact. -/
def Vtx.words (origin : Pt) (v : Vtx) : List UInt32 :=
  [(ratToFloat32 (v.pos.x - origin.x)).toBits, (ratToFloat32 (v.pos.y - origin.y)).toBits,
   (ratToFloat32 v.dir.x).toBits, (ratToFloat32 v.dir.y).toBits,
   (ratToFloat32 v.kx).toBits, (ratToFloat32 v.ky).toBits]

/-- A point with no stroke offset: the direction is a placeholder and the corner is zero. -/
def Vtx.plain (p : Pt) : Vtx := ⟨p, ⟨1, 0⟩, 0, 0⟩

/-- A vertex as the two words of its Float32 coordinates relative to `origin`, which the vertex shader reads. The subtraction is exact. -/
def vertexWords (origin p : Pt) : List UInt32 :=
  [(ratToFloat32 (p.x - origin.x)).toBits, (ratToFloat32 (p.y - origin.y)).toBits]

/-- The vertex words of a triangle. -/
def triWords (origin : Pt) (t : Tri) : List UInt32 :=
  vertexWords origin t.a ++ vertexWords origin t.b ++ vertexWords origin t.c

/-- The vertex words of a command, three vertices per triangle, with coordinates relative to `origin`. `tessellate origin` is the `tess` that `compile` takes, with `origin` the tile origin that the transform uniform is rebased to. Strips and markers are baked at their size in list units, and a vertex is its two position words. -/
def tessellate (origin : Pt) (c : Command) : List UInt32 :=
  ((triangles c.shape).map (triWords origin)).flatten

/-- The two triangles of the rectangle about the segment from `a` to `b`, with no extension past its ends, as stroke vertices that sit at `a` or `b`. -/
def segVertices (a b : Pt) : List Vtx :=
  let d := a.dir b
  [⟨a, d, 0, -1⟩, ⟨b, d, 0, -1⟩, ⟨a, d, 0, 1⟩, ⟨b, d, 0, 1⟩, ⟨a, d, 0, 1⟩, ⟨b, d, 0, -1⟩]

/-- The vertices of the square marker about `c`, with the corner as its offset in units of the radius. -/
def squareVertices (c : Pt) : List Vtx :=
  [⟨c, ⟨1, 0⟩, -1, -1⟩, ⟨c, ⟨1, 0⟩, 1, -1⟩, ⟨c, ⟨1, 0⟩, -1, 1⟩,
   ⟨c, ⟨1, 0⟩, 1, 1⟩, ⟨c, ⟨1, 0⟩, -1, 1⟩, ⟨c, ⟨1, 0⟩, 1, -1⟩]

/-- The vertices of the octagon about the circle about `c`, as a fan from the centre, with corners in units of the radius along and across `d`. -/
def octagonVertices (c d : Pt) : List Vtx :=
  let k := octagonSlope
  let v : List (Rat × Rat) :=
    [(1, -k), (1, k), (k, 1), (-k, 1), (-1, k), (-1, -k), (-k, -1), (k, -1)]
  let ring := v ++ v.take 1
  (ring.zip (ring.drop 1)).flatMap fun (a, b) =>
    [⟨c, d, 0, 0⟩, ⟨c, d, a.1, a.2⟩, ⟨c, d, b.1, b.2⟩]

/-- The vertices of the polygon of `discTriangles` about `c` for a circle of radius `r`, with corners in units of the radius, as a fan from the centre. -/
def discVertices (r : Rat) (c : Pt) : List Vtx :=
  let ring := discRing (discQuarter r)
  (ring.zip (ring.drop 1 ++ ring.take 1)).flatMap fun (a, b) =>
    [⟨c, ⟨1, 0⟩, 0, 0⟩, ⟨c, ⟨1, 0⟩, a.1, a.2⟩, ⟨c, ⟨1, 0⟩, b.1, b.2⟩]

/-- The half of the octagon about `c` that lies ahead of `c` along `d`, as a fan from the centre. Its straight edge is across `d` through `c`, with the corners that the rectangle about a segment has at its end, so a cap and a segment that meet there share an edge and cover nothing twice. -/
def capVertices (c d : Pt) : List Vtx :=
  let k := octagonSlope
  let ring : List (Rat × Rat) := [(0, -1), (k, -1), (1, -k), (1, k), (k, 1), (0, 1)]
  (ring.zip (ring.drop 1)).flatMap fun (a, b) =>
    [⟨c, d, 0, 0⟩, ⟨c, d, a.1, a.2⟩, ⟨c, d, b.1, b.2⟩]

/-- The vertices of a strip: the rectangle about each segment between adjacent values, a half octagon beyond each end of a run of values, which with the rectangle makes the disc that Scene's round caps make, and a whole octagon about each value between two, for its round joins. A run of one value is one octagon. Each octagon corner is `1 / cos (π / 8)`, about 1.082, times the half width from its value, so the strip is never more than about 8% of its half width wider than the thickened polyline. An octagon or cap is turned to the direction of the segment beside it, so that its sides across that segment are placed by the same arithmetic as the segment's own and a thin stroke has no step where they meet. `prev` is the direction of the segment that arrives at the first value, if there is one. -/
def stripVerticesFrom (prev : Option Pt) : List (Item Pt) → List Vtx
  | [] => []
  | .gap :: rest => stripVerticesFrom none rest
  | .val a :: rest =>
    match rest with
    | .val b :: _ =>
      let d := a.dir b
      (match prev with
        | none => capVertices a ⟨-d.x, -d.y⟩
        | some _ => octagonVertices a d) ++ segVertices a b ++ stripVerticesFrom (some d) rest
    | _ =>
      (match prev with
        | none => octagonVertices a ⟨1, 0⟩
        | some d => capVertices a d) ++ stripVerticesFrom none rest

/-- The vertices of a strip, as `stripVerticesFrom` with no segment before the first value. -/
def stripVertices (items : List (Item Pt)) : List Vtx := stripVerticesFrom none items

/-- The vertices that cover a shape when drawn by the vertex shader at its stroke size, which `strokeSize` gives. A strip or a marker is described apart from its size, so the vertices are the same in every view; the other shapes are as in `triangles`. -/
def strokeVertices : Shape → List Vtx
  | .strip _ items => stripVertices items
  | .marker .square c _ => squareVertices c
  | .marker .circle c r => discVertices r c
  | .clipped _ s => strokeVertices s
  | s => (triangles s).flatMap fun t => [Vtx.plain t.a, Vtx.plain t.b, Vtx.plain t.c]

/-- The half width of a strip or the radius of a marker, which the vertex shader applies in pixels; zero for the other shapes. -/
def strokeSize : Shape → Rat
  | .strip hw _ => hw
  | .marker _ _ r => r
  | .clipped _ s => strokeSize s
  | _ => 0

/-- The word of a shape's stroke size as a Float32, the operand of the size uniform. -/
def strokeSizeWords (s : Shape) : List UInt32 := [(ratToFloat32 (strokeSize s)).toBits]

/-- The vertex words of a command for a view-independent stroke: `tessellate`, except that the half width of a strip and the radius of a marker are left to the size uniform, so that they are in pixels whatever the transform. -/
def tessellateStroke (origin : Pt) (c : Command) : List UInt32 :=
  (strokeVertices c.shape).flatMap (Vtx.words origin)

end Inkproof.Gpu
