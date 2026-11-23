/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Tessellate

namespace Inkproof.Gpu

open Scene

/-- A triangle's words are those of its three vertices in order. -/
theorem triWords_eq (origin : Pt) (t : Tri) :
    triWords origin t = vertexWords origin t.a ++ vertexWords origin t.b ++ vertexWords origin t.c := rfl

/-- A vertex's words are the bits of its two coordinates relative to the origin, each rounded to Float32. -/
theorem vertexWords_eq (origin p : Pt) :
    vertexWords origin p =
      [(ratToFloat32 (p.x - origin.x)).toBits, (ratToFloat32 (p.y - origin.y)).toBits] := rfl

/-- A stroke vertex's words are the bits of its position relative to the origin, its direction and its corner, each coordinate rounded to Float32. -/
theorem Vtx.words_eq (origin : Pt) (v : Vtx) :
    v.words origin =
      [(ratToFloat32 (v.pos.x - origin.x)).toBits, (ratToFloat32 (v.pos.y - origin.y)).toBits,
       (ratToFloat32 v.dir.x).toBits, (ratToFloat32 v.dir.y).toBits,
       (ratToFloat32 v.kx).toBits, (ratToFloat32 v.ky).toBits] := rfl

/-- A command's stroke words are those of its stroke vertices, in order. -/
theorem tessellateStroke_eq (origin : Pt) (c : Command) :
    tessellateStroke origin c = (strokeVertices c.shape).flatMap (Vtx.words origin) := rfl

/-- A command's stroke words are six per vertex. -/
theorem tessellateStroke_length (origin : Pt) (c : Command) :
    (tessellateStroke origin c).length = 6 * (strokeVertices c.shape).length := by
  unfold tessellateStroke
  generalize strokeVertices c.shape = vs
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; show 6 + _ = _; grind

/-- The size of a strip or marker is its half width or radius; of any other shape, zero. -/
theorem strokeSize_strip (hw : Rat) (items : List (Item Pt)) : strokeSize (.strip hw items) = hw := rfl

theorem strokeSize_marker (k : MarkerShape) (c : Pt) (r : Rat) : strokeSize (.marker k c r) = r := rfl

theorem strokeSize_rect (b : Rect) : strokeSize (.rect b) = 0 := rfl

theorem strokeSize_clipped (b : Rect) (s : Shape) : strokeSize (.clipped b s) = strokeSize s := rfl

theorem strokeSizeWords_eq (s : Shape) :
    strokeSizeWords s = [(ratToFloat32 (strokeSize s)).toBits] := rfl

/-- A segment and a square marker have 6 vertices. -/
theorem segVertices_length (a b : Pt) : (segVertices a b).length = 6 := rfl

theorem Vtx.plain_eq (p : Pt) : Vtx.plain p = ⟨p, ⟨1, 0⟩, 0, 0⟩ := rfl

theorem squareVertices_eq (c : Pt) :
    squareVertices c =
      [⟨c, ⟨1, 0⟩, -1, -1⟩, ⟨c, ⟨1, 0⟩, 1, -1⟩, ⟨c, ⟨1, 0⟩, -1, 1⟩,
       ⟨c, ⟨1, 0⟩, 1, 1⟩, ⟨c, ⟨1, 0⟩, -1, 1⟩, ⟨c, ⟨1, 0⟩, 1, -1⟩] := rfl

/-- The octagon is a fan of eight triangles from the centre over the ring of its corners. -/
theorem octagonVertices_eq (c d : Pt) :
    octagonVertices c d =
      let k : Rat := 4143 / 10000
      let v : List (Rat × Rat) :=
        [(1, -k), (1, k), (k, 1), (-k, 1), (-1, k), (-1, -k), (-k, -1), (k, -1)]
      let ring := v ++ v.take 1
      (ring.zip (ring.drop 1)).flatMap fun (a, b) =>
        [⟨c, d, 0, 0⟩, ⟨c, d, a.1, a.2⟩, ⟨c, d, b.1, b.2⟩] := rfl

theorem squareVertices_length (c : Pt) : (squareVertices c).length = 6 := rfl

theorem octagonVertices_length (c d : Pt) : (octagonVertices c d).length = 24 := rfl

/-- The cap is a fan of five triangles from the centre over the ring of the corners ahead of it. -/
theorem capVertices_eq (c d : Pt) :
    capVertices c d =
      let k : Rat := 4143 / 10000
      let ring : List (Rat × Rat) := [(0, -1), (k, -1), (1, -k), (1, k), (k, 1), (0, 1)]
      (ring.zip (ring.drop 1)).flatMap fun (a, b) =>
        [⟨c, d, 0, 0⟩, ⟨c, d, a.1, a.2⟩, ⟨c, d, b.1, b.2⟩] := rfl

theorem capVertices_length (c d : Pt) : (capVertices c d).length = 15 := rfl

/-- A command's words are those of its triangles, in order. -/
theorem tessellate_eq (origin : Pt) (c : Command) :
    tessellate origin c = ((triangles c.shape).map (triWords origin)).flatten := rfl

theorem triWords_length (origin : Pt) (t : Tri) : (triWords origin t).length = 6 := rfl

/-- A command's vertex words are six per triangle. -/
theorem tessellate_length (origin : Pt) (c : Command) :
    (tessellate origin c).length = 6 * (triangles c.shape).length := by
  unfold tessellate
  generalize triangles c.shape = ts
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]; rw [triWords_length]; grind

/-- The tangent points are the first quarter, `j` steps of `π / (2 m)` through the Padé approximation of the tangent, followed by its rotations by a quarter, a half and three quarters of a turn. -/
theorem discTangents_eq (m : Nat) :
    discTangents m =
      let q := (List.range m).map fun (j : Nat) =>
        let x := (355 / 113 : Rat) * (j : Rat) / (4 * (m : Rat))
        let t := x * (15 - x ^ 2) / (15 - 6 * x ^ 2)
        ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))
      q ++ q.map (fun p => (-p.2, p.1)) ++ q.map (fun p => (-p.1, -p.2)) ++ q.map (fun p => (p.2, -p.1)) := rfl

theorem discTangents_length (m : Nat) : (discTangents m).length = 4 * m := by
  simp [discTangents]; omega

/-- The consecutive pairs of a ring, the last with the first, are as many as its items. -/
theorem ring_pairs_length {α : Type} (l : List α) : (l.zip (l.drop 1 ++ l.take 1)).length = l.length := by
  rw [List.length_zip, List.length_append, List.length_drop, List.length_take]; omega

theorem discRing_length (m : Nat) : (discRing m).length = 4 * m := by
  simp only [discRing, List.length_map, ring_pairs_length, discTangents_length]

/-- A circle's polygon has `4m` triangles, with `m` the quarter count that its radius gives. -/
theorem discTriangles_length (c : Pt) (r : Rat) : (discTriangles c r).length = 4 * discQuarter r := by
  simp only [discTriangles, List.length_map, ring_pairs_length, discRing_length]

/-- A radius of up to 3 has the eight triangles of an octagon. -/
theorem discTriangles_small (c : Pt) {r : Rat} (h : r ≤ 3) : (discTriangles c r).length = 8 := by
  have : discQuarter r = 2 := by
    have h2 : r * 5 / 4 ≤ ((2 : Nat) : Rat) * ((2 : Nat) : Rat) := by push_cast; grind
    have h3 : decide (r * 5 / 4 ≤ ((2 : Nat) : Rat) * ((2 : Nat) : Rat)) = true := decide_eq_true h2
    have h4 : List.range' 2 63 = 2 :: List.range' 3 62 := rfl
    simp only [discQuarter, h4, List.find?_cons, h3]
    rfl
  rw [discTriangles_length, this]

/-- The quarter count is the first `m` from two with `5 r / 4 ≤ m²`, or 64 if none up to 63 has. -/
theorem discQuarter_eq (r : Rat) :
    discQuarter r = ((List.range' 2 63).find? fun (m : Nat) => r * 5 / 4 ≤ (m : Rat) * (m : Rat)).getD 64 := rfl

/-- A circle's polygon is the fan from its centre over the scaled and shifted corners of `discRing`. -/
theorem discTriangles_eq (c : Pt) (r : Rat) :
    discTriangles c r =
      (let v := (discRing (discQuarter r)).map fun p => (⟨c.x + r * p.1, c.y + r * p.2⟩ : Pt)
       (v.zip (v.drop 1 ++ v.take 1)).map fun (a, b) => ⟨c, a, b⟩) := rfl

/-- The corners are where the tangent lines at consecutive tangent points meet. -/
theorem discRing_eq (m : Nat) :
    discRing m =
      ((discTangents m).zip ((discTangents m).drop 1 ++ (discTangents m).take 1)).map fun (a, b) =>
        ((a.1 + b.1) / (1 + a.1 * b.1 + a.2 * b.2), (a.2 + b.2) / (1 + a.1 * b.1 + a.2 * b.2)) := rfl

/-- The vertices of a circle are three per corner pair of `discRing`: the centre, then the pair, in units of the radius. -/
theorem discVertices_eq (r : Rat) (c : Pt) :
    discVertices r c =
      (let ring := discRing (discQuarter r)
       (ring.zip (ring.drop 1 ++ ring.take 1)).flatMap fun (a, b) =>
         [⟨c, ⟨1, 0⟩, 0, 0⟩, ⟨c, ⟨1, 0⟩, a.1, a.2⟩, ⟨c, ⟨1, 0⟩, b.1, b.2⟩]) := rfl

theorem discVertices_length (r : Rat) (c : Pt) : (discVertices r c).length = 12 * discQuarter r := by
  have key : ∀ l : List ((Rat × Rat) × (Rat × Rat)),
      (l.flatMap fun (a, b) => ([⟨c, ⟨1, 0⟩, 0, 0⟩, ⟨c, ⟨1, 0⟩, a.1, a.2⟩, ⟨c, ⟨1, 0⟩, b.1, b.2⟩] : List Vtx)).length
        = 3 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; omega
  unfold discVertices
  simp only []
  rw [key, ring_pairs_length, discRing_length]; omega

theorem between_param {a b v : Rat} (h : Between a b v) :
    ∃ s : Rat, 0 ≤ s ∧ s ≤ 1 ∧ v = a + s * (b - a) := by
  by_cases hab : a = b
  · subst hab
    exact ⟨0, by grind, by grind, by unfold Between at h; grind⟩
  · obtain ⟨s, hs⟩ : ∃ s, s * (b - a) = v - a := ⟨_, Rat.div_mul_cancel (by grind)⟩
    refine ⟨s, ?_, ?_, by grind⟩ <;>
    (unfold Between at h
     apply Classical.byContradiction; intro hc
     rcases Classical.em (b - a < 0) with hd | hd <;>
     first
        | have := Rat.mul_pos (show 0 < -s by grind) (show 0 < -(b - a) by grind); grind
        | have := Rat.mul_pos (show 0 < -s by grind) (show 0 < b - a by grind); grind
        | have := Rat.mul_pos (show 0 < s - 1 by grind) (show 0 < -(b - a) by grind); grind
        | have := Rat.mul_pos (show 0 < s - 1 by grind) (show 0 < b - a by grind); grind)

theorem box_sub_boxTriangles {x0 y0 x1 y1 : Rat} {p : Pt} (h : Region.box x0 y0 x1 y1 p) :
    ∃ t ∈ boxTriangles x0 y0 x1 y1, t.region p := by
  obtain ⟨u, hu0, hu1, hx⟩ := between_param h.1
  obtain ⟨v, hv0, hv1, hy⟩ := between_param h.2
  have := parallelogram_sub_tris ⟨x0, y0⟩ ⟨x1 - x0, 0⟩ ⟨0, y1 - y0⟩ u v hu0 hu1 hv0 hv1
  have hp : p = ⟨x0 + u * (x1 - x0) + v * 0, y0 + u * 0 + v * (y1 - y0)⟩ := by
    cases p; simp only [Pt.mk.injEq]; constructor <;> grind
  rw [hp]
  simp only [boxTriangles]
  have ex : x0 + (x1 - x0) = x1 := by grind
  have ey : y0 + (y1 - y0) = y1 := by grind
  rcases this with h1 | h1
  · exact ⟨_, List.mem_cons_self, by simpa [ex, ey, Rat.add_zero] using h1⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simpa [ex, ey, Rat.add_zero] using h1⟩

theorem span_sub_spanTriangles {x0 x1 l0 l1 h0 h1 : Rat} {p : Pt}
    (h : Region.span x0 x1 l0 l1 h0 h1 p) :
    ∃ t ∈ spanTriangles x0 x1 l0 l1 h0 h1, t.region p := by
  obtain ⟨t, ht0, ht1, hx, hy⟩ := h
  have hcase : Between (l0 + t * (l1 - l0)) (h0 + t * (l1 - h0)) p.y ∨
      Between (h0 + t * (l1 - h0)) (h0 + t * (h1 - h0)) p.y := by
    unfold Between at hy ⊢
    grind
  have h1t : 0 ≤ 1 - t := by grind
  rcases hcase with hc | hc
  · obtain ⟨s, hs0, hs1, hs⟩ := between_param hc
    have h1s : 0 ≤ 1 - s := by grind
    refine ⟨_, List.mem_cons_self, (1 - t) * (1 - s), (1 - t) * s, t,
      Rat.mul_nonneg h1t h1s, Rat.mul_nonneg h1t hs0, ht0, by grind, by grind, by grind⟩
  · obtain ⟨s, hs0, hs1, hs⟩ := between_param hc
    have h1s : 0 ≤ 1 - s := by grind
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, t * s, t * (1 - s), 1 - t,
      Rat.mul_nonneg ht0 hs0, Rat.mul_nonneg ht0 h1s, h1t, by grind, by grind, by grind⟩

/-- A pair of values on opposite sides of the baseline is two triangles that meet at the crossing. -/
theorem areaTriangles_cross {x0 x1 y0 ya yb : Rat} (h : (ya - y0) * (yb - y0) < 0) :
    areaTriangles x0 x1 y0 ya yb =
      [⟨⟨x0, y0⟩, ⟨x0, ya⟩, ⟨x0 + (ya - y0) / (ya - yb) * (x1 - x0), y0⟩⟩,
       ⟨⟨x1, y0⟩, ⟨x1, yb⟩, ⟨x0 + (ya - y0) / (ya - yb) * (x1 - x0), y0⟩⟩] := by
  simp [areaTriangles, h]

/-- A pair that does not cross the baseline is the quadrilateral of `spanTriangles`. -/
theorem areaTriangles_of_not_cross {x0 x1 y0 ya yb : Rat} (h : ¬(ya - y0) * (yb - y0) < 0) :
    areaTriangles x0 x1 y0 ya yb = spanTriangles x0 x1 y0 y0 ya yb := by
  simp [areaTriangles, h]

/-- The area between a segment and the line `y = y0` lies in the triangles of `areaTriangles`, whether or not the segment crosses the line. -/
theorem span_sub_areaTriangles {x0 x1 y0 ya yb : Rat} {p : Pt}
    (h : Region.span x0 x1 y0 y0 ya yb p) :
    ∃ t ∈ areaTriangles x0 x1 y0 ya yb, t.region p := by
  unfold areaTriangles
  split
  · rename_i hc
    obtain ⟨t, ht0, ht1, hx, hy⟩ := h
    have hne : ya - yb ≠ 0 := by
      intro h0
      have : ya = yb := by grind
      subst this
      rcases Classical.em (0 ≤ ya - y0) with hd | hd
      · have := Rat.mul_nonneg hd hd
        grind
      · have := Rat.mul_nonneg (show 0 ≤ -(ya - y0) by grind) (show 0 ≤ -(ya - y0) by grind)
        grind
    obtain ⟨s, hs⟩ : ∃ s, s = (ya - y0) / (ya - yb) := ⟨_, rfl⟩
    have hsd : s * (ya - yb) = ya - y0 := by rw [hs]; exact Rat.div_mul_cancel hne
    have hk : 0 < (ya - yb) * (ya - yb) := by
      rcases Classical.em (0 < ya - yb) with hd | hd
      · exact Rat.mul_pos hd hd
      · have : 0 < -(ya - yb) := by grind
        have := Rat.mul_pos this this
        grind
    have sq : ∀ z : Rat, 0 ≤ z * z := fun z => by
      rcases Classical.em (0 ≤ z) with hz | hz
      · exact Rat.mul_nonneg hz hz
      · have := Rat.mul_nonneg (show 0 ≤ -z by grind) (show 0 ≤ -z by grind)
        grind
    have e1 : s * (ya - yb) * (ya - yb) = (ya - y0) * (ya - yb) := by rw [hsd]
    have := sq (ya - y0)
    have := sq (yb - y0)
    have hs0 : 0 < s := by
      apply Classical.byContradiction; intro hh
      have := Rat.mul_nonneg (show 0 ≤ -s by grind) (show 0 ≤ (ya - yb) * (ya - yb) by grind)
      grind
    have hs1 : s < 1 := by
      apply Classical.byContradiction; intro hh
      have := Rat.mul_nonneg (show 0 ≤ s - 1 by grind) (show 0 ≤ (ya - yb) * (ya - yb) by grind)
      grind
    obtain ⟨r, hr0, hr1, hry⟩ := between_param hy
    simp only [Rat.sub_self, Rat.mul_zero, Rat.add_zero] at hry
    have hxc : x0 + (ya - y0) / (ya - yb) * (x1 - x0) = x0 + s * (x1 - x0) := by rw [hs]
    simp only [hxc]
    by_cases hts : t ≤ s
    · obtain ⟨q, hq⟩ : ∃ q, q = t / s := ⟨_, rfl⟩
      have hqs : q * s = t := by rw [hq]; exact Rat.div_mul_cancel (by grind)
      have hq0 : 0 ≤ q := by
        apply Classical.byContradiction; intro hh
        have := Rat.mul_pos (show 0 < -q by grind) hs0
        grind
      have hq1 : q ≤ 1 := by
        apply Classical.byContradiction; intro hh
        have := Rat.mul_pos (show 0 < q - 1 by grind) hs0
        grind
      subst hqs
      refine ⟨_, List.mem_cons_self, (1 - r) * (1 - q), r * (1 - q), q, ?_, ?_, hq0, by grind, ?_, ?_⟩
      · exact Rat.mul_nonneg (by grind) (by grind)
      · exact Rat.mul_nonneg hr0 (by grind)
      · simp only; rw [hx]; grind
      · simp only; rw [hry]; grind
    · obtain ⟨q, hq⟩ : ∃ q, q = (t - s) / (1 - s) := ⟨_, rfl⟩
      have hqs : q * (1 - s) = t - s := by rw [hq]; exact Rat.div_mul_cancel (by grind)
      have hq0 : 0 ≤ q := by
        apply Classical.byContradiction; intro hh
        have := Rat.mul_pos (show 0 < -q by grind) (show 0 < 1 - s by grind)
        grind
      have hq1 : q ≤ 1 := by
        apply Classical.byContradiction; intro hh
        have := Rat.mul_pos (show 0 < q - 1 by grind) (show 0 < 1 - s by grind)
        grind
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (1 - r) * q, r * q, 1 - q, ?_, ?_, by grind, by grind, ?_, ?_⟩
      · exact Rat.mul_nonneg (by grind) hq0
      · exact Rat.mul_nonneg hr0 hq0
      · simp only; rw [hx]; grind
      · simp only; rw [hry]; grind
  · exact span_sub_spanTriangles h

private theorem fold_covered {α : Type} {single : α → Region} {join : α → α → Region}
    {ts : α → List Tri} {tj : α → α → List Tri}
    (hs : ∀ a p, single a p → ∃ t ∈ ts a, t.region p)
    (hj : ∀ a b p, join a b p → ∃ t ∈ tj a b, t.region p) :
    ∀ (items : List (Item α)) (x : Region), x ∈ Item.fold single join items →
      ∃ l ∈ Item.fold ts tj items, ∀ p, x p → ∃ t ∈ l, t.region p
  | [], _, h => by simp [Item.fold] at h
  | .gap :: rest, x, h => by
    rw [Item.fold_gap] at h ⊢
    exact fold_covered hs hj rest x h
  | [.val a], x, h => by
    rw [Item.fold_val_nil] at h ⊢
    simp only [List.mem_singleton] at h
    exact ⟨ts a, by simp, h ▸ hs a⟩
  | .val a :: .gap :: rest, x, h => by
    rw [Item.fold_val_gap] at h ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ts a, by simp, hs a⟩
    · obtain ⟨l, hl, hx⟩ := fold_covered hs hj rest x h
      exact ⟨l, List.mem_cons_of_mem _ hl, hx⟩
  | .val a :: .val b :: rest, x, h => by
    rw [Item.fold_val_val] at h ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ts a, by simp, hs a⟩
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨tj a b, by simp, hj a b⟩
    · obtain ⟨l, hl, hx⟩ := fold_covered hs hj (.val b :: rest) x h
      exact ⟨l, by simp [hl], hx⟩

theorem chain_sub_chainTriangles {α : Type} {single : α → Region} {join : α → α → Region}
    {ts : α → List Tri} {tj : α → α → List Tri}
    (hs : ∀ a p, single a p → ∃ t ∈ ts a, t.region p)
    (hj : ∀ a b p, join a b p → ∃ t ∈ tj a b, t.region p) :
    ∀ (items : List (Item α)) (p : Pt), Item.chain single join items p →
      ∃ t ∈ chainTriangles ts tj items, t.region p := by
  intro items p h
  obtain ⟨x, hx, hp⟩ := (Item.chain_eq_fold single join items p).1 h
  obtain ⟨l, hl, hc⟩ := fold_covered hs hj items x hx
  obtain ⟨t, ht, hr⟩ := hc p hp
  exact ⟨t, by simp only [chainTriangles, List.mem_flatten]; exact ⟨l, hl, ht⟩, hr⟩

/-- The shapes whose triangles are known to cover them: all but circles, whose polygon covers them but without a proof (see `discTriangles`), and strips of no width, which Scene's triangles do not cover. -/
def Polygonal : Shape → Prop
  | .strip hw _ => 0 < hw
  | .marker .circle _ _ => False
  | .clipped _ s => Polygonal s
  | _ => True

/-- Every point of a polygonal shape lies in one of its triangles, so they cover every pixel the shape covers. -/
theorem region_sub_triangles : ∀ (s : Shape), Polygonal s → ∀ p : Pt, s.region p →
    ∃ t ∈ triangles s, t.region p
  | .strip hw items, hp, p, h => strip_region_sub_triangles hp items p h
  | .envelope items, _, p, h =>
    chain_sub_chainTriangles (fun _ _ h => span_sub_spanTriangles h)
      (fun _ _ _ h => span_sub_spanTriangles h) items p h
  | .area y0 items, _, p, h =>
    chain_sub_chainTriangles (fun _ _ h => span_sub_spanTriangles h)
      (fun _ _ _ h => span_sub_areaTriangles h) items p h
  | .rect _, _, _, h => box_sub_boxTriangles h
  | .marker .square _ _, _, _, h => box_sub_boxTriangles h
  | .marker .circle _ _, hp, _, _ => absurd hp id
  | .text _ _, _, _, h => box_sub_boxTriangles h
  | .clipped b s, hp, p, h => by
    simpa [triangles] using region_sub_triangles s hp p h.2

theorem covers_triangles {c : Command} (hp : Polygonal c.shape) {px : Pixel} (h : c.Covers px) :
    ∃ t ∈ triangles c.shape, t.region.Covers px := by
  obtain ⟨p, hr, hc⟩ := h
  obtain ⟨t, ht, htr⟩ := region_sub_triangles c.shape hp p hr
  exact ⟨t, ht, p, htr, hc⟩

/-- The stroke vertices of a clipped shape are those of what it clips. -/
theorem strokeVertices_clipped (b : Rect) (s : Shape) : strokeVertices (.clipped b s) = strokeVertices s := rfl

theorem strokeVertices_strip (hw : Rat) (items : List (Item Pt)) :
    strokeVertices (.strip hw items) = stripVertices items := rfl

theorem strokeVertices_square (c : Pt) (r : Rat) :
    strokeVertices (.marker .square c r) = squareVertices c := rfl

theorem strokeVertices_circle (c : Pt) (r : Rat) :
    strokeVertices (.marker .circle c r) = discVertices r c := rfl

/-- A segment is the two triangles of the rectangle about it: four corners at its ends, each end twice or once, with no extension along it. -/
theorem segVertices_eq (a b : Pt) :
    segVertices a b = [⟨a, a.dir b, 0, -1⟩, ⟨b, a.dir b, 0, -1⟩, ⟨a, a.dir b, 0, 1⟩,
      ⟨b, a.dir b, 0, 1⟩, ⟨a, a.dir b, 0, 1⟩, ⟨b, a.dir b, 0, -1⟩] := rfl

theorem stripVertices_eq (items : List (Item Pt)) : stripVertices items = stripVerticesFrom none items := rfl

theorem stripVerticesFrom_nil (prev : Option Pt) : stripVerticesFrom prev [] = [] := rfl

theorem stripVerticesFrom_gap (prev : Option Pt) (rest : List (Item Pt)) :
    stripVerticesFrom prev (.gap :: rest) = stripVerticesFrom none rest := rfl

/-- A run of one value is an octagon. -/
theorem stripVerticesFrom_val_single (a : Pt) :
    stripVerticesFrom none [.val a] = octagonVertices a ⟨1, 0⟩ := by simp [stripVerticesFrom]

/-- The last value of a run of more than one has a cap ahead of the segment that arrives at it. -/
theorem stripVerticesFrom_val_last (d a : Pt) :
    stripVerticesFrom (some d) [.val a] = capVertices a d := by simp [stripVerticesFrom]

/-- The first value of a run followed by another has a cap behind the segment that leaves it, then that segment, then the rest. -/
theorem stripVerticesFrom_val_first (a b : Pt) (rest : List (Item Pt)) :
    stripVerticesFrom none (.val a :: .val b :: rest) =
      capVertices a ⟨-(a.dir b).x, -(a.dir b).y⟩ ++ segVertices a b ++
        stripVerticesFrom (some (a.dir b)) (.val b :: rest) := rfl

/-- A value between two has an octagon in the direction of the segment that leaves it, then that segment, then the rest. -/
theorem stripVerticesFrom_val_val (d a b : Pt) (rest : List (Item Pt)) :
    stripVerticesFrom (some d) (.val a :: .val b :: rest) =
      octagonVertices a (a.dir b) ++ segVertices a b ++ stripVerticesFrom (some (a.dir b)) (.val b :: rest) := rfl

end Inkproof.Gpu
