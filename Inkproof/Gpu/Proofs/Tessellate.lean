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

theorem octagonTriangles_length (c : Pt) (r : Rat) : (octagonTriangles c r).length = 8 := rfl

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

/-- The shapes whose triangles are known to cover them: all but circles, which the octagon covers but without a proof, and strips of no width, which Scene's triangles do not cover. -/
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
      (fun _ _ _ h => span_sub_spanTriangles h) items p h
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

end Inkproof.Gpu
