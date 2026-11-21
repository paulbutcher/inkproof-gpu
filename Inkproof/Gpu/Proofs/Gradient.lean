/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Gradient

namespace Inkproof.Gpu

open Scene

/-- A fraction clamped to 0 to 1, as the fragment shader's `clamp` does. -/
def clamp01 (x : Rat) : Rat := if x ≤ 0 then 0 else if 1 ≤ x then 1 else x

/-- What one channel of the stops adds to the first stop's, in exact arithmetic as the fragment shader does: each segment adds the change in the channel across it, scaled by how far `t` is along it, clamped to 0 to 1. -/
def deltaSum (f : Color → UInt8) (t : Rat) : Stop → List Stop → Rat
  | _, [] => 0
  | s, n :: rest =>
    (((f n.color).toNat : Rat) - (f s.color).toNat) * clamp01 ((t - s.pos) / (n.pos - s.pos)) +
      deltaSum f t n rest

private theorem lerpChannel_close (a b : UInt8) {w : Rat} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    (lerpChannel a b w).toNat - ((a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w) ≤ 1 / 2 ∧
    -(1 / 2) ≤ (lerpChannel a b w).toNat - ((a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w) := by
  rw [lerpChannel_toNat a b h0 h1]
  obtain ⟨x, hx⟩ : ∃ x : Rat, x = (a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w + 1 / 2 := ⟨_, rfl⟩
  rw [← hx]
  have ha : (a.toNat : Rat) ≤ 255 := by have := a.toNat_lt; exact_mod_cast (by omega : a.toNat ≤ 255)
  have a0 : (0 : Rat) ≤ a.toNat := by exact_mod_cast Nat.zero_le _
  have b0 : (0 : Rat) ≤ b.toNat := by exact_mod_cast Nat.zero_le _
  have p1 : 0 ≤ (a.toNat : Rat) * (1 - w) := Rat.mul_nonneg a0 (by grind)
  have p2 : 0 ≤ (b.toNat : Rat) * w := Rat.mul_nonneg b0 h0
  have e : (a.toNat : Rat) + ((b.toNat : Rat) - a.toNat) * w =
      (a.toNat : Rat) * (1 - w) + (b.toNat : Rat) * w := by grind
  have hnn : (0 : Int) ≤ x.floor := Rat.le_floor_iff.2 (by grind)
  have hl : ((x.floor : Int) : Rat) ≤ x := Rat.le_floor_iff.1 (Int.le_refl _)
  have hu : x < ((x.floor : Int) : Rat) + 1 := by
    have : x < (((x.floor + 1 : Int)) : Rat) := Rat.floor_lt_iff.1 (by omega)
    exact_mod_cast this
  have hc : (((x.floor).toNat : Nat) : Rat) = ((x.floor : Int) : Rat) := by
    have : ((x.floor.toNat : Nat) : Int) = x.floor := Int.toNat_of_nonneg hnn
    exact_mod_cast this
  rw [hc]
  constructor <;> grind

private theorem div_le_of_le (x d y : Rat) (hd : 0 < d) (h : x ≤ y * d) : x / d ≤ y := by
  have hi : 0 < d⁻¹ := Rat.inv_pos.mpr hd
  have hc : d * d⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hi)
  rw [Rat.mul_assoc, hc, Rat.mul_one] at this
  rw [Rat.div_def]; exact this

private theorem le_div_of_le (x d y : Rat) (hd : 0 < d) (h : y * d ≤ x) : y ≤ x / d := by
  have hi : 0 < d⁻¹ := Rat.inv_pos.mpr hd
  have hc : d * d⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hi)
  rw [Rat.mul_assoc, hc, Rat.mul_one] at this
  rw [Rat.div_def]; exact this

/-- Before the start of a segment the clamped fraction is 0, and after its end it is 1. -/
private theorem clamp01_before (x d : Rat) (hd : 0 < d) (h : x ≤ 0) : clamp01 (x / d) = 0 := by
  have : x / d ≤ 0 := div_le_of_le x d 0 hd (by grind)
  simp [clamp01, this]

private theorem clamp01_after (x d : Rat) (hd : 0 < d) (h : d ≤ x) : clamp01 (x / d) = 1 := by
  have : 1 ≤ x / d := le_div_of_le x d 1 hd (by grind)
  have h0 : ¬ x / d ≤ 0 := by grind
  simp [clamp01, h0, this]

private theorem clamp01_between (x d : Rat) (hd : 0 < d) (h0 : 0 < x) (h1 : x ≤ d) :
    clamp01 (x / d) = x / d ∧ 0 ≤ x / d ∧ x / d ≤ 1 := by
  have a : x / d ≤ 1 := div_le_of_le x d 1 hd (by grind)
  have b : 0 ≤ x / d := le_div_of_le x d 0 hd (by grind)
  have c : 0 < x / d := by
    rw [Rat.div_def]; exact Rat.mul_pos h0 (Rat.inv_pos.mpr hd)
  have n1 : ¬ x / d ≤ 0 := by grind
  refine ⟨?_, b, a⟩
  by_cases e : 1 ≤ x / d
  · simp only [clamp01, n1, e, ite_false, ite_true]; grind
  · simp [clamp01, n1, e]

private theorem deltaSum_before (f : Color → UInt8) (t : Rat) :
    ∀ (rest : List Stop) (s : Stop), (s :: rest).Pairwise (·.pos < ·.pos) → t ≤ s.pos →
      deltaSum f t s rest = 0 := by
  intro rest
  induction rest with
  | nil => intro s _ _; rfl
  | cons n rest ih =>
    intro s hs ht
    have hsn : s.pos < n.pos := (List.pairwise_cons.1 hs).1 n (by simp)
    have hr := (List.pairwise_cons.1 hs).2
    have h1 : clamp01 ((t - s.pos) / (n.pos - s.pos)) = 0 :=
      clamp01_before _ _ (by grind) (by grind)
    simp only [deltaSum, h1, Rat.mul_zero, Rat.zero_add]
    exact ih n hr (by grind)

/-- In exact arithmetic the fragment shader's blend of a channel, the first stop's value plus `deltaSum`, is within half a unit of what Scene gives the pixel, which rounds each blend to a whole number. -/
theorem evalStops_close (f : Color → UInt8)
    (hf : ∀ a b w, f (a.lerp b w) = lerpChannel (f a) (f b) w) :
    ∀ (rest : List Stop) (s : Stop), (s :: rest).Pairwise (·.pos < ·.pos) → ∀ t : Rat,
      ((f (evalStops s rest t)).toNat : Rat) - ((f s.color).toNat + deltaSum f t s rest) ≤ 1 / 2 ∧
      -(1 / 2) ≤ ((f (evalStops s rest t)).toNat : Rat) - ((f s.color).toNat + deltaSum f t s rest) := by
  intro rest
  induction rest with
  | nil => intro s _ t; simp only [evalStops, deltaSum]; grind
  | cons n rest ih =>
    intro s hs t
    have hsn : s.pos < n.pos := (List.pairwise_cons.1 hs).1 n (by simp)
    have hr := (List.pairwise_cons.1 hs).2
    by_cases h0 : t ≤ s.pos
    · have h1 : clamp01 ((t - s.pos) / (n.pos - s.pos)) = 0 :=
        clamp01_before _ _ (by grind) (by grind)
      have h2 := deltaSum_before f t rest n hr (by grind)
      simp only [evalStops, h0, ite_true, deltaSum, h1, h2, Rat.mul_zero]; grind
    · by_cases h1 : t ≤ n.pos
      · obtain ⟨hc, hw0, hw1⟩ := clamp01_between (t - s.pos) (n.pos - s.pos) (by grind) (by grind) (by grind)
        have h2 := deltaSum_before f t rest n hr h1
        have h3 := lerpChannel_close (f s.color) (f n.color) hw0 hw1
        simp only [evalStops, h0, h1, ite_false, ite_true, hf, deltaSum, hc, h2, Rat.add_zero]
        exact h3
      · have h2 : clamp01 ((t - s.pos) / (n.pos - s.pos)) = 1 :=
          clamp01_after _ _ (by grind) (by grind)
        have := ih n hr t
        simp only [evalStops, h0, h1, ite_false, deltaSum, h2, Rat.mul_one]
        grind

theorem gradientSegments_eq : gradientSegments = 4 := rfl

theorem stepInv_eq : stepInv = (ratToFloat32 (10 ^ 30)).toBits := rfl

theorem deltaWords_eq (a b : Color) :
    deltaWords a b = [(a.r, b.r), (a.g, b.g), (a.b, b.b), (a.a, b.a)].map fun (x, y) =>
      (ratToFloat32 (((y.toNat : Int) - x.toNat : Int) / 255)).toBits := rfl

theorem stopsAscend_cons_cons (a b : Stop) (rest : List Stop) :
    stopsAscend (a :: b :: rest) = (decide (a.pos ≤ b.pos) && stopsAscend (b :: rest)) := rfl

/-- Stops in strictly ascending order are ascending. -/
theorem stopsAscend_of_pairwise : ∀ l : List Stop, l.Pairwise (·.pos < ·.pos) → stopsAscend l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    have h1 := List.pairwise_cons.1 h
    have hab : a.pos < b.pos := h1.1 b (by simp)
    have := stopsAscend_of_pairwise (b :: rest) h1.2
    simp [stopsAscend, this, Rat.le_of_lt hab]

/-- The gradient along `x` has the unit vector of `x` as its axis, and along `y` that of `y`. -/
theorem Gradient.ofStops_axis (o : Pt) (a : GradientAxis) (s : Stop) (rest : List Stop) :
    (Gradient.ofStops o a s rest).axis =
      match a with | .x => [(1 : Float32).toBits, 0] | .y => [0, (1 : Float32).toBits] := by
  cases a <;> rfl

/-- The first segment starts at the first stop's position relative to the tile origin, has the reciprocal of its length, and changes the colour by the difference between its stops. -/
theorem Gradient.ofStops_first (o : Pt) (s n : Stop) (rest : List Stop) :
    ((Gradient.ofStops o .x s (n :: rest)).starts.head? = some (ratToFloat32 (s.pos - o.x)).toBits) ∧
    ((Gradient.ofStops o .x s (n :: rest)).invs.head? =
      some (if s.pos = n.pos then stepInv else (ratToFloat32 (1 / (n.pos - s.pos))).toBits)) ∧
    (Gradient.ofStops o .x s (n :: rest)).d0 = deltaWords s.color n.color := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Gradient.ofStops]

/-- The first step starts just before the second stop's position relative to the tile origin, has no length, and changes the colour by the difference between the first two stops. -/
theorem Gradient.ofSteps_first (o : Pt) (s n : Stop) (rest : List Stop) :
    ((Gradient.ofSteps o .x s (n :: rest)).starts.head? =
      some (ratToFloat32 (n.pos - o.x - stepLead)).toBits) ∧
    ((Gradient.ofSteps o .x s (n :: rest)).invs.head? = some stepInv) ∧
    (Gradient.ofSteps o .x s (n :: rest)).d0 = deltaWords s.color n.color := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Gradient.ofSteps]

end Inkproof.Gpu
