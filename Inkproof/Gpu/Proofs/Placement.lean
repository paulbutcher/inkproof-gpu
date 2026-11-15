/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.Axioms
import Inkproof.Gpu.Shaders

namespace Inkproof.Gpu

open Inkproof.Float

/-- The Float32 evaluation of `x * s + c` can be bounded: the exact values of the three inputs are `b`, `a` and `d`, no intermediate result overflows or is subnormal, and in clip space the magnitude `|b * a| + |d|` times the viewport size `v` in pixels is at most `2 ^ 22`. Clip space spans two units across the viewport, so half a pixel is `1 / v`. `t` is the exact placement of the inputs. -/
def Placeable (v : Rat) (x s c : Float32) (t : Rat) : Prop :=
  ∃ b a d : Rat, Float32.toRat x = some b ∧ Float32.toRat s = some a ∧ Float32.toRat c = some d ∧
    t = b * a + d ∧ FloatFormat.binary32.NormalRange (b * a) ∧
    (∀ q, Float32.toRat (x * s) = some q → FloatFormat.binary32.NormalRange (q + d)) ∧
    ((b * a).abs + d.abs) * v ≤ 2 ^ 22

/-- A Float32 coordinate that is within half a pixel of `t`. -/
def Placed (v : Rat) (z : Float32) (t : Rat) : Prop :=
  ∃ q, Float32.toRat z = some q ∧ (q - t).abs ≤ 1 / v

theorem placed_mul_add (v : Rat) (hv : 0 < v) (x s c : Float32) (t : Rat)
    (h : Placeable v x s c t) : Placed v (x * s + c) t := by
  obtain ⟨b, a, d, hx, hs, hc, rfl, n1, n2, hm⟩ := h
  have hK : scaleTwoPow 1 24 = 16777216 := by
    rw [scaleTwoPow_of_nonneg 1 (by decide)]; decide +kernel
  obtain ⟨p, hp, e1⟩ := Float32.Approximates.error_step
    (Float32.approximates_mul hx hs n1) (e := 0) (s := b * a) (by rw [Rat.sub_self]; decide)
  obtain ⟨z, hz, e2⟩ := Float32.Approximates.error_step
    (Float32.approximates_add hp hc (n2 p hp)) (e := (b * a).abs / scaleTwoPow 1 24)
    (s := b * a + d) (by
      have : (p + d - (b * a + d)) = p - b * a := by grind
      rw [this, Rat.zero_add, Rat.add_zero] at *; exact e1)
  refine ⟨z, hz, ?_⟩
  have hS := rat_abs_add_le (b * a) d
  have hM : 0 ≤ (b * a).abs := Rat.abs_nonneg
  have hD : 0 ≤ d.abs := Rat.abs_nonneg
  have hMv : ((b * a).abs + d.abs) ≤ 2 ^ 22 * v⁻¹ := by
    have hi : 0 < v⁻¹ := Rat.inv_pos.mpr hv
    have hc : v * v⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
    have := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt hi)
    rw [Rat.mul_assoc, hc, Rat.mul_one] at this
    exact this
  rw [hK] at e2
  rw [Rat.div_def, Rat.one_mul]
  grind

/-- The vertex shader places each vertex within half a pixel of its exact position, for a viewport `v` pixels across, given the hypotheses of `Placeable` for each coordinate. -/
theorem vertexShader_placement (v : Rat) (hv : 0 < v) (env : String → Option (List Float32))
    (x y a b c d : Float32) (tx ty : Rat)
    (hp : env "a_position" = some [x, y]) (hs : env "u_slope" = some [a, b])
    (ho : env "u_offset" = some [c, d])
    (hx : Placeable v x a c tx) (hy : Placeable v y b d ty) :
    ∃ X Y : Float32, vertexShader.run env = some [("gl_Position", [X, Y, 0, 1])] ∧
      Placed v X tx ∧ Placed v Y ty :=
  ⟨x * a + c, y * b + d, vertexShader_run env x y a b c d hp hs ho,
    placed_mul_add v hv x a c tx hx, placed_mul_add v hv y b d ty hy⟩

end Inkproof.Gpu
