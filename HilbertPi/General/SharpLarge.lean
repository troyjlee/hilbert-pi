/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.Sharp
import HilbertPi.Sequence

/-!
# Sharpness for `λ ≥ 1/2`: `‖H_λ‖ = π` (paper Theorem `sharp-large`)

For `λ ≥ 1/2` the norm is no longer attained, and the lower bound `‖H_λ‖ ≥ π`
is obtained by using the `ℓ²` eigenvectors `x(μ)` of the `μ < 1/2` case as test
vectors and letting `μ ↑ 1/2`.

This file builds the ingredients: monotonicity of `gx` in the parameter, the
identification of `gx (1/2)` with the central-binomial sequence of the warm-up,
and the convergent constant `D = ∑ gx(1/2)_i/(i+1/4)` used to bound the
perturbation error.
-/

namespace HilbertPi.General

open Real Finset Filter Topology

/-- `gx` is monotone in its parameter. -/
lemma gx_mono_param {μ ν : ℝ} (hμ : 0 < μ) (hμν : μ ≤ ν) (i : ℕ) :
    gx μ i ≤ gx ν i := by
  unfold gx
  refine Finset.prod_le_prod (fun t _ => ?_) (fun t _ => ?_)
  · positivity
  · have hc : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    rw [div_le_div_iff_of_pos_right hc]
    linarith

/-- At `λ = 1/2` the general sequence is the central-binomial sequence of the
warm-up. -/
lemma gx_half_eq (i : ℕ) : gx (1 / 2 : ℝ) i = HilbertPi.x i := by
  induction i with
  | zero => rw [gx_zero, HilbertPi.x_zero]
  | succ n ih =>
    rw [gx_succ, ih, HilbertPi.x_succ]
    congr 1
    field_simp

/-- `(gx(1/2) i)² ≤ 1/(2i+1)` (from the warm-up Wallis bound). -/
lemma gx_half_sq_le (i : ℕ) : (gx (1 / 2 : ℝ) i) ^ 2 ≤ 1 / (2 * (i : ℝ) + 1) := by
  rw [gx_half_eq]; exact HilbertPi.x_sq_le i

/-- `1/(π(i+1/2)) ≤ (gx(1/2) i)²` (from the warm-up Wallis bound). -/
lemma gx_half_sq_ge (i : ℕ) : 1 / (π * ((i : ℝ) + 1 / 2)) ≤ (gx (1 / 2 : ℝ) i) ^ 2 := by
  have hπ := Real.pi_pos
  have hu := HilbertPi.one_div_pi_le_u i
  simp only [HilbertPi.u] at hu
  rw [gx_half_eq, div_le_iff₀ (by positivity : (0 : ℝ) < π * ((i : ℝ) + 1 / 2))]
  have h2 := mul_le_mul_of_nonneg_left hu hπ.le
  rw [mul_one_div, div_self hπ.ne'] at h2
  nlinarith [h2]

/-- `gx(1/2) i ≤ 1/√(2i+1)`. -/
lemma gx_half_le_inv_sqrt (i : ℕ) : gx (1 / 2 : ℝ) i ≤ 1 / Real.sqrt (2 * (i : ℝ) + 1) := by
  have hpos : (0 : ℝ) < 2 * (i : ℝ) + 1 := by positivity
  have hsqrtpos := Real.sqrt_pos.mpr hpos
  have hg := (gx_pos (1 / 2 : ℝ) (by norm_num) i).le
  rw [le_div_iff₀ hsqrtpos]
  have h := gx_half_sq_le i
  rw [le_div_iff₀ hpos] at h
  nlinarith [h, hg, Real.sq_sqrt hpos.le, Real.sqrt_nonneg (2 * (i : ℝ) + 1)]

/-- The comparison bound `gx(1/2) i/(i+1/4) ≤ 4/(i+1)^{3/2}`. -/
lemma gx_half_div_le (i : ℕ) :
    gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4) ≤ 4 / ((i : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hsq1 : (0 : ℝ) < Real.sqrt ((i : ℝ) + 1) := Real.sqrt_pos.mpr hi1
  have hs1 : Real.sqrt ((i : ℝ) + 1) ≤ Real.sqrt (2 * (i : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hgle : gx (1 / 2 : ℝ) i ≤ 1 / Real.sqrt ((i : ℝ) + 1) :=
    (gx_half_le_inv_sqrt i).trans (one_div_le_one_div_of_le hsq1 hs1)
  have hden : 1 / ((i : ℝ) + 1 / 4) ≤ 1 / (((i : ℝ) + 1) / 4) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hrpow : ((i : ℝ) + 1) ^ (3 / 2 : ℝ) = ((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hi1, Real.rpow_one]
  rw [hrpow, div_eq_mul_one_div]
  calc gx (1 / 2 : ℝ) i * (1 / ((i : ℝ) + 1 / 4))
      ≤ (1 / Real.sqrt ((i : ℝ) + 1)) * (1 / (((i : ℝ) + 1) / 4)) :=
        mul_le_mul hgle hden (by positivity) (by positivity)
    _ = 4 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1)) := by
        rw [one_div_div]
        field_simp

/-- The constant `D = ∑ gx(1/2)_i/(i+1/4)` converges; it bounds the
perturbation error uniformly in `μ` and `λ`. -/
lemma D_summable : Summable (fun i : ℕ => gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4)) := by
  have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    summable_one_div_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hps.comp_injective (add_left_injective 1)
  have hbound : Summable (fun i : ℕ => 4 / ((i : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    simpa only [mul_one_div] using hshift.mul_left 4
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => gx_half_div_le i) hbound
  exact div_nonneg (gx_pos (1 / 2 : ℝ) (by norm_num) i).le (by positivity)

end HilbertPi.General
