/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt

/-!
# The finite Schur test (paper Lemma 2, inequality half)

If `B` is a symmetric matrix with nonnegative entries and `p` is a positive
vector with `∑ j < n, B i j * p j ≤ θ * p i` for all `i`, then the bilinear
form of `B` is bounded: `∑∑ B i j * u i * v j ≤ θ * ‖u‖ * ‖v‖`.

Stated for plain functions `ℕ → ℝ` with `Finset.range` sums and `Real.sqrt`
norms; no matrix or operator API is involved.
-/

namespace HilbertPi

open Finset Real

section SchurTest

variable {n : ℕ} {B : ℕ → ℕ → ℝ} {p : ℕ → ℝ} {θ : ℝ}

/-- Weighted AM–GM: `|u| * |v| ≤ (1/2) * ((q/r) * u² + (r/q) * v²)` for
positive weights `q, r`. -/
lemma abs_mul_abs_le_weighted {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (a b : ℝ) :
    |a| * |b| ≤ (1 / 2) * ((q / r) * a ^ 2 + (r / q) * b ^ 2) := by
  rw [← sub_nonneg]
  have key : (1 / 2) * ((q / r) * a ^ 2 + (r / q) * b ^ 2) - |a| * |b|
      = (q * |a| - r * |b|) ^ 2 / (2 * (q * r)) := by
    have ha : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    have hb : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
    rw [ha, hb]
    field_simp
    ring
  rw [key]
  positivity

/-- Quadratic-form version of the Schur test:
`∑∑ B i j u i v j ≤ (θ/2) * (∑ u² + ∑ v²)`. -/
lemma schur_test_quadratic
    (hsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, 0 ≤ B i j)
    (hp : ∀ i, 0 < p i)
    (hrow : ∀ i, ∑ j ∈ range n, B i j * p j ≤ θ * p i)
    (u v : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, B i j * (u i * v j)
      ≤ θ / 2 * ((∑ i ∈ range n, u i ^ 2) + ∑ j ∈ range n, v j ^ 2) := by
  have hS1 : ∑ i ∈ range n, ∑ j ∈ range n, B i j * ((p j / p i) * u i ^ 2)
      ≤ θ * ∑ i ∈ range n, u i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpi := hp i
    have heq : ∑ j ∈ range n, B i j * ((p j / p i) * u i ^ 2)
        = (u i ^ 2 / p i) * ∑ j ∈ range n, B i j * p j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [heq]
    calc (u i ^ 2 / p i) * ∑ j ∈ range n, B i j * p j
        ≤ (u i ^ 2 / p i) * (θ * p i) :=
          mul_le_mul_of_nonneg_left (hrow i) (by positivity)
      _ = θ * u i ^ 2 := by field_simp
  have hS2 : ∑ i ∈ range n, ∑ j ∈ range n, B i j * ((p i / p j) * v j ^ 2)
      ≤ θ * ∑ j ∈ range n, v j ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hpj := hp j
    have heq : ∑ i ∈ range n, B i j * ((p i / p j) * v j ^ 2)
        = (v j ^ 2 / p j) * ∑ i ∈ range n, B j i * p i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsymm i j]
      field_simp
    rw [heq]
    calc (v j ^ 2 / p j) * ∑ i ∈ range n, B j i * p i
        ≤ (v j ^ 2 / p j) * (θ * p j) :=
          mul_le_mul_of_nonneg_left (hrow j) (by positivity)
      _ = θ * v j ^ 2 := by field_simp
  calc ∑ i ∈ range n, ∑ j ∈ range n, B i j * (u i * v j)
      ≤ ∑ i ∈ range n, ∑ j ∈ range n, B i j * (|u i| * |v j|) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hB i j)
        calc u i * v j ≤ |u i * v j| := le_abs_self _
          _ = |u i| * |v j| := abs_mul _ _
    _ ≤ ∑ i ∈ range n, ∑ j ∈ range n,
          ((1 / 2) * (B i j * ((p j / p i) * u i ^ 2))
            + (1 / 2) * (B i j * ((p i / p j) * v j ^ 2))) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        calc B i j * (|u i| * |v j|)
            ≤ B i j * ((1 / 2) * ((p j / p i) * u i ^ 2 + (p i / p j) * v j ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (abs_mul_abs_le_weighted (hp j) (hp i) (u i) (v j)) (hB i j)
          _ = (1 / 2) * (B i j * ((p j / p i) * u i ^ 2))
                + (1 / 2) * (B i j * ((p i / p j) * v j ^ 2)) := by ring
    _ = (1 / 2) * (∑ i ∈ range n, ∑ j ∈ range n, B i j * ((p j / p i) * u i ^ 2))
          + (1 / 2) * (∑ i ∈ range n, ∑ j ∈ range n, B i j * ((p i / p j) * v j ^ 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ (1 / 2) * (θ * ∑ i ∈ range n, u i ^ 2)
          + (1 / 2) * (θ * ∑ j ∈ range n, v j ^ 2) := by
        have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
        exact add_le_add (mul_le_mul_of_nonneg_left hS1 h12)
          (mul_le_mul_of_nonneg_left hS2 h12)
    _ = θ / 2 * ((∑ i ∈ range n, u i ^ 2) + ∑ j ∈ range n, v j ^ 2) := by ring

/-- **The finite Schur test** (paper Lemma 2): bilinear-form bound with the
product of norms. -/
theorem schur_test
    (hsymm : ∀ i j, B i j = B j i)
    (hB : ∀ i j, 0 ≤ B i j)
    (hp : ∀ i, 0 < p i)
    (hrow : ∀ i, ∑ j ∈ range n, B i j * p j ≤ θ * p i)
    (u v : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, B i j * (u i * v j)
      ≤ θ * Real.sqrt (∑ i ∈ range n, u i ^ 2)
          * Real.sqrt (∑ j ∈ range n, v j ^ 2) := by
  set a := Real.sqrt (∑ i ∈ range n, u i ^ 2) with ha
  set b := Real.sqrt (∑ j ∈ range n, v j ^ 2) with hb
  have hu2 : a ^ 2 = ∑ i ∈ range n, u i ^ 2 := by
    rw [ha]; exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (u i))
  have hv2 : b ^ 2 = ∑ j ∈ range n, v j ^ 2 := by
    rw [hb]; exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (v j))
  -- degenerate cases: one of the vectors vanishes on `range n`
  have ha0 : 0 ≤ a := ha ▸ Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := hb ▸ Real.sqrt_nonneg _
  rcases eq_or_lt_of_le ha0 with hA | hA
  · have hsum0 : ∑ i ∈ range n, u i ^ 2 = 0 := by rw [← hu2, ← hA]; norm_num
    have hu0 : ∀ i ∈ range n, u i = 0 := by
      intro i hi
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (u i))).mp hsum0 i hi
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h
    have hz : ∑ i ∈ range n, ∑ j ∈ range n, B i j * (u i * v j) = 0 :=
      Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ => by
        rw [hu0 i hi]; ring
    rw [hz, ← hA]
    simp
  rcases eq_or_lt_of_le hb0 with hB' | hB'
  · have hsum0 : ∑ j ∈ range n, v j ^ 2 = 0 := by rw [← hv2, ← hB']; norm_num
    have hv0 : ∀ j ∈ range n, v j = 0 := by
      intro j hj
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (v j))).mp hsum0 j hj
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h
    have hz : ∑ i ∈ range n, ∑ j ∈ range n, B i j * (u i * v j) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => by
        rw [hv0 j hj]; ring
    rw [hz, ← hB']
    simp
  -- main case: normalize and apply the quadratic version
  have hq := schur_test_quadratic hsymm hB hp hrow
    (fun i => u i / a) (fun j => v j / b)
  have hlhs : ∑ i ∈ range n, ∑ j ∈ range n, B i j * ((u i / a) * (v j / b))
      = (∑ i ∈ range n, ∑ j ∈ range n, B i j * (u i * v j)) / (a * b) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hA.ne', hB'.ne']
  have hsc1 : ∑ i ∈ range n, (u i / a) ^ 2 = 1 := by
    have : ∀ i ∈ range n, (u i / a) ^ 2 = u i ^ 2 / a ^ 2 := fun i _ => div_pow _ _ _
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← hu2]
    exact div_self (pow_ne_zero 2 hA.ne')
  have hsc2 : ∑ j ∈ range n, (v j / b) ^ 2 = 1 := by
    have : ∀ j ∈ range n, (v j / b) ^ 2 = v j ^ 2 / b ^ 2 := fun j _ => div_pow _ _ _
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← hv2]
    exact div_self (pow_ne_zero 2 hB'.ne')
  rw [hlhs, hsc1, hsc2] at hq
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < a * b)] at hq
  calc ∑ i ∈ range n, ∑ j ∈ range n, B i j * (u i * v j)
      ≤ θ / 2 * (1 + 1) * (a * b) := hq
    _ = θ * a * b := by ring

end SchurTest

end HilbertPi
