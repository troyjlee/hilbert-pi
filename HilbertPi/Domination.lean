/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.EigenMatrix

/-!
# Entrywise domination: `T ≤ π • M` (paper Theorem 8)

`T n` is the half-Hilbert matrix, with entries `1/(i+j+1/2)` above the
anti-diagonal (`i + j < n`) and `0` below. We prove `T n i j ≤ π * M n i j`
entrywise, and deduce the row bound `∑ j < n, T n i j * x j ≤ π * x i`.

The proof avoids square roots entirely: both sides are nonnegative, and the
squared inequality is pure algebra in the Wallis quantities `u`, using only
`1/π ≤ u` (`one_div_pi_le_u`).
-/

namespace HilbertPi

open Real Finset

/-- The half-Hilbert matrix (paper eq. (2), with parameter `λ = 1/2`). -/
noncomputable def T (n i j : ℕ) : ℝ :=
  if i + j < n then 1 / ((i : ℝ) + (j : ℝ) + 1 / 2) else 0

lemma T_nonneg (n i j : ℕ) : 0 ≤ T n i j := by
  unfold T
  split
  · positivity
  · exact le_rfl

lemma T_symm (n i j : ℕ) : T n i j = T n j i := by
  unfold T
  rw [add_comm i j, add_comm (i : ℝ) (j : ℝ)]

/-- The squared closed form of `M` in terms of the Wallis quantities:
for `k = i + j < n`,
`(M n i j)^2 * ((k+1/2)^2 * (2(n-1-k)+1)) = u (n-1) * u (n-1-k) * (2n-1)`. -/
lemma M_sq_eq {n i j : ℕ} (h : i + j < n) :
    (M n i j) ^ 2 * ((((i : ℝ) + j) + 1 / 2) ^ 2 * (2 * (((n : ℝ) - 1) - ((i : ℝ) + j)) + 1))
      = u (n - 1) * u (n - 1 - (i + j)) * (2 * (n : ℝ) - 1) := by
  have hM := M_closed h
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hc2 : ((n - 1 - (i + j) : ℕ) : ℝ) = (n : ℝ) - 1 - ((i : ℝ) + j) := by
    rw [show n - 1 - (i + j) = n - (1 + (i + j)) by omega,
        Nat.cast_sub (by omega : 1 + (i + j) ≤ n)]
    push_cast
    ring
  rw [hM]
  unfold u
  rw [hc1, hc2]
  have hd : (2 * ((i : ℝ) + j) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **Entrywise domination** (paper Theorem 8): `T n i j ≤ π * M n i j`. -/
lemma T_le_pi_mul_M (n i j : ℕ) : T n i j ≤ π * M n i j := by
  rcases lt_or_ge (i + j) n with h | h
  · -- above the anti-diagonal
    have hM0 : 0 ≤ M n i j := M_nonneg n i j
    have hTval : T n i j = 1 / ((i : ℝ) + (j : ℝ) + 1 / 2) := by
      unfold T; rw [if_pos h]
    -- abbreviations
    set k : ℝ := (i : ℝ) + j with hk
    have hk0 : 0 ≤ k := by positivity
    have hkn : k + 1 ≤ (n : ℝ) := by
      have hn : i + j + 1 ≤ n := by omega
      rw [hk]
      exact_mod_cast hn
    -- lower bounds on the Wallis quantities
    have hu1 := one_div_pi_le_u (n - 1)
    have hu2 := one_div_pi_le_u (n - 1 - (i + j))
    have hπ := Real.pi_pos
    -- squared inequality: (π * M)^2 ≥ (1/(k+1/2))^2
    have hsq := M_sq_eq h
    have hden1 : (0 : ℝ) < k + 1 / 2 := by positivity
    have hden2 : (0 : ℝ) < 2 * (((n : ℝ) - 1) - k) + 1 := by linarith
    have h2n : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
    -- (π M)^2 (k+1/2)^2 ≥ 1, i.e. (π M (k+1/2))^2 ≥ 1, with π M (k+1/2) ≥ 0
    have hkey : 1 ≤ (π * M n i j * (k + 1 / 2)) ^ 2 := by
      have expand : (π * M n i j * (k + 1 / 2)) ^ 2
          = π ^ 2 * ((M n i j) ^ 2 * ((k + 1 / 2) ^ 2
              * (2 * (((n : ℝ) - 1) - k) + 1))) / (2 * (((n : ℝ) - 1) - k) + 1) := by
        field_simp
        try ring
      rw [expand, hsq, le_div_iff₀ hden2]
      have hfrac : 2 * (((n : ℝ) - 1) - k) + 1 ≤ 2 * (n : ℝ) - 1 := by linarith
      have hS : 1 ≤ π ^ 2 * (u (n - 1) * u (n - 1 - (i + j))) := by
        have ha : 1 ≤ u (n - 1) * π := (div_le_iff₀ hπ).mp hu1
        have hb : 1 ≤ u (n - 1 - (i + j)) * π := (div_le_iff₀ hπ).mp hu2
        nlinarith [mul_le_mul ha hb zero_le_one
          (by positivity : (0 : ℝ) ≤ u (n - 1) * π)]
      nlinarith [hS, hfrac, h2n, mul_nonneg (sub_nonneg.mpr hS) h2n.le]
    have hprod : 0 ≤ π * M n i j * (k + 1 / 2) := by positivity
    have : 1 ≤ π * M n i j * (k + 1 / 2) := by
      nlinarith [hkey, hprod]
    rw [hTval, div_le_iff₀ hden1]
    linarith
  · -- below the anti-diagonal: both sides are zero
    have hT : T n i j = 0 := by unfold T; rw [if_neg (by omega)]
    rw [hT, M_eq_zero h, mul_zero]

/-- **Row bound**: `∑ j < n, T n i j * x j ≤ π * x i`, for every `i`
(rows `i ≥ n` are identically zero). This is the input to the Schur test. -/
lemma T_row_bound (n i : ℕ) : ∑ j ∈ range n, T n i j * x j ≤ π * x i := by
  rcases lt_or_ge i n with hi | hi
  · calc ∑ j ∈ range n, T n i j * x j
        ≤ ∑ j ∈ range n, π * M n i j * x j := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (T_le_pi_mul_M n i j) (x_nonneg j)
      _ = π * ∑ j ∈ range n, M n i j * x j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = π * x i := by rw [eig n i hi]
  · have hz : ∀ j ∈ range n, T n i j * x j = 0 := by
      intro j hj
      have : ¬ i + j < n := by omega
      unfold T
      rw [if_neg this, zero_mul]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    have := x_pos i
    positivity

end HilbertPi
