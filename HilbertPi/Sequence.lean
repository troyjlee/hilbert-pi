/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Data.Nat.Choose.Central

/-!
# The eigenvector sequence `x i = centralBinom i / 4 ^ i`

This file defines the sequence `x i = C(2i, i) / 4^i` and proves its basic
properties, culminating in the Wallis bound `1 / π ≤ (i + 1/2) * x i ^ 2`,
the only analytic input to the proof of Hilbert's inequality.
-/

namespace HilbertPi

open Real Finset

/-- The Perron eigenvector sequence: `x i = C(2i, i) / 4 ^ i`. -/
noncomputable def x (i : ℕ) : ℝ := (Nat.centralBinom i : ℝ) / 4 ^ i

lemma x_zero : x 0 = 1 := by simp [x, Nat.centralBinom]

lemma x_pos (i : ℕ) : 0 < x i :=
  div_pos (by exact_mod_cast i.centralBinom_pos) (by positivity)

lemma x_nonneg (i : ℕ) : 0 ≤ x i := (x_pos i).le

/-- The fundamental ratio identity, paper eq. (7):
`(i + 1) * x (i + 1) = (i + 1/2) * x i`. -/
lemma succ_mul_x_succ (i : ℕ) : ((i : ℝ) + 1) * x (i + 1) = ((i : ℝ) + 1 / 2) * x i := by
  have h : ((i : ℝ) + 1) * (Nat.centralBinom (i + 1) : ℝ)
      = 2 * (2 * (i : ℝ) + 1) * (Nat.centralBinom i : ℝ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.succ_mul_centralBinom_succ i)
  unfold x
  rw [pow_succ]
  have h4 : (4 : ℝ) ^ i ≠ 0 := by positivity
  field_simp
  linarith [h]

/-- `x (i + 1) = x i * ((2i + 1) / (2i + 2))`. -/
lemma x_succ (i : ℕ) : x (i + 1) = x i * ((2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2)) := by
  have h := succ_mul_x_succ i
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [h]

/-- `x i - x (i + 1) = x i / (2i + 2)`, used in the closed form of `M`. -/
lemma x_sub_x_succ (i : ℕ) : x i - x (i + 1) = x i / (2 * (i : ℝ) + 2) := by
  rw [x_succ i]
  have hi : (2 * (i : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The Wallis quantity `u m = (m + 1/2) * x m ^ 2`. -/
noncomputable def u (m : ℕ) : ℝ := ((m : ℝ) + 1 / 2) * x m ^ 2

lemma u_pos (m : ℕ) : 0 < u m := by
  have := x_pos m
  unfold u
  positivity

/-- `centralBinom m * m! * m! = (2m)!`. -/
lemma centralBinom_mul_factorial_sq (m : ℕ) :
    Nat.centralBinom m * m.factorial * m.factorial = (2 * m).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
  simpa [Nat.centralBinom, two_mul, Nat.add_sub_cancel] using h

open Real.Wallis in
/-- The bridge to Mathlib's Wallis product: `u m = 1 / (2 * W m)`. -/
lemma u_eq_inv_two_W (m : ℕ) : u m = 1 / (2 * W m) := by
  rw [W_eq_factorial_ratio]
  unfold u x
  have hcb : (Nat.centralBinom m : ℝ) * (m.factorial : ℝ) * (m.factorial : ℝ)
      = ((2 * m).factorial : ℝ) := by exact_mod_cast centralBinom_mul_factorial_sq m
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have hf2 : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast (2 * m).factorial_pos
  have h4 : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
  have h2 : ((2 : ℝ) ^ (4 * m)) = ((4 : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  have hcb2 : ((2 * m).factorial : ℝ) ^ 2
      = ((Nat.centralBinom m : ℝ) * (m.factorial : ℝ) ^ 2) ^ 2 := by
    rw [← hcb]; ring
  field_simp
  rw [h2, hcb2]
  ring

open Real.Wallis in
/-- The only analytic input: `1 / π ≤ u m`, from Mathlib's `Real.Wallis.W_le`. -/
lemma one_div_pi_le_u (m : ℕ) : 1 / π ≤ u m := by
  rw [u_eq_inv_two_W]
  have hW := W_le m
  have hWpos := W_pos m
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- One-step monotonicity of `u`. -/
lemma u_succ_le (m : ℕ) : u (m + 1) ≤ u m := by
  unfold u
  rw [x_succ m]
  have hsq := sq_nonneg (x m)
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd : (0 : ℝ) < (2 * (m : ℝ) + 2) ^ 2 := by positivity
  have key : (((m + 1 : ℕ) : ℝ) + 1 / 2) * ((2 * (m : ℝ) + 1) ^ 2 / (2 * (m : ℝ) + 2) ^ 2)
      ≤ (m : ℝ) + 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hd]
    push_cast
    nlinarith [hm]
  rw [mul_pow, div_pow]
  calc (((m + 1 : ℕ) : ℝ) + 1 / 2) * (x m ^ 2 * ((2 * (m : ℝ) + 1) ^ 2 / (2 * (m : ℝ) + 2) ^ 2))
      = ((((m + 1 : ℕ) : ℝ) + 1 / 2) * ((2 * (m : ℝ) + 1) ^ 2 / (2 * (m : ℝ) + 2) ^ 2))
          * x m ^ 2 := by ring
    _ ≤ ((m : ℝ) + 1 / 2) * x m ^ 2 := mul_le_mul_of_nonneg_right key hsq

lemma u_le_half (m : ℕ) : u m ≤ 1 / 2 := by
  have h0 : u 0 = 1 / 2 := by norm_num [u, x_zero]
  have h : ∀ k, u k ≤ u 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ n ih => exact (u_succ_le n).trans ih
  exact (h m).trans h0.le

/-- `x m ^ 2 ≤ 1 / (2 m + 1)`, used for the ℓ² tail bounds. -/
lemma x_sq_le (m : ℕ) : x m ^ 2 ≤ 1 / (2 * (m : ℝ) + 1) := by
  have h := u_le_half m
  unfold u at h
  rw [le_div_iff₀ (by positivity)]
  linarith

end HilbertPi
