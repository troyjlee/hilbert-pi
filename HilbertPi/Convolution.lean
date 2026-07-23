/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.Sequence

/-!
# The convolution identity `∑_{i ≤ m} x i * x (m - i) = 1`

Paper Proposition 3, equivalently `∑ C(2i,i) C(2(m-i), m-i) = 4^m`, proved by
a discrete version of the generating-function argument: the ratio identity
`(i+1) x_{i+1} = (i+1/2) x_i` is the coefficient form of `(1-z) f' = f/2` for
`f = ∑ x_i z^i`, which forces `((1-z) f²)' = 0`; discretely this becomes
`S (m+1) = S m` for the convolution sums `S`, via symmetrizing the sum and
shifting the index.
-/

namespace HilbertPi

open Finset

/-- The convolution sum `S m = ∑_{i=0}^m x i * x (m - i)`. -/
noncomputable def S (m : ℕ) : ℝ := ∑ i ∈ range (m + 1), x i * x (m - i)

lemma S_zero : S 0 = 1 := by simp [S, x_zero]

/-- Symmetrization: `(m + 1) * S m = 2 * ∑_{i ≤ m} (i + 1/2) * x i * x (m - i)`. -/
lemma symm_sum (m : ℕ) :
    ((m : ℝ) + 1) * S m
      = 2 * ∑ i ∈ range (m + 1), ((i : ℝ) + 1 / 2) * (x i * x (m - i)) := by
  have hrefl :
      ∑ i ∈ range (m + 1), (((m - i : ℕ) : ℝ) + 1 / 2) * (x i * x (m - i))
        = ∑ i ∈ range (m + 1), ((i : ℝ) + 1 / 2) * (x i * x (m - i)) := by
    rw [← Finset.sum_range_reflect
      (fun i => ((i : ℝ) + 1 / 2) * (x i * x (m - i))) (m + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : m + 1 - 1 - i = m - i := by omega
    have h2 : m - (m - i) = i := Nat.sub_sub_self hi'
    rw [h1, h2]
    ring
  have key : ∀ i ∈ range (m + 1),
      ((m : ℝ) + 1) * (x i * x (m - i))
        = ((i : ℝ) + 1 / 2) * (x i * x (m - i))
          + (((m - i : ℕ) : ℝ) + 1 / 2) * (x i * x (m - i)) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hc : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := Nat.cast_sub hi'
    rw [hc]; ring
  calc ((m : ℝ) + 1) * S m
      = ∑ i ∈ range (m + 1), ((m : ℝ) + 1) * (x i * x (m - i)) := by
        rw [S, Finset.mul_sum]
    _ = ∑ i ∈ range (m + 1), (((i : ℝ) + 1 / 2) * (x i * x (m - i))
          + (((m - i : ℕ) : ℝ) + 1 / 2) * (x i * x (m - i))) :=
        Finset.sum_congr rfl key
    _ = ∑ i ∈ range (m + 1), ((i : ℝ) + 1 / 2) * (x i * x (m - i))
          + ∑ i ∈ range (m + 1), (((m - i : ℕ) : ℝ) + 1 / 2) * (x i * x (m - i)) :=
        Finset.sum_add_distrib
    _ = 2 * ∑ i ∈ range (m + 1), ((i : ℝ) + 1 / 2) * (x i * x (m - i)) := by
        rw [hrefl]; ring

/-- Index shift via the ratio identity:
`∑_{i ≤ m} (i + 1/2) x i x (m-i) = ∑_{j ≤ m+1} j x j x (m+1-j)`. -/
lemma shift_sum (m : ℕ) :
    ∑ i ∈ range (m + 1), ((i : ℝ) + 1 / 2) * (x i * x (m - i))
      = ∑ j ∈ range (m + 2), (j : ℝ) * (x j * x (m + 1 - j)) := by
  have step : ∀ i : ℕ, ((i : ℝ) + 1 / 2) * (x i * x (m - i))
      = (((i + 1 : ℕ) : ℝ)) * (x (i + 1) * x (m + 1 - (i + 1))) := by
    intro i
    have h := succ_mul_x_succ i
    have hidx : m + 1 - (i + 1) = m - i := by omega
    rw [hidx]
    push_cast
    calc ((i : ℝ) + 1 / 2) * (x i * x (m - i))
        = (((i : ℝ) + 1 / 2) * x i) * x (m - i) := by ring
      _ = (((i : ℝ) + 1) * x (i + 1)) * x (m - i) := by rw [← h]
      _ = ((i : ℝ) + 1) * (x (i + 1) * x (m - i)) := by ring
  rw [Finset.sum_range_succ' (fun j => (j : ℝ) * (x j * x (m + 1 - j))) (m + 1)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  exact Finset.sum_congr rfl fun i _ => step i

/-- The key identity: `S` is constant. -/
lemma S_succ (m : ℕ) : S (m + 1) = S m := by
  have hA := symm_sum m
  have hA' := symm_sum (m + 1)
  have hshift := shift_sum m
  have hsplit : ∑ j ∈ range (m + 2), ((j : ℝ) + 1 / 2) * (x j * x (m + 1 - j))
      = ∑ j ∈ range (m + 2), (j : ℝ) * (x j * x (m + 1 - j)) + (1 / 2) * S (m + 1) := by
    rw [S, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast, hsplit] at hA'
  -- hA' : ((m : ℝ) + 1 + 1) * S (m + 1) = 2 * (P + (1/2) * S (m+1))
  -- hA, hshift : ((m : ℝ) + 1) * S m = 2 * P
  have h2P : ((m : ℝ) + 1) * S (m + 1) = ((m : ℝ) + 1) * S m := by
    rw [hshift] at hA
    linarith [hA, hA']
  exact mul_left_cancel₀ (by positivity : ((m : ℝ) + 1) ≠ 0) h2P

/-- **The convolution identity** (paper Proposition 3):
`∑_{i=0}^m x i * x (m - i) = 1`. -/
theorem conv (m : ℕ) : ∑ i ∈ range (m + 1), x i * x (m - i) = 1 := by
  have h : S m = 1 := by
    induction m with
    | zero => exact S_zero
    | succ n ih => rw [S_succ]; exact ih
  simpa [S] using h

end HilbertPi
