/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.Sequence

/-!
# The convolution identity `∑_{i≤m} gx i * gy (m-i) = 1` (paper eq. (16))

Proved by the discrete form of the identity `((1-z) f h)' = 0` for
`f = (1-z)^{-l}`, `h = (1-z)^{l-1}`: the two ratio identities
`(i+1) gx_{i+1} = (i+l) gx_i` and `(i+1) gy_{i+1} = (i+1-l) gy_i`,
combined with a symmetrization, give `(m+1) C_{m+1} = (m+1) C_m`.
-/

namespace HilbertPi.General

open Finset

variable (l : ℝ)

/-- The (asymmetric) convolution sum. -/
noncomputable def C (m : ℕ) : ℝ := ∑ i ∈ range (m + 1), gx l i * gy l (m - i)

lemma C_zero : C l 0 = 1 := by simp [C, gx_zero, gy_zero]

/-- `A`-part after symmetrization: shifting the `gx` index by the ratio law. -/
lemma A_part (m : ℕ) :
    (∑ i ∈ range (m + 2), (i : ℝ) * (gx l i * gy l (m + 1 - i)))
      = ∑ i ∈ range (m + 1), ((i : ℝ) + l) * (gx l i * gy l (m - i)) := by
  rw [Finset.sum_range_succ' (fun i => (i : ℝ) * (gx l i * gy l (m + 1 - i))) (m + 1)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hidx : m + 1 - (i + 1) = m - i := by omega
  rw [hidx]
  have hr := succ_mul_gx_succ l i
  push_cast
  calc ((i : ℝ) + 1) * (gx l (i + 1) * gy l (m - i))
      = (((i : ℝ) + 1) * gx l (i + 1)) * gy l (m - i) := by ring
    _ = (((i : ℝ) + l) * gx l i) * gy l (m - i) := by rw [hr]
    _ = ((i : ℝ) + l) * (gx l i * gy l (m - i)) := by ring

/-- `B`-part after symmetrization: two reflections and the `gy` ratio law. -/
lemma B_part (m : ℕ) :
    (∑ i ∈ range (m + 2), ((m + 1 - i : ℕ) : ℝ) * (gx l i * gy l (m + 1 - i)))
      = ∑ i ∈ range (m + 1), (((m - i : ℕ) : ℝ) + 1 - l) * (gx l i * gy l (m - i)) := by
  -- first reflection: put the counting weight on gy
  have hB1 : (∑ i ∈ range (m + 2), ((m + 1 - i : ℕ) : ℝ) * (gx l i * gy l (m + 1 - i)))
      = ∑ j ∈ range (m + 2), (j : ℝ) * (gx l (m + 1 - j) * gy l j) := by
    rw [← Finset.sum_range_reflect (fun j => (j : ℝ) * (gx l (m + 1 - j) * gy l j)) (m + 2)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m + 2 := Finset.mem_range.mp hi
    have h1 : m + 2 - 1 - i = m + 1 - i := by omega
    have h2 : m + 1 - (m + 1 - i) = i := by omega
    rw [h1, h2]
  -- peel the zero term and apply the gy ratio
  have hB2 : (∑ j ∈ range (m + 2), (j : ℝ) * (gx l (m + 1 - j) * gy l j))
      = ∑ j ∈ range (m + 1), (((j : ℝ) + 1 - l) * (gx l (m - j) * gy l j)) := by
    rw [Finset.sum_range_succ' (fun j => (j : ℝ) * (gx l (m + 1 - j) * gy l j)) (m + 1)]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hidx : m + 1 - (j + 1) = m - j := by omega
    rw [hidx]
    have hr := succ_mul_gy_succ l j
    push_cast
    calc ((j : ℝ) + 1) * (gx l (m - j) * gy l (j + 1))
        = gx l (m - j) * (((j : ℝ) + 1) * gy l (j + 1)) := by ring
      _ = gx l (m - j) * (((j : ℝ) + 1 - l) * gy l j) := by rw [hr]
      _ = ((j : ℝ) + 1 - l) * (gx l (m - j) * gy l j) := by ring
  -- second reflection: put gx back on index i
  have hB3 : (∑ j ∈ range (m + 1), (((j : ℝ) + 1 - l) * (gx l (m - j) * gy l j)))
      = ∑ i ∈ range (m + 1), (((m - i : ℕ) : ℝ) + 1 - l) * (gx l i * gy l (m - i)) := by
    rw [← Finset.sum_range_reflect
      (fun i => (((m - i : ℕ) : ℝ) + 1 - l) * (gx l i * gy l (m - i))) (m + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m + 1 := Finset.mem_range.mp hj
    have h1 : m + 1 - 1 - j = m - j := by omega
    have h2 : m - (m - j) = j := by omega
    rw [h1, h2]
  rw [hB1, hB2, hB3]

/-- The key recurrence: `C` is constant. -/
lemma C_succ (m : ℕ) : C l (m + 1) = C l m := by
  have hkey : ((m : ℝ) + 1) * C l (m + 1) = ((m : ℝ) + 1) * C l m := by
    have expand : ((m : ℝ) + 1) * C l (m + 1)
        = (∑ i ∈ range (m + 2), (i : ℝ) * (gx l i * gy l (m + 1 - i)))
          + ∑ i ∈ range (m + 2), ((m + 1 - i : ℕ) : ℝ) * (gx l i * gy l (m + 1 - i)) := by
      rw [C, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < m + 2 := Finset.mem_range.mp hi
      have hcast : ((m + 1 - i : ℕ) : ℝ) = (m : ℝ) + 1 - (i : ℝ) := by
        rw [Nat.cast_sub (by omega : i ≤ m + 1)]; push_cast; ring
      rw [show (m + 1) - i = m + 1 - i from rfl]  -- align nat expr
      rw [hcast]; ring
    rw [expand, A_part, B_part, ← Finset.sum_add_distrib, C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    have hcast : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub (by omega : i ≤ m)]
    rw [hcast]; ring
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  exact mul_left_cancel₀ hm hkey

/-- **The convolution identity** (paper eq. (16)):
`∑_{i≤m} gx i * gy (m-i) = 1`. -/
theorem conv (m : ℕ) : ∑ i ∈ range (m + 1), gx l i * gy l (m - i) = 1 := by
  have h : C l m = 1 := by
    induction m with
    | zero => exact C_zero l
    | succ n ih => rw [C_succ]; exact ih
  simpa [C] using h

end HilbertPi.General
