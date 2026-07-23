/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.Domination
import HilbertPi.SchurTest

/-!
# Schur's theorem: `‖T_{n,λ}‖ ≤ π csc(πλ)` (paper Section 4)

For `0 < λ < 1` the half-Hilbert matrix `T λ n` with entries `1/(i+j+λ)` has
bilinear form bounded by `(π / sin(πλ)) ‖u‖ ‖v‖`, at every finite size, and
the finitely-supported Schur inequality
`∑_{i,j<N} u_i v_j /(i+j+λ) ≤ π csc(πλ) ‖u‖ ‖v‖` follows by embedding.  Since
`π / sin(πλ) = π csc(πλ)`, this is Schur's sharpening of Hilbert's inequality.
-/

namespace HilbertPi.General

open Real Finset

/-- **Schur's bilinear bound** (paper Theorem, general `λ`): `‖T λ n‖ ≤ π csc(πλ)`. -/
theorem half_hilbert_bound_general (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (n : ℕ) (u v : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, T l n i j * (u i * v j)
      ≤ (π / Real.sin (π * l)) * Real.sqrt (∑ i ∈ range n, u i ^ 2)
          * Real.sqrt (∑ j ∈ range n, v j ^ 2) :=
  HilbertPi.schur_test (T_symm l n) (T_nonneg l hl0 n) (gx_pos l hl0)
    (T_row_bound l hl0 hl1 n) u v

/-- **Schur's inequality** for finitely supported sequences (paper Theorem 21). -/
theorem schur_inequality_finite (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (N : ℕ) (u v : ℕ → ℝ) :
    ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + l)
      ≤ (π / Real.sin (π * l)) * Real.sqrt (∑ i ∈ range N, u i ^ 2)
          * Real.sqrt (∑ j ∈ range N, v j ^ 2) := by
  classical
  set u' : ℕ → ℝ := fun i => if i < N then |u i| else 0 with hu'
  set v' : ℕ → ℝ := fun j => if j < N then |v j| else 0 with hv'
  have hNle : N ≤ 2 * N := by omega
  have step1 : ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + l)
      ≤ ∑ i ∈ range N, ∑ j ∈ range N, |u i| * |v j| / ((i : ℝ) + (j : ℝ) + l) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h1 : (0 : ℝ) < (i : ℝ) + (j : ℝ) + l := by
      have : (0 : ℝ) ≤ (i : ℝ) + (j : ℝ) := by positivity
      linarith
    have h3 : u i * v j ≤ |u i| * |v j| := (le_abs_self _).trans (abs_mul _ _).le
    gcongr
  have step2 : ∑ i ∈ range N, ∑ j ∈ range N, |u i| * |v j| / ((i : ℝ) + (j : ℝ) + l)
      = ∑ i ∈ range (2 * N), ∑ j ∈ range (2 * N), T l (2 * N) i j * (u' i * v' j) := by
    symm
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hNle)
        (fun i _ hi => Finset.sum_eq_zero fun j _ => by
          have : ¬ i < N := by simpa using hi
          simp only [hu', if_neg this]
          ring)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hNle)
        (fun j _ hj => by
          have : ¬ j < N := by simpa using hj
          simp only [hv', if_neg this]
          ring)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hiN : i < N := Finset.mem_range.mp hi
    have hjN : j < N := Finset.mem_range.mp hj
    simp only [hu', hv', if_pos hiN, if_pos hjN]
    unfold T
    rw [if_pos (by omega : i + j < 2 * N)]
    ring
  have hnormu : ∑ i ∈ range (2 * N), u' i ^ 2 = ∑ i ∈ range N, u i ^ 2 := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hNle)
        (fun i _ hi => by
          have : ¬ i < N := by simpa using hi
          simp only [hu', if_neg this]
          ring)]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hu', if_pos (Finset.mem_range.mp hi), sq_abs]
  have hnormv : ∑ j ∈ range (2 * N), v' j ^ 2 = ∑ j ∈ range N, v j ^ 2 := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hNle)
        (fun j _ hj => by
          have : ¬ j < N := by simpa using hj
          simp only [hv', if_neg this]
          ring)]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [hv', if_pos (Finset.mem_range.mp hj), sq_abs]
  calc ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + l)
      ≤ ∑ i ∈ range N, ∑ j ∈ range N, |u i| * |v j| / ((i : ℝ) + (j : ℝ) + l) := step1
    _ = ∑ i ∈ range (2 * N), ∑ j ∈ range (2 * N), T l (2 * N) i j * (u' i * v' j) := step2
    _ ≤ (π / Real.sin (π * l)) * Real.sqrt (∑ i ∈ range (2 * N), u' i ^ 2)
          * Real.sqrt (∑ j ∈ range (2 * N), v' j ^ 2) :=
        half_hilbert_bound_general l hl0 hl1 (2 * N) u' v'
    _ = (π / Real.sin (π * l)) * Real.sqrt (∑ i ∈ range N, u i ^ 2)
          * Real.sqrt (∑ j ∈ range N, v j ^ 2) := by rw [hnormu, hnormv]

end HilbertPi.General
