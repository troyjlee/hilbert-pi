/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.Domination
import HilbertPi.SchurTest
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Hilbert's inequality: `‖H‖ ≤ π`

Assembles the pieces into the main results:

* `half_hilbert_bound` (paper Cor. 11): the bilinear form of the half-Hilbert
  matrix `T n` is bounded by `π ‖u‖ ‖v‖`;
* `hilbert_inequality_finite` (paper Cor. 12, Hilbert's inequality):
  `∑_{i,j<N} u i * v j / (i+j+1) ≤ π ‖u‖ ‖v‖`;
* `hilbert_summable`, `hilbert_inequality_l2`: the ℓ² version — for
  `f, g ∈ ℓ²(ℕ)` the double series converges absolutely and
  `|∑∑ f i * g j / (i+j+1)| ≤ π ‖f‖ ‖g‖`. This is the statement `‖H‖ ≤ π`
  for the Hilbert matrix `H[i,j] = 1/(i+j+1)` on `ℓ²`.
-/

namespace HilbertPi

open Finset Real
open scoped ENNReal

/-- **Half-Hilbert bilinear bound** (paper Corollary 11): `‖T n‖ ≤ π` as a
bilinear form. -/
theorem half_hilbert_bound (n : ℕ) (u v : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, T n i j * (u i * v j)
      ≤ π * Real.sqrt (∑ i ∈ range n, u i ^ 2)
          * Real.sqrt (∑ j ∈ range n, v j ^ 2) :=
  schur_test (T_symm n) (T_nonneg n) x_pos (T_row_bound n) u v

/-- **Hilbert's inequality** for finitely supported sequences
(paper Corollary 12). -/
theorem hilbert_inequality_finite (N : ℕ) (u v : ℕ → ℝ) :
    ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + 1)
      ≤ π * Real.sqrt (∑ i ∈ range N, u i ^ 2)
          * Real.sqrt (∑ j ∈ range N, v j ^ 2) := by
  classical
  set u' : ℕ → ℝ := fun i => if i < N then |u i| else 0 with hu'
  set v' : ℕ → ℝ := fun j => if j < N then |v j| else 0 with hv'
  have hNle : N ≤ 2 * N := by omega
  have step1 : ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + 1)
      ≤ ∑ i ∈ range N, ∑ j ∈ range N, |u i| * |v j| / ((i : ℝ) + (j : ℝ) + 1 / 2) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h1 : (0 : ℝ) < (i : ℝ) + (j : ℝ) + 1 / 2 := by positivity
    have h3 : u i * v j ≤ |u i| * |v j| := (le_abs_self _).trans (abs_mul _ _).le
    have h4 : (0 : ℝ) ≤ |u i| * |v j| := by positivity
    calc u i * v j / ((i : ℝ) + (j : ℝ) + 1)
        ≤ |u i| * |v j| / ((i : ℝ) + (j : ℝ) + 1) := by gcongr
      _ ≤ |u i| * |v j| / ((i : ℝ) + (j : ℝ) + 1 / 2) := by gcongr; linarith
  have step2 : ∑ i ∈ range N, ∑ j ∈ range N, |u i| * |v j| / ((i : ℝ) + (j : ℝ) + 1 / 2)
      = ∑ i ∈ range (2 * N), ∑ j ∈ range (2 * N), T (2 * N) i j * (u' i * v' j) := by
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
  calc ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + 1)
      ≤ ∑ i ∈ range N, ∑ j ∈ range N, |u i| * |v j| / ((i : ℝ) + (j : ℝ) + 1 / 2) :=
        step1
    _ = ∑ i ∈ range (2 * N), ∑ j ∈ range (2 * N), T (2 * N) i j * (u' i * v' j) :=
        step2
    _ ≤ π * Real.sqrt (∑ i ∈ range (2 * N), u' i ^ 2)
          * Real.sqrt (∑ j ∈ range (2 * N), v' j ^ 2) :=
        half_hilbert_bound (2 * N) u' v'
    _ = π * Real.sqrt (∑ i ∈ range N, u i ^ 2)
          * Real.sqrt (∑ j ∈ range N, v j ^ 2) := by rw [hnormu, hnormv]

section L2

/-- Finite sums of squares of an `ℓ²` element are bounded by the square of
its norm. -/
lemma sum_sq_le_norm_sq (f : lp (fun _ : ℕ => ℝ) 2) (s : Finset ℕ) :
    ∑ i ∈ s, (f i) ^ 2 ≤ ‖f‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by simp
  have h := lp.sum_rpow_le_norm_rpow hp f s
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by simp
  rw [h2] at h
  have hL : ∑ i ∈ s, ‖f i‖ ^ (2 : ℝ) = ∑ i ∈ s, (f i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  have hR : ‖f‖ ^ (2 : ℝ) = ‖f‖ ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hL, hR] at h
  exact h

/-- The square root of a finite sum of squares is at most the `ℓ²` norm. -/
lemma sqrt_sum_sq_le_norm (f : lp (fun _ : ℕ => ℝ) 2) (s : Finset ℕ) :
    Real.sqrt (∑ i ∈ s, (f i) ^ 2) ≤ ‖f‖ := by
  rw [show ‖f‖ = Real.sqrt (‖f‖ ^ 2) from (Real.sqrt_sq (norm_nonneg f)).symm]
  exact Real.sqrt_le_sqrt (sum_sq_le_norm_sq f s)

/-- Any finite partial sum of the absolute double series is at most
`π ‖f‖ ‖g‖`. -/
lemma partial_sum_bound (f g : lp (fun _ : ℕ => ℝ) 2) (s : Finset (ℕ × ℕ)) :
    ∑ q ∈ s, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1) ≤ π * ‖f‖ * ‖g‖ := by
  classical
  set N : ℕ := 1 + s.sup (fun q => max q.1 q.2) with hN
  have hsub : s ⊆ Finset.range N ×ˢ Finset.range N := by
    intro q hq
    have h1 : q.1 ≤ s.sup (fun q => max q.1 q.2) :=
      le_trans (le_max_left _ _) (Finset.le_sup (f := fun q => max q.1 q.2) hq)
    have h2 : q.2 ≤ s.sup (fun q => max q.1 q.2) :=
      le_trans (le_max_right _ _) (Finset.le_sup (f := fun q => max q.1 q.2) hq)
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have hmono : ∑ q ∈ s, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1)
      ≤ ∑ q ∈ Finset.range N ×ˢ Finset.range N,
          |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => ?_
    positivity
  have hprod : ∑ q ∈ Finset.range N ×ˢ Finset.range N,
        |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1)
      = ∑ i ∈ range N, ∑ j ∈ range N,
          |f i| * |g j| / ((i : ℝ) + (j : ℝ) + 1) := by
    rw [Finset.sum_product]
  have hfin := hilbert_inequality_finite N (fun i => |f i|) (fun j => |g j|)
  simp only [sq_abs] at hfin
  calc ∑ q ∈ s, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1)
      ≤ ∑ q ∈ Finset.range N ×ˢ Finset.range N,
          |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1) := hmono
    _ = ∑ i ∈ range N, ∑ j ∈ range N, |f i| * |g j| / ((i : ℝ) + (j : ℝ) + 1) := hprod
    _ ≤ π * Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
          * Real.sqrt (∑ j ∈ range N, (g j) ^ 2) := hfin
    _ ≤ π * ‖f‖ * ‖g‖ := by
        have h1 := sqrt_sum_sq_le_norm f (range N)
        have h2 := sqrt_sum_sq_le_norm g (range N)
        have hπ := Real.pi_pos
        have s2 := Real.sqrt_nonneg (∑ j ∈ range N, (g j) ^ 2)
        have hfg : Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
              * Real.sqrt (∑ j ∈ range N, (g j) ^ 2) ≤ ‖f‖ * ‖g‖ :=
          mul_le_mul h1 h2 s2 (norm_nonneg f)
        calc π * Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
              * Real.sqrt (∑ j ∈ range N, (g j) ^ 2)
            = π * (Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
                * Real.sqrt (∑ j ∈ range N, (g j) ^ 2)) := by ring
          _ ≤ π * (‖f‖ * ‖g‖) := mul_le_mul_of_nonneg_left hfg hπ.le
          _ = π * ‖f‖ * ‖g‖ := by ring

/-- The absolute double series is summable. -/
lemma hilbert_summable_abs (f g : lp (fun _ : ℕ => ℝ) 2) :
    Summable (fun q : ℕ × ℕ => |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1)) := by
  exact summable_of_sum_le (fun q => by positivity) (fun s => partial_sum_bound f g s)

/-- **Summability**: for `f, g ∈ ℓ²`, the Hilbert double series converges
absolutely. -/
theorem hilbert_summable (f g : lp (fun _ : ℕ => ℝ) 2) :
    Summable (fun q : ℕ × ℕ => f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)) := by
  rw [← summable_abs_iff]
  have heq : ∀ q : ℕ × ℕ, |f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)|
      = |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1) := by
    intro q
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + 1)]
  simp only [heq]
  exact hilbert_summable_abs f g

/-- **Hilbert's inequality on ℓ²** — the statement `‖H‖ ≤ π`:
for `f, g ∈ ℓ²(ℕ)`,
`|∑_{i,j} f i * g j / (i + j + 1)| ≤ π * ‖f‖ * ‖g‖`. -/
theorem hilbert_inequality_l2 (f g : lp (fun _ : ℕ => ℝ) 2) :
    |∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)| ≤ π * ‖f‖ * ‖g‖ := by
  have habs := hilbert_summable_abs f g
  have heq : ∀ q : ℕ × ℕ, |f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)|
      = |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1) := by
    intro q
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + 1)]
  have hnorm : Summable
      (fun q : ℕ × ℕ => ‖f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)‖) := by
    simpa only [Real.norm_eq_abs, heq] using habs
  calc |∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)|
      = ‖∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' q : ℕ × ℕ, ‖f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + 1)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ = ∑' q : ℕ × ℕ, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + 1) := by
        exact tsum_congr fun q => by rw [Real.norm_eq_abs, heq q]
    _ ≤ π * ‖f‖ * ‖g‖ :=
        Real.tsum_le_of_sum_le (fun q => by positivity)
          (fun s => partial_sum_bound f g s)

/-- Iterated form of the ℓ² Hilbert inequality. -/
theorem hilbert_inequality_l2' (f g : lp (fun _ : ℕ => ℝ) 2) :
    |∑' i : ℕ, ∑' j : ℕ, f i * g j / ((i : ℝ) + (j : ℝ) + 1)| ≤ π * ‖f‖ * ‖g‖ := by
  have h := hilbert_inequality_l2 f g
  rwa [Summable.tsum_prod' (hilbert_summable f g)
    ((hilbert_summable f g).prod_factor)] at h

end L2

end HilbertPi
