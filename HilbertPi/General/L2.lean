/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.Main
import HilbertPi.Main

/-!
# Schur's inequality on `ℓ²`: `‖H_λ‖ ≤ π csc(πλ)`

The finitely-supported bound `schur_inequality_finite` is lifted to arbitrary
`ℓ²` sequences by the same partial-sum argument used for `λ = 1/2` in
`HilbertPi/Main.lean`.  The lifting is carried out once, generically in the
constant `C` (`partial_sum_bound_of_finite`, `summable_of_finite_bound`,
`tsum_abs_le_of_finite_bound`), so that it can be reused at `C = π` for
`λ ≥ 1/2` in `HilbertPi/General/OpNorm.lean`.

Main results:

* `schur_summable` — for `0 < λ < 1` and `f, g ∈ ℓ²` the double series
  converges absolutely;
* `schur_inequality_l2`, `schur_inequality_l2'` — the `ℓ²` statement
  `|∑'_{i,j} f i * g j / (i+j+λ)| ≤ π csc(πλ) ‖f‖ ‖g‖`, i.e. `‖H_λ‖ ≤ π csc(πλ)`
  for the generalized Hilbert matrix `H_λ[i,j] = 1/(i+j+λ)` on `ℓ²`.
-/

namespace HilbertPi.General

open Finset Real
open scoped ENNReal

/-- The denominators `i + j + λ` are positive for `λ > 0`. -/
lemma denom_pos {l : ℝ} (hl0 : 0 < l) (i j : ℕ) : (0 : ℝ) < (i : ℝ) + (j : ℝ) + l := by
  have : (0 : ℝ) ≤ (i : ℝ) + (j : ℝ) := by positivity
  linarith

/-- `π csc(πλ) ≥ 0` for `0 < λ < 1`. -/
lemma theta_nonneg (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) :
    (0 : ℝ) ≤ π / Real.sin (π * l) :=
  (div_pos Real.pi_pos (sin_pi_mul_pos l hl0 hl1)).le

section Generic

variable {lam C : ℝ}

/-- The finitely-supported bilinear bound with constant `C`, in the form in
which `schur_inequality_finite` and `hilbert_le_pi_finite` both supply it. -/
def FiniteBound (lam C : ℝ) : Prop :=
  ∀ (N : ℕ) (u v : ℕ → ℝ),
    ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + lam)
      ≤ C * Real.sqrt (∑ i ∈ range N, u i ^ 2) * Real.sqrt (∑ j ∈ range N, v j ^ 2)

/-- Any finite partial sum of the absolute double series is at most `C ‖f‖ ‖g‖`. -/
lemma partial_sum_bound_of_finite (hlam : 0 < lam) (hC : 0 ≤ C) (hfin : FiniteBound lam C)
    (f g : lp (fun _ : ℕ => ℝ) 2) (s : Finset (ℕ × ℕ)) :
    ∑ q ∈ s, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam) ≤ C * ‖f‖ * ‖g‖ := by
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
  have hmono : ∑ q ∈ s, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam)
      ≤ ∑ q ∈ Finset.range N ×ˢ Finset.range N,
          |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => ?_
    exact div_nonneg (by positivity) (denom_pos hlam q.1 q.2).le
  have hprod : ∑ q ∈ Finset.range N ×ˢ Finset.range N,
        |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam)
      = ∑ i ∈ range N, ∑ j ∈ range N, |f i| * |g j| / ((i : ℝ) + (j : ℝ) + lam) := by
    rw [Finset.sum_product]
  have hbd := hfin N (fun i => |f i|) (fun j => |g j|)
  simp only [sq_abs] at hbd
  calc ∑ q ∈ s, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam)
      ≤ ∑ q ∈ Finset.range N ×ˢ Finset.range N,
          |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam) := hmono
    _ = ∑ i ∈ range N, ∑ j ∈ range N, |f i| * |g j| / ((i : ℝ) + (j : ℝ) + lam) := hprod
    _ ≤ C * Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
          * Real.sqrt (∑ j ∈ range N, (g j) ^ 2) := hbd
    _ ≤ C * ‖f‖ * ‖g‖ := by
        have h1 := HilbertPi.sqrt_sum_sq_le_norm f (range N)
        have h2 := HilbertPi.sqrt_sum_sq_le_norm g (range N)
        have s2 := Real.sqrt_nonneg (∑ j ∈ range N, (g j) ^ 2)
        have hfg : Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
              * Real.sqrt (∑ j ∈ range N, (g j) ^ 2) ≤ ‖f‖ * ‖g‖ :=
          mul_le_mul h1 h2 s2 (norm_nonneg f)
        calc C * Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
              * Real.sqrt (∑ j ∈ range N, (g j) ^ 2)
            = C * (Real.sqrt (∑ i ∈ range N, (f i) ^ 2)
                * Real.sqrt (∑ j ∈ range N, (g j) ^ 2)) := by ring
          _ ≤ C * (‖f‖ * ‖g‖) := mul_le_mul_of_nonneg_left hfg hC
          _ = C * ‖f‖ * ‖g‖ := by ring

/-- The absolute value of a term of the `λ`-series. -/
lemma abs_term (hlam : 0 < lam) (f g : lp (fun _ : ℕ => ℝ) 2) (q : ℕ × ℕ) :
    |f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)|
      = |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam) := by
  rw [abs_div, abs_mul, abs_of_pos (denom_pos hlam q.1 q.2)]

/-- The absolute double series is summable. -/
lemma summable_abs_of_finite_bound (hlam : 0 < lam) (hC : 0 ≤ C) (hfin : FiniteBound lam C)
    (f g : lp (fun _ : ℕ => ℝ) 2) :
    Summable (fun q : ℕ × ℕ => |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam)) :=
  summable_of_sum_le (fun q => div_nonneg (by positivity) (denom_pos hlam q.1 q.2).le)
    (fun s => partial_sum_bound_of_finite hlam hC hfin f g s)

/-- The double series converges absolutely. -/
lemma summable_of_finite_bound (hlam : 0 < lam) (hC : 0 ≤ C) (hfin : FiniteBound lam C)
    (f g : lp (fun _ : ℕ => ℝ) 2) :
    Summable (fun q : ℕ × ℕ => f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)) := by
  rw [← summable_abs_iff]
  simp only [abs_term hlam f g]
  exact summable_abs_of_finite_bound hlam hC hfin f g

/-- A finitely-supported bilinear bound with constant `C` lifts to `ℓ²`. -/
lemma tsum_abs_le_of_finite_bound (hlam : 0 < lam) (hC : 0 ≤ C) (hfin : FiniteBound lam C)
    (f g : lp (fun _ : ℕ => ℝ) 2) :
    |∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)| ≤ C * ‖f‖ * ‖g‖ := by
  have habs := summable_abs_of_finite_bound hlam hC hfin f g
  have hnorm : Summable
      (fun q : ℕ × ℕ => ‖f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)‖) := by
    simpa only [Real.norm_eq_abs, abs_term hlam f g] using habs
  calc |∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)|
      = ‖∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' q : ℕ × ℕ, ‖f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ = ∑' q : ℕ × ℕ, |f q.1| * |g q.2| / ((q.1 : ℝ) + (q.2 : ℝ) + lam) :=
        tsum_congr fun q => by rw [Real.norm_eq_abs, abs_term hlam f g q]
    _ ≤ C * ‖f‖ * ‖g‖ :=
        Real.tsum_le_of_sum_le
          (fun q => div_nonneg (by positivity) (denom_pos hlam q.1 q.2).le)
          (fun s => partial_sum_bound_of_finite hlam hC hfin f g s)

end Generic

section Schur

variable (l : ℝ)

/-- Schur's finitely-supported bound, packaged as a `FiniteBound`. -/
lemma finiteBound_schur (hl0 : 0 < l) (hl1 : l < 1) :
    FiniteBound l (π / Real.sin (π * l)) :=
  fun N u v => schur_inequality_finite l hl0 hl1 N u v

/-- **Summability**: for `f, g ∈ ℓ²` the generalized Hilbert double series
converges absolutely. -/
theorem schur_summable (hl0 : 0 < l) (hl1 : l < 1) (f g : lp (fun _ : ℕ => ℝ) 2) :
    Summable (fun q : ℕ × ℕ => f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l)) :=
  summable_of_finite_bound hl0 (theta_nonneg l hl0 hl1) (finiteBound_schur l hl0 hl1) f g

/-- **Schur's inequality on ℓ²** — the statement `‖H_λ‖ ≤ π csc(πλ)`: for
`f, g ∈ ℓ²(ℕ)` and `0 < λ < 1`,
`|∑_{i,j} f i * g j / (i + j + λ)| ≤ π csc(πλ) * ‖f‖ * ‖g‖`. -/
theorem schur_inequality_l2 (hl0 : 0 < l) (hl1 : l < 1) (f g : lp (fun _ : ℕ => ℝ) 2) :
    |∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l)|
      ≤ (π / Real.sin (π * l)) * ‖f‖ * ‖g‖ :=
  tsum_abs_le_of_finite_bound hl0 (theta_nonneg l hl0 hl1) (finiteBound_schur l hl0 hl1) f g

/-- Iterated form of the `ℓ²` Schur inequality. -/
theorem schur_inequality_l2' (hl0 : 0 < l) (hl1 : l < 1) (f g : lp (fun _ : ℕ => ℝ) 2) :
    |∑' i : ℕ, ∑' j : ℕ, f i * g j / ((i : ℝ) + (j : ℝ) + l)|
      ≤ (π / Real.sin (π * l)) * ‖f‖ * ‖g‖ := by
  have h := schur_inequality_l2 l hl0 hl1 f g
  rwa [Summable.tsum_prod' (schur_summable l hl0 hl1 f g)
    ((schur_summable l hl0 hl1 f g).prod_factor)] at h

end Schur

end HilbertPi.General
