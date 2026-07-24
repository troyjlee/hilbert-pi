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

/-- The separating denominator estimate `(i+¼)(j+¼) ≤ (i+j+μ)(i+j+λ)` for
`μ, λ ≥ 1/4` (paper: `i+j+¼ = a+b-¼ ≥ max(a,b) ≥ √(ab)`). -/
lemma denom_sep (i j : ℕ) {μ lam : ℝ} (hμ : 1 / 4 ≤ μ) (hlam : 1 / 4 ≤ lam) :
    ((i : ℝ) + 1 / 4) * ((j : ℝ) + 1 / 4)
      ≤ ((i : ℝ) + (j : ℝ) + μ) * ((i : ℝ) + (j : ℝ) + lam) := by
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [hi, hj, hμ, hlam, mul_nonneg hi hj]

/-- **The factored error bound** (paper, simplified): `E(μ,λ) ≤ D²`. -/
lemma E_le_D_sq {μ lam : ℝ} (hμ4 : 1 / 4 ≤ μ) (hμ : μ ≤ 1 / 2) (hlam : 1 / 4 ≤ lam) :
    ∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2
        / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam))
      ≤ (∑' i, gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4)) ^ 2 := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hfsum := D_summable
  have hfnn : ∀ i : ℕ, 0 ≤ gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4) := fun i =>
    div_nonneg (gx_pos (1 / 2 : ℝ) hhalf i).le (by positivity)
  have hprod : Summable (fun q : ℕ × ℕ =>
      (gx (1 / 2 : ℝ) q.1 / ((q.1 : ℝ) + 1 / 4)) * (gx (1 / 2 : ℝ) q.2 / ((q.2 : ℝ) + 1 / 4))) :=
    hfsum.mul_of_nonneg hfsum hfnn hfnn
  have hEnn : ∀ q : ℕ × ℕ, 0 ≤ gx μ q.1 * gx μ q.2
      / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam)) := fun q =>
    div_nonneg (mul_nonneg (gx_pos μ hμ0 _).le (gx_pos μ hμ0 _).le) (by positivity)
  have hle : ∀ q : ℕ × ℕ, gx μ q.1 * gx μ q.2
      / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam))
      ≤ (gx (1 / 2 : ℝ) q.1 / ((q.1 : ℝ) + 1 / 4))
          * (gx (1 / 2 : ℝ) q.2 / ((q.2 : ℝ) + 1 / 4)) := by
    intro q
    have hA : (0 : ℝ) < ((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam) := by
      have h1 : (0 : ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + μ := by positivity
      have h2 : (0 : ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + lam := by
        have : (0 : ℝ) ≤ (q.1 : ℝ) + (q.2 : ℝ) := by positivity
        linarith
      positivity
    have hB : (0 : ℝ) < ((q.1 : ℝ) + 1 / 4) * ((q.2 : ℝ) + 1 / 4) := by positivity
    have hnum : gx μ q.1 * gx μ q.2 ≤ gx (1 / 2 : ℝ) q.1 * gx (1 / 2 : ℝ) q.2 :=
      mul_le_mul (gx_mono_param hμ0 hμ q.1) (gx_mono_param hμ0 hμ q.2)
        (gx_pos μ hμ0 _).le (gx_pos (1 / 2 : ℝ) hhalf _).le
    have hhalfnn : (0 : ℝ) ≤ gx (1 / 2 : ℝ) q.1 * gx (1 / 2 : ℝ) q.2 :=
      mul_nonneg (gx_pos (1 / 2 : ℝ) hhalf _).le (gx_pos (1 / 2 : ℝ) hhalf _).le
    rw [div_mul_div_comm, div_le_div_iff₀ hA hB]
    have h1 := mul_le_mul_of_nonneg_right hnum hB.le
    have h2 := mul_le_mul_of_nonneg_left (denom_sep q.1 q.2 hμ4 hlam) hhalfnn
    linarith
  have hEsum : Summable (fun q : ℕ × ℕ => gx μ q.1 * gx μ q.2
      / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam))) :=
    Summable.of_nonneg_of_le hEnn hle hprod
  calc ∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2
        / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam))
      ≤ ∑' q : ℕ × ℕ, (gx (1 / 2 : ℝ) q.1 / ((q.1 : ℝ) + 1 / 4))
          * (gx (1 / 2 : ℝ) q.2 / ((q.2 : ℝ) + 1 / 4)) := Summable.tsum_le_tsum hle hEsum hprod
    _ = (∑' i, gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4)) ^ 2 := by
        rw [← Summable.tsum_mul_tsum hfsum hfsum hprod, ← pow_two]

/-! ### Divergence of `‖x(μ)‖²` as `μ ↑ 1/2` -/

/-- The partial sums of `∑ (gx(1/2)_i)²` are unbounded (the series diverges). -/
lemma half_partial_unbounded (M : ℝ) :
    ∃ N : ℕ, M < ∑ i ∈ range N, (gx (1 / 2 : ℝ) i) ^ 2 := by
  have hπ := Real.pi_pos
  -- `∑ 1/(i+1/2)` diverges
  have hns2 : ¬ Summable (fun i : ℕ => 1 / ((i : ℝ) + 1 / 2)) := by
    intro hs
    have h1 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1)) :=
      Summable.of_nonneg_of_le (fun i => by positivity)
        (fun i => one_div_le_one_div_of_le (by positivity) (by linarith)) hs
    have h3 : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      refine Summable.comp_nat_add (k := 1) ?_
      simpa only [Nat.cast_add, Nat.cast_one] using h1
    exact not_summable_one_div_natCast h3
  -- hence `∑ 1/(π(i+1/2))` diverges
  have hdiv : ¬ Summable (fun i : ℕ => 1 / (π * ((i : ℝ) + 1 / 2))) := by
    intro hs
    refine hns2 ((hs.mul_left π).congr (fun i => ?_))
    field_simp
  -- so `∑ (gx(1/2)_i)²` diverges, by the Wallis lower bound
  have hns : ¬ Summable (fun i : ℕ => (gx (1 / 2 : ℝ) i) ^ 2) := fun hs =>
    hdiv (Summable.of_nonneg_of_le (fun i => by positivity) (fun i => gx_half_sq_ge i) hs)
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun i => sq_nonneg (gx (1 / 2 : ℝ) i))).mp hns
  exact (htend.eventually_gt_atTop M).exists

/-- `μ ↦ gx μ i` is continuous. -/
lemma continuous_gx (i : ℕ) : Continuous (fun μ : ℝ => gx μ i) := by
  simp only [gx]
  exact continuous_finsetProd _ (fun t _ => (continuous_const.add continuous_id).div_const _)

/-- **`‖x(μ)‖²` is unbounded**: for every `M` there is `μ ∈ [1/4, 1/2)` with
`∑' (gx μ i)² > M`. -/
lemma norm_sq_unbounded (M : ℝ) :
    ∃ μ : ℝ, 1 / 4 ≤ μ ∧ μ < 1 / 2 ∧ M < ∑' i, (gx μ i) ^ 2 := by
  obtain ⟨N, hN⟩ := half_partial_unbounded M
  have hcontN : Continuous (fun μ : ℝ => ∑ i ∈ range N, (gx μ i) ^ 2) :=
    continuous_finsetSum _ (fun i _ => (continuous_gx i).pow 2)
  have hopen : IsOpen {μ : ℝ | M < ∑ i ∈ range N, (gx μ i) ^ 2} :=
    isOpen_lt continuous_const hcontN
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen (1 / 2) hN
  set e := min (δ / 2) (1 / 8) with he
  have he0 : (0 : ℝ) < e := lt_min (by linarith) (by norm_num)
  have he8 : e ≤ 1 / 8 := min_le_right _ _
  have heδ : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hμ0 : (0 : ℝ) < 1 / 2 - e := by linarith
  have hμ2 : (1 / 2 : ℝ) - e < 1 / 2 := by linarith
  refine ⟨1 / 2 - e, by linarith, hμ2, ?_⟩
  have hmem : (1 / 2 - e) ∈ {μ : ℝ | M < ∑ i ∈ range N, (gx μ i) ^ 2} := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, show (1 / 2 - e) - 1 / 2 = -e by ring, abs_neg,
      abs_of_pos he0]
    exact heδ
  calc M < ∑ i ∈ range N, (gx (1 / 2 - e) i) ^ 2 := hmem
    _ ≤ ∑' i, (gx (1 / 2 - e) i) ^ 2 :=
        Summable.sum_le_tsum _ (fun i _ => sq_nonneg _) (gx_sq_summable _ hμ0 hμ2)

/-! ### Assembly: the lower bound `‖H_λ‖ ≥ π` for `λ ≥ 1/2` -/

/-- Summability of the perturbation error series. -/
lemma E_summable {μ lam : ℝ} (hμ4 : 1 / 4 ≤ μ) (hμ : μ ≤ 1 / 2) (hlam : 1 / 4 ≤ lam) :
    Summable (fun q : ℕ × ℕ => gx μ q.1 * gx μ q.2
      / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam))) := by
  have hμ0 : (0 : ℝ) < μ := by linarith
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hfsum := D_summable
  have hfnn : ∀ i : ℕ, 0 ≤ gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4) := fun i =>
    div_nonneg (gx_pos (1 / 2 : ℝ) hhalf i).le (by positivity)
  have hprod : Summable (fun q : ℕ × ℕ =>
      (gx (1 / 2 : ℝ) q.1 / ((q.1 : ℝ) + 1 / 4)) * (gx (1 / 2 : ℝ) q.2 / ((q.2 : ℝ) + 1 / 4))) :=
    hfsum.mul_of_nonneg hfsum hfnn hfnn
  refine Summable.of_nonneg_of_le (fun q =>
    div_nonneg (mul_nonneg (gx_pos μ hμ0 _).le (gx_pos μ hμ0 _).le) (by positivity))
    (fun q => ?_) hprod
  have hA : (0 : ℝ) < ((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam) := by
    have h1 : (0 : ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + μ := by positivity
    have h2 : (0 : ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + lam := by
      have : (0 : ℝ) ≤ (q.1 : ℝ) + (q.2 : ℝ) := by positivity
      linarith
    positivity
  have hB : (0 : ℝ) < ((q.1 : ℝ) + 1 / 4) * ((q.2 : ℝ) + 1 / 4) := by positivity
  have hnum : gx μ q.1 * gx μ q.2 ≤ gx (1 / 2 : ℝ) q.1 * gx (1 / 2 : ℝ) q.2 :=
    mul_le_mul (gx_mono_param hμ0 hμ q.1) (gx_mono_param hμ0 hμ q.2)
      (gx_pos μ hμ0 _).le (gx_pos (1 / 2 : ℝ) hhalf _).le
  have hhalfnn : (0 : ℝ) ≤ gx (1 / 2 : ℝ) q.1 * gx (1 / 2 : ℝ) q.2 :=
    mul_nonneg (gx_pos (1 / 2 : ℝ) hhalf _).le (gx_pos (1 / 2 : ℝ) hhalf _).le
  rw [div_mul_div_comm, div_le_div_iff₀ hA hB]
  have h1 := mul_le_mul_of_nonneg_right hnum hB.le
  have h2 := mul_le_mul_of_nonneg_left (denom_sep q.1 q.2 hμ4 hlam) hhalfnn
  linarith

/-- **Sharpness for `λ ≥ 1/2`** (paper Theorem `sharp-large`, lower bound): the
Rayleigh quotient of `H_λ` at the test vectors `x(μ)` exceeds `π - ε`.  With the
upper bound `‖H_λ‖ ≤ π` this gives `‖H_λ‖ = π`. -/
theorem norm_ge_pi_sharp {lam : ℝ} (hlam : 1 / 2 ≤ lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 1 / 4 ≤ μ ∧ μ < 1 / 2 ∧
      (π - ε) * (∑' i, (gx μ i) ^ 2)
        < ∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam) := by
  have hπ := Real.pi_pos
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hlam4 : (1 : ℝ) / 4 ≤ lam := by linarith
  obtain ⟨μ, hμ4, hμ2, hM⟩ :=
    norm_sq_unbounded (lam * (∑' i, gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4)) ^ 2 / ε)
  have hμ0 : (0 : ℝ) < μ := by linarith
  refine ⟨μ, hμ4, hμ2, ?_⟩
  have hgxnn : ∀ q : ℕ × ℕ, (0 : ℝ) ≤ gx μ q.1 * gx μ q.2 := fun q =>
    mul_nonneg (gx_pos μ hμ0 _).le (gx_pos μ hμ0 _).le
  have hHμ := gx_double_summable μ hμ0 hμ2
  have hE := E_summable hμ4 hμ2.le hlam4
  -- the `λ`-series is summable, dominated by the `μ`-series
  have hHlam : Summable (fun q : ℕ × ℕ =>
      gx μ q.1 * gx μ q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)) := by
    refine Summable.of_nonneg_of_le
      (fun q => div_nonneg (hgxnn q) (by positivity)) (fun q => ?_) hHμ
    have h1 : (0 : ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + μ := by positivity
    have h2 : (0 : ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + lam := by linarith
    have hμlam : (q.1 : ℝ) + (q.2 : ℝ) + μ ≤ (q.1 : ℝ) + (q.2 : ℝ) + lam := by linarith
    rw [div_le_div_iff₀ h2 h1]
    exact mul_le_mul_of_nonneg_left hμlam (hgxnn q)
  -- the perturbation identity
  have hsplit : ∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + μ)
      = (∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam))
        + (lam - μ) * (∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2
            / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam))) := by
    rw [← tsum_mul_left, ← Summable.tsum_add hHlam (hE.mul_left _)]
    refine tsum_congr (fun q => ?_)
    have hc : (0 : ℝ) ≤ (q.1 : ℝ) + (q.2 : ℝ) := by positivity
    have h1 : ((q.1 : ℝ) + (q.2 : ℝ) + μ) ≠ 0 := by positivity
    have h2 : ((q.1 : ℝ) + (q.2 : ℝ) + lam) ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have hray := rayleigh μ hμ0 hμ2
  rw [hsplit] at hray
  -- estimates
  have hS0 : (0 : ℝ) ≤ ∑' i, (gx μ i) ^ 2 := tsum_nonneg (fun i => sq_nonneg _)
  have hsin := sin_pi_mul_pos μ hμ0 (by linarith : μ < 1)
  have hratio : π ≤ π / Real.sin (π * μ) := by
    rw [le_div_iff₀ hsin]; nlinarith [Real.sin_le_one (π * μ)]
  have hπS := mul_le_mul_of_nonneg_right hratio hS0
  have hEnn : (0 : ℝ) ≤ ∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2
      / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam)) :=
    tsum_nonneg (fun q => div_nonneg (hgxnn q) (by positivity))
  have hEbound : (lam - μ) * (∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2
      / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam)))
      ≤ lam * (∑' i, gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4)) ^ 2 := by
    have hle := E_le_D_sq hμ4 hμ2.le hlam4
    nlinarith [hEnn, hle, hlam0, hμ0]
  rw [div_lt_iff₀ hε] at hM
  calc (π - ε) * (∑' i, (gx μ i) ^ 2)
      = π * (∑' i, (gx μ i) ^ 2) - ε * (∑' i, (gx μ i) ^ 2) := by ring
    _ < π * (∑' i, (gx μ i) ^ 2)
          - lam * (∑' i, gx (1 / 2 : ℝ) i / ((i : ℝ) + 1 / 4)) ^ 2 := by nlinarith [hM]
    _ ≤ (π / Real.sin (π * μ)) * (∑' i, (gx μ i) ^ 2)
          - (lam - μ) * (∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2
              / (((q.1 : ℝ) + (q.2 : ℝ) + μ) * ((q.1 : ℝ) + (q.2 : ℝ) + lam))) := by
        linarith [hπS, hEbound]
    _ = ∑' q : ℕ × ℕ, gx μ q.1 * gx μ q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam) := by linarith [hray]

/-! ### The matching upper bound `‖H_λ‖ ≤ π` for `λ ≥ 1/2` -/

/-- **Upper bound** (paper Theorem `main`, final statement): for `λ ≥ 1/2` the
entrywise domination `1/(i+j+λ) ≤ 1/(i+j+1/2)` gives the constant `π`. -/
theorem hilbert_le_pi_finite {lam : ℝ} (hlam : 1 / 2 ≤ lam) (N : ℕ) (u v : ℕ → ℝ) :
    ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + lam)
      ≤ π * Real.sqrt (∑ i ∈ range N, u i ^ 2) * Real.sqrt (∑ j ∈ range N, v j ^ 2) := by
  have hsin : Real.sin (π * (1 / 2 : ℝ)) = 1 := by
    rw [show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two]
  have hhalf := schur_inequality_finite (1 / 2 : ℝ) (by norm_num) (by norm_num) N
    (fun i => |u i|) (fun j => |v j|)
  rw [hsin, div_one] at hhalf
  simp only [sq_abs] at hhalf
  refine le_trans ?_ hhalf
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hij : (0 : ℝ) ≤ (i : ℝ) + (j : ℝ) := by positivity
  have hB : (0 : ℝ) < (i : ℝ) + (j : ℝ) + 1 / 2 := by linarith
  have hA : (0 : ℝ) < (i : ℝ) + (j : ℝ) + lam := by linarith
  have hAB : (i : ℝ) + (j : ℝ) + 1 / 2 ≤ (i : ℝ) + (j : ℝ) + lam := by linarith
  have h3 : u i * v j ≤ |u i| * |v j| := (le_abs_self _).trans (abs_mul _ _).le
  have habs : (0 : ℝ) ≤ |u i| * |v j| := by positivity
  calc u i * v j / ((i : ℝ) + (j : ℝ) + lam)
      ≤ |u i| * |v j| / ((i : ℝ) + (j : ℝ) + lam) := by
        rw [div_le_div_iff_of_pos_right hA]; exact h3
    _ ≤ |u i| * |v j| / ((i : ℝ) + (j : ℝ) + 1 / 2) := by
        rw [div_le_div_iff₀ hA hB]; exact mul_le_mul_of_nonneg_left hAB habs

end HilbertPi.General
