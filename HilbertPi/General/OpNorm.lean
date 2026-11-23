/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.Convolution
import HilbertPi.General.L2
import HilbertPi.General.SharpLarge

/-!
# The operator norm of `H_λ`: `‖H_λ‖ = π csc(πλ)` and `‖H_λ‖ = π`

This file introduces the norm of the generalized Hilbert matrix
`H_λ[i,j] = 1/(i+j+λ)` in the form used in the paper (Section 1): the supremum
of the bilinear form over *finitely supported* unit vectors,

  `opNorm λ = sup { ∑_{i,j<N} u_i v_j /(i+j+λ) : ∑_{i<N} u_i² = ∑_{j<N} v_j² = 1 }`,

and proves the two sharpness theorems as statements about that number:

* `opNorm_eq_csc` — `‖H_λ‖ = π csc(πλ)` for `0 < λ < 1/2`;
* `opNorm_eq_pi` — `‖H_λ‖ = π` for every `λ ≥ 1/2` (paper Thm. `sharp-large`).

For `0 < λ < 1/2` the lower bound comes from the `ℓ²` Rayleigh estimate of
`Sharp.lean` through `lt_opNorm_of_tsum`, which extracts a finitely supported
truncation of an `ℓ²` test vector. For `λ ≥ 1/2` it is `pi_le_opNorm`, which
tests the form on truncated central binomial vectors, as in the paper's proof.

For `0 < λ < 1/2` the norm is moreover *attained*, and this is recorded as a
genuine `ℓ²` statement:

* `schur_norm_attained_l2` — `π csc(πλ)` is the greatest value of the `ℓ²`
  bilinear form on unit vectors, realized at `gx λ / ‖gx λ‖`.
-/

namespace HilbertPi.General

open Finset Real
open scoped ENNReal

/-! ### The norm as a supremum over finitely supported unit vectors -/

/-- The values of the bilinear form of `H_λ` at finitely supported unit
vectors. -/
def bilinValues (lam : ℝ) : Set ℝ :=
  {c : ℝ | ∃ (N : ℕ) (u v : ℕ → ℝ), ∑ i ∈ range N, u i ^ 2 = 1 ∧
    ∑ j ∈ range N, v j ^ 2 = 1 ∧
    c = ∑ i ∈ range N, ∑ j ∈ range N, u i * v j / ((i : ℝ) + (j : ℝ) + lam)}

/-- **`‖H_λ‖`** (paper Section 1): the supremum of the bilinear form of `H_λ`
over finitely supported unit vectors. -/
noncomputable def opNorm (lam : ℝ) : ℝ := sSup (bilinValues lam)

lemma bilinValues_nonempty (lam : ℝ) : (bilinValues lam).Nonempty :=
  ⟨_, 1, (fun _ => 1), (fun _ => 1), by simp, by simp, rfl⟩

/-- A finitely-supported bilinear bound with constant `C` bounds `bilinValues`. -/
lemma bilinValues_le {lam C : ℝ} (hfin : FiniteBound lam C) :
    ∀ c ∈ bilinValues lam, c ≤ C := by
  rintro c ⟨N, u, v, hu, hv, rfl⟩
  have h := hfin N u v
  rwa [hu, hv, Real.sqrt_one, mul_one, mul_one] at h

lemma bddAbove_bilinValues {lam C : ℝ} (hfin : FiniteBound lam C) :
    BddAbove (bilinValues lam) :=
  ⟨C, bilinValues_le hfin⟩

/-- The upper bound half: any finitely-supported bilinear bound bounds the
norm. -/
lemma opNorm_le {lam C : ℝ} (hfin : FiniteBound lam C) : opNorm lam ≤ C :=
  csSup_le (bilinValues_nonempty lam) (bilinValues_le hfin)

/-- The norm is positive (the vector `e₀` already gives `1/λ`). -/
lemma opNorm_pos {lam C : ℝ} (hlam : 0 < lam) (hfin : FiniteBound lam C) :
    0 < opNorm lam := by
  refine lt_csSup_of_lt (bddAbove_bilinValues hfin)
    ⟨1, (fun _ => 1), (fun _ => 1), by simp, by simp, rfl⟩ ?_
  simp only [Finset.sum_range_one, Nat.cast_zero, one_mul, zero_add]
  positivity

/-- **Lower bound from a finitely supported test vector.** -/
lemma lt_opNorm {lam C c : ℝ} (hlam : 0 < lam) (hfin : FiniteBound lam C)
    (N : ℕ) (u : ℕ → ℝ) (hu : 0 < ∑ i ∈ range N, u i ^ 2)
    (h : c * (∑ i ∈ range N, u i ^ 2)
        < ∑ i ∈ range N, ∑ j ∈ range N, u i * u j / ((i : ℝ) + (j : ℝ) + lam)) :
    c < opNorm lam := by
  set S : ℝ := ∑ i ∈ range N, u i ^ 2 with hS
  set s : ℝ := Real.sqrt S with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu
  have hs2 : s ^ 2 = S := Real.sq_sqrt hu.le
  set u' : ℕ → ℝ := fun i => u i / s with hu'
  have hnorm : ∑ i ∈ range N, u' i ^ 2 = 1 := by
    simp only [hu', div_pow]
    rw [← Finset.sum_div, ← hS, hs2, div_self hu.ne']
  have hbil : ∑ i ∈ range N, ∑ j ∈ range N, u' i * u' j / ((i : ℝ) + (j : ℝ) + lam)
      = (∑ i ∈ range N, ∑ j ∈ range N, u i * u j / ((i : ℝ) + (j : ℝ) + lam)) / S := by
    rw [← hs2, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd : ((i : ℝ) + (j : ℝ) + lam) ≠ 0 := (denom_pos hlam i j).ne'
    simp only [hu']
    field_simp
  refine lt_csSup_of_lt (bddAbove_bilinValues hfin)
    ⟨N, u', u', hnorm, hnorm, rfl⟩ ?_
  rw [hbil, lt_div_iff₀ hu]
  exact h

/-! ### Truncating an `ℓ²` test vector -/

/-- Square truncations of a nonnegative summable family on `ℕ × ℕ` exhaust its
sum. -/
lemma exists_square_sum_gt {F : ℕ × ℕ → ℝ} (hF : Summable F) (hFnn : ∀ q, 0 ≤ F q)
    {c : ℝ} (hc : c < ∑' q, F q) :
    ∃ N : ℕ, c < ∑ i ∈ range N, ∑ j ∈ range N, F (i, j) := by
  classical
  obtain ⟨t, ht⟩ := (hF.hasSum.eventually_const_lt hc).exists
  refine ⟨1 + t.sup (fun q => max q.1 q.2), ?_⟩
  set N : ℕ := 1 + t.sup (fun q => max q.1 q.2) with hN
  have hsub : t ⊆ Finset.range N ×ˢ Finset.range N := by
    intro q hq
    have h1 : q.1 ≤ t.sup (fun q => max q.1 q.2) :=
      le_trans (le_max_left _ _) (Finset.le_sup (f := fun q => max q.1 q.2) hq)
    have h2 : q.2 ≤ t.sup (fun q => max q.1 q.2) :=
      le_trans (le_max_right _ _) (Finset.le_sup (f := fun q => max q.1 q.2) hq)
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have hle : ∑ q ∈ t, F q ≤ ∑ q ∈ Finset.range N ×ˢ Finset.range N, F q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hFnn q)
  rw [← Finset.sum_product]
  linarith

/-- Square truncations are monotone for a nonnegative family. -/
lemma square_sum_mono {F : ℕ × ℕ → ℝ} (hFnn : ∀ q, 0 ≤ F q) {M N : ℕ} (hMN : M ≤ N) :
    ∑ i ∈ range M, ∑ j ∈ range M, F (i, j)
      ≤ ∑ i ∈ range N, ∑ j ∈ range N, F (i, j) := by
  rw [← Finset.sum_product, ← Finset.sum_product]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.product_subset_product (Finset.range_subset_range.mpr hMN)
      (Finset.range_subset_range.mpr hMN)) (fun q _ _ => hFnn q)

/-- **Lower bound from an `ℓ²` test vector.**  A positive square-summable test
vector whose (infinite) Rayleigh quotient exceeds `c` yields a finitely
supported witness, hence `c < ‖H_λ‖`. -/
lemma lt_opNorm_of_tsum {lam C c : ℝ} (hlam : 0 < lam) (hfin : FiniteBound lam C)
    (hc : 0 ≤ c) (w : ℕ → ℝ) (hw : ∀ i, 0 < w i)
    (hsq : Summable (fun i => (w i) ^ 2))
    (hsum : Summable (fun q : ℕ × ℕ => w q.1 * w q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)))
    (h : c * (∑' i, (w i) ^ 2)
        < ∑' q : ℕ × ℕ, w q.1 * w q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)) :
    c < opNorm lam := by
  have hFnn : ∀ q : ℕ × ℕ, 0 ≤ w q.1 * w q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam) :=
    fun q => div_nonneg (mul_nonneg (hw _).le (hw _).le) (denom_pos hlam _ _).le
  obtain ⟨N, hN⟩ := exists_square_sum_gt hsum hFnn h
  refine lt_opNorm hlam hfin (N + 1) w ?_ ?_
  · refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    exact pow_pos (hw 0) 2
  · calc c * (∑ i ∈ range (N + 1), w i ^ 2)
        ≤ c * (∑' i, (w i) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (Summable.sum_le_tsum _ (fun i _ => sq_nonneg _) hsq) hc
      _ < ∑ i ∈ range N, ∑ j ∈ range N,
            w i * w j / ((i : ℝ) + (j : ℝ) + lam) := hN
      _ ≤ ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
            w i * w j / ((i : ℝ) + (j : ℝ) + lam) :=
          square_sum_mono hFnn (Nat.le_succ N)

/-! ### `‖H_λ‖ = π csc(πλ)` for `0 < λ < 1/2` -/

/-- **The norm of `H_λ` for `0 < λ < 1/2`** (paper Prop. `exact-eig`):
`‖H_λ‖ = π csc(πλ)`. -/
theorem opNorm_eq_csc {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    opNorm l = π / Real.sin (π * l) := by
  have hl1' : l < 1 := by linarith
  have hfin := finiteBound_schur l hl0 hl1'
  have hθ : 0 < π / Real.sin (π * l) :=
    div_pos Real.pi_pos (sin_pi_mul_pos l hl0 hl1')
  refine le_antisymm (opNorm_le hfin) ?_
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  rcases le_or_gt (π / Real.sin (π * l)) ε with hbig | hbig
  · linarith [opNorm_pos hl0 hfin]
  · have hS : 0 < ∑' i, (gx l i) ^ 2 := (schur_norm_attained l hl0 hl1).2
    have hlt : (π / Real.sin (π * l) - ε) * (∑' i, (gx l i) ^ 2)
        < ∑' q : ℕ × ℕ, gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l) := by
      rw [(schur_norm_attained l hl0 hl1).1]
      nlinarith
    have := lt_opNorm_of_tsum hl0 hfin (by linarith) (gx l) (gx_pos l hl0)
      (gx_sq_summable l hl0 hl1) (gx_double_summable l hl0 hl1) hlt
    linarith

/-! ### `‖H_λ‖ = π` for `λ ≥ 1/2` -/

/-- The `λ ≥ 1/2` bound of `SharpLarge.lean`, packaged as a `FiniteBound`. -/
lemma finiteBound_pi {lam : ℝ} (hlam : 1 / 2 ≤ lam) : FiniteBound lam π :=
  fun N u v => hilbert_le_pi_finite hlam N u v

section LandauTestVector

open Filter Topology

/-- The Rayleigh quotient at a finitely supported nonzero vector is at most the
norm. -/
lemma bilin_le_opNorm_mul {lam C : ℝ} (hlam : 0 < lam) (hfin : FiniteBound lam C)
    (N : ℕ) (w : ℕ → ℝ) (hw : 0 < ∑ i ∈ range N, w i ^ 2) :
    ∑ i ∈ range N, ∑ j ∈ range N, w i * w j / ((i : ℝ) + (j : ℝ) + lam)
      ≤ opNorm lam * ∑ i ∈ range N, w i ^ 2 := by
  by_contra h
  exact lt_irrefl _ (lt_opNorm hlam hfin N w hw (not_le.mp h))

/-- Testing `H_λ` on the truncated central binomial vector: the convolution
identity evaluates the part of the form with `i + j < n`. -/
lemma sum_inv_le_bilin {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ∑ k ∈ range n, 1 / ((k : ℝ) + lam)
      ≤ ∑ i ∈ range n, ∑ j ∈ range n,
          HilbertPi.x i * HilbertPi.x j / ((i : ℝ) + (j : ℝ) + lam) := by
  set F : ℕ × ℕ → ℝ := fun p =>
    HilbertPi.x p.1 * HilbertPi.x p.2 / ((p.1 : ℝ) + (p.2 : ℝ) + lam) with hF
  have hFnn : ∀ p, 0 ≤ F p := fun p =>
    div_nonneg (mul_nonneg (HilbertPi.x_nonneg _) (HilbertPi.x_nonneg _))
      (denom_pos hlam _ _).le
  have hk : ∀ k ∈ range n, 1 / ((k : ℝ) + lam) = ∑ p ∈ antidiagonal k, F p := by
    intro k _
    have hc : ((k : ℝ) + lam) ≠ 0 := by positivity
    have hterm : ∀ p ∈ antidiagonal k, F p =
        (HilbertPi.x p.1 * HilbertPi.x p.2) * (1 / ((k : ℝ) + lam)) := by
      intro p hp
      have hsum : (p.1 : ℝ) + (p.2 : ℝ) = k := by
        exact_mod_cast mem_antidiagonal.mp hp
      simp only [hF, hsum]
      ring
    rw [sum_congr rfl hterm, ← sum_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have := HilbertPi.conv k
    simp only at this ⊢
    rw [this, one_mul]
  have hdisj : (↑(range n) : Set ℕ).PairwiseDisjoint (fun k => antidiagonal k) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun p hpa hpb => hab ?_
    rw [mem_antidiagonal] at hpa hpb
    omega
  have hsub : (range n).biUnion (fun k => antidiagonal k) ⊆ range n ×ˢ range n := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_biUnion.mp hp
    rw [mem_range] at hk
    rw [mem_antidiagonal] at hpk
    simp only [mem_product, mem_range]
    omega
  calc ∑ k ∈ range n, 1 / ((k : ℝ) + lam)
      = ∑ k ∈ range n, ∑ p ∈ antidiagonal k, F p := sum_congr rfl hk
    _ = ∑ p ∈ (range n).biUnion (fun k => antidiagonal k), F p :=
        (sum_biUnion hdisj).symm
    _ ≤ ∑ p ∈ range n ×ˢ range n, F p :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hFnn p
    _ = _ := sum_product _ _ _

/-- The Wallis quantity converges: `(m + 1/2) x_m² → 1/π`. -/
lemma tendsto_wallis_u : Tendsto HilbertPi.u atTop (𝓝 (1 / π)) := by
  have hW := Real.Wallis.tendsto_W_nhds_pi_div_two
  have h2 : Tendsto (fun m => 1 / (2 * Real.Wallis.W m)) atTop (𝓝 (1 / (2 * (π / 2)))) :=
    tendsto_const_nhds.div (hW.const_mul 2) (by positivity)
  have he : (2 : ℝ) * (π / 2) = π := by ring
  rw [he] at h2
  exact h2.congr fun m => (HilbertPi.u_eq_inv_two_W m).symm

/-- For all large `k`, `1/(k+λ) ≥ (π-ε) x_k²`. -/
lemma exists_inv_ge_x_sq {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, (π - ε) * HilbertPi.x k ^ 2 ≤ 1 / ((k : ℝ) + lam) := by
  have hπ := Real.pi_pos
  have hratio : Tendsto (fun k : ℕ => ((k : ℝ) + lam) / ((k : ℝ) + 1 / 2)) atTop (𝓝 1) := by
    have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1 / 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hquot : Tendsto (fun k : ℕ => (lam - 1 / 2) / ((k : ℝ) + 1 / 2)) atTop (𝓝 0) :=
      hden.const_div_atTop _
    have h1 : Tendsto (fun k : ℕ => 1 + (lam - 1 / 2) / ((k : ℝ) + 1 / 2)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hquot
    rw [add_zero] at h1
    refine h1.congr fun k => ?_
    have : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    field_simp
    ring
  have hprod : Tendsto (fun k : ℕ => (π - ε) *
      (((k : ℝ) + lam) / ((k : ℝ) + 1 / 2) * HilbertPi.u k)) atTop
      (𝓝 ((π - ε) * (1 * (1 / π)))) :=
    (hratio.mul tendsto_wallis_u).const_mul _
  have hlim : (π - ε) * (1 * (1 / π)) < 1 := by
    rw [one_mul, mul_one_div, div_lt_one hπ]
    linarith
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hprod.eventually_lt_const hlim)
  refine ⟨K, fun k hk => ?_⟩
  have h := hK k hk
  have hc : (0 : ℝ) < (k : ℝ) + lam := by positivity
  have hd : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  have he : (π - ε) * (((k : ℝ) + lam) / ((k : ℝ) + 1 / 2) * HilbertPi.u k)
      = (π - ε) * HilbertPi.x k ^ 2 * ((k : ℝ) + lam) := by
    simp only [HilbertPi.u]
    field_simp
  rw [he] at h
  rw [le_div_iff₀ hc]
  exact h.le

/-- **The lower bound `π ≤ ‖H_λ‖`, for every `λ > 0`** (paper Thm.
`sharp-large`). The test vectors are the truncated central binomial vectors. -/
theorem pi_le_opNorm {lam C : ℝ} (hlam : 0 < lam) (hfin : FiniteBound lam C) :
    π ≤ opNorm lam := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨K, hK⟩ := exists_inv_ge_x_sq hlam hε
  set c := opNorm lam with hc
  set Sn : ℕ → ℝ := fun n => ∑ m ∈ range n, HilbertPi.x m ^ 2 with hSn
  have hd : 0 < π - ε - c := by linarith
  obtain ⟨N, hN⟩ := half_partial_unbounded ((π - ε) * Sn K / (π - ε - c))
  simp only [gx_half_eq] at hN
  set n := max N (K + 1) with hn
  have hNn : N ≤ n := le_max_left _ _
  have hKn : K ≤ n := le_trans (Nat.le_succ K) (le_max_right _ _)
  have hSnn : Sn N ≤ Sn n :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hNn) fun _ _ _ => sq_nonneg _
  have hSpos : 0 < Sn n := by
    refine sum_pos' (fun _ _ => sq_nonneg _) ⟨0, mem_range.mpr ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.succ_pos K) (le_max_right _ _)
    · exact pow_pos (HilbertPi.x_pos 0) 2
  have hupper : ∑ k ∈ range n, 1 / ((k : ℝ) + lam) ≤ c * Sn n :=
    (sum_inv_le_bilin hlam n).trans (bilin_le_opNorm_mul hlam hfin n HilbertPi.x hSpos)
  have hlower : (π - ε) * (Sn n - Sn K) ≤ ∑ k ∈ range n, 1 / ((k : ℝ) + lam) := by
    have hsplit : Sn n - Sn K = ∑ k ∈ Ico K n, HilbertPi.x k ^ 2 := by
      simp only [hSn]
      rw [Finset.sum_Ico_eq_sub _ hKn]
    rw [hsplit, mul_sum]
    calc ∑ k ∈ Ico K n, (π - ε) * HilbertPi.x k ^ 2
        ≤ ∑ k ∈ Ico K n, 1 / ((k : ℝ) + lam) :=
          sum_le_sum fun k hk => hK k (mem_Ico.mp hk).1
      _ ≤ ∑ k ∈ range n, 1 / ((k : ℝ) + lam) :=
          sum_le_sum_of_subset_of_nonneg
            (fun k hk => mem_range.mpr (mem_Ico.mp hk).2)
            (fun k _ _ => by positivity)
  have hbig : (π - ε) * Sn K < (π - ε - c) * Sn n := by
    have h1 : (π - ε) * Sn K / (π - ε - c) < Sn n := lt_of_lt_of_le hN hSnn
    rwa [div_lt_iff₀ hd, mul_comm (Sn n)] at h1
  nlinarith [hupper, hlower, hbig]

end LandauTestVector

/-- **The norm of `H_λ` for `λ ≥ 1/2`** (paper Thm. `sharp-large`):
`‖H_λ‖ = π`. -/
theorem opNorm_eq_pi {lam : ℝ} (hlam : 1 / 2 ≤ lam) : opNorm lam = π := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hfin := finiteBound_pi hlam
  exact le_antisymm (opNorm_le hfin) (pi_le_opNorm hlam0 hfin)

/-! ### Attainment on `ℓ²` for `0 < λ < 1/2` -/

section Attained

variable {l : ℝ}

/-- The square-summable eigenvector `gx λ` as an element of `ℓ²`. -/
noncomputable def gxL2 (hl0 : 0 < l) (hl1 : l < 1 / 2) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨gx l, memℓp_gen (by
    have h2 : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by simp
    have : (fun i : ℕ => ‖gx l i‖ ^ ((2 : ℝ≥0∞)).toReal) = fun i : ℕ => (gx l i) ^ 2 := by
      funext i
      rw [h2, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
    rw [this]
    exact gx_sq_summable l hl0 hl1)⟩

@[simp] lemma gxL2_apply (hl0 : 0 < l) (hl1 : l < 1 / 2) (i : ℕ) :
    (gxL2 hl0 hl1) i = gx l i := rfl

lemma norm_gxL2_sq (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    ‖gxL2 hl0 hl1‖ ^ 2 = ∑' i, (gx l i) ^ 2 := by
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞)).toReal := by simp
  have h := lp.norm_rpow_eq_tsum hp (gxL2 hl0 hl1)
  have h2 : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by simp
  rw [h2, Real.rpow_natCast] at h
  rw [h]
  refine tsum_congr fun i => ?_
  rw [Real.rpow_natCast, gxL2_apply, Real.norm_eq_abs, sq_abs]

lemma norm_gxL2_pos (hl0 : 0 < l) (hl1 : l < 1 / 2) : 0 < ‖gxL2 hl0 hl1‖ := by
  have hS : 0 < ∑' i, (gx l i) ^ 2 := (schur_norm_attained l hl0 hl1).2
  have hsq : 0 < ‖gxL2 hl0 hl1‖ ^ 2 := by rw [norm_gxL2_sq]; exact hS
  by_contra hcon
  rw [le_antisymm (not_lt.mp hcon) (norm_nonneg _)] at hsq
  norm_num at hsq

/-- The values of the `ℓ²` bilinear form of `H_λ` at unit vectors. -/
def bilinValuesL2 (lam : ℝ) : Set ℝ :=
  {c : ℝ | ∃ f g : lp (fun _ : ℕ => ℝ) 2, ‖f‖ = 1 ∧ ‖g‖ = 1 ∧
    c = ∑' q : ℕ × ℕ, f q.1 * g q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + lam)}

/-- **The norm is attained on `ℓ²`** (paper Prop. `exact-eig`): for
`0 < λ < 1/2` the value `π csc(πλ)` is the *greatest* value of the `ℓ²`
bilinear form of `H_λ` at unit vectors, and it is realized at the normalized
eigenvector `gx λ / ‖gx λ‖`. -/
theorem schur_norm_attained_l2 (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    IsGreatest (bilinValuesL2 l) (π / Real.sin (π * l)) := by
  have hl1' : l < 1 := by linarith
  have hn := norm_gxL2_pos hl0 hl1
  set a : ℝ := ‖gxL2 hl0 hl1‖⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hn
  set f : lp (fun _ : ℕ => ℝ) 2 := a • gxL2 hl0 hl1 with hf
  constructor
  · refine ⟨f, f, ?_, ?_, ?_⟩
    · rw [hf, norm_smul, Real.norm_eq_abs, abs_of_pos ha0, ha, inv_mul_cancel₀ hn.ne']
    · rw [hf, norm_smul, Real.norm_eq_abs, abs_of_pos ha0, ha, inv_mul_cancel₀ hn.ne']
    · have hfa : ∀ i : ℕ, f i = a * gx l i := by
        intro i
        rw [hf, lp.coeFn_smul]
        simp
      have hterm : ∀ q : ℕ × ℕ,
          f q.1 * f q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l)
            = a ^ 2 * (gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l)) := by
        intro q
        rw [hfa, hfa]
        ring
      rw [tsum_congr hterm, tsum_mul_left, (schur_norm_attained l hl0 hl1).1,
        ← norm_gxL2_sq hl0 hl1, ha]
      field_simp
  · rintro c ⟨f, g, hf1, hg1, rfl⟩
    have h := schur_inequality_l2 l hl0 hl1' f g
    rw [hf1, hg1, mul_one, mul_one] at h
    exact (le_abs_self _).trans h

/-- Restated as a supremum: `‖H_λ‖_{ℓ²} = π csc(πλ)` for `0 < λ < 1/2`. -/
theorem sSup_bilinValuesL2 (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    sSup (bilinValuesL2 l) = π / Real.sin (π * l) :=
  (schur_norm_attained_l2 hl0 hl1).csSup_eq

end Attained

end HilbertPi.General
