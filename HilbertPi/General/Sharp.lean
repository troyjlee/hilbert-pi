/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.Domination
import HilbertPi.General.Main
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Sharpness of Schur's bound on `ℓ²` (paper Section 5)

For `0 < λ < 1/2` the eigenvector `gx λ` is square-summable and satisfies the
exact identity `∑' j, gx_j /(i+j+λ) = (π/sin πλ) gx_i`, so the constant
`π csc(πλ)` is attained.

This file builds the analytic foundations: Wendel's Γ bounds (from
log-convexity), the resulting decay bound `gx λ m ≤ m^{λ-1}/Γ(λ)`, and
square-summability of `gx λ`.
-/

namespace HilbertPi.General

open Real Finset

variable (l : ℝ)

/-- **Wendel's upper bound** (paper Lemma 16(ii)): `Γ(a+λ) ≤ Γ(a) · a^λ` for
`a > 0`, from log-convexity of `Γ`. -/
lemma Gamma_add_le (hl0 : 0 < l) (hl1 : l < 1) {a : ℝ} (ha : 0 < a) :
    Gamma (a + l) ≤ Gamma a * a ^ l := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hGa := Real.Gamma_pos_of_pos ha
  have hGa1 := Real.Gamma_pos_of_pos ha1
  have hGal := Real.Gamma_pos_of_pos (show (0:ℝ) < a + l by linarith)
  set F : ℝ → ℝ := fun x => Real.log (Gamma x) with hF
  have hconv : ConvexOn ℝ (Set.Ioi 0) F := Real.convexOn_log_Gamma
  have hcomb : (1 - l) * a + l * (a + 1) = a + l := by ring
  have hc := hconv.2 (show a ∈ Set.Ioi (0:ℝ) from ha)
    (show a + 1 ∈ Set.Ioi (0:ℝ) from ha1) (by linarith : (0:ℝ) ≤ 1 - l)
    (le_of_lt hl0) (by ring : (1 - l) + l = 1)
  simp only [smul_eq_mul, hcomb] at hc
  -- hc : F (a+l) ≤ (1-l) F a + l F (a+1)
  have hGa1eq : Real.log (Gamma (a + 1)) = Real.log a + Real.log (Gamma a) := by
    rw [Real.Gamma_add_one (ne_of_gt ha), Real.log_mul (ne_of_gt ha) (ne_of_gt hGa)]
  have hlog : Real.log (Gamma (a + l)) ≤ Real.log (Gamma a) + l * Real.log a := by
    simp only [hF] at hc
    rw [hGa1eq] at hc
    nlinarith [hc]
  -- exponentiate
  have hrpow : a ^ l = Real.exp (l * Real.log a) := by
    rw [Real.rpow_def_of_pos ha]; ring_nf
  rw [hrpow]
  calc Gamma (a + l) = Real.exp (Real.log (Gamma (a + l))) := (Real.exp_log hGal).symm
    _ ≤ Real.exp (Real.log (Gamma a) + l * Real.log a) := by
        apply Real.exp_le_exp.mpr hlog
    _ = Gamma a * Real.exp (l * Real.log a) := by
        rw [Real.exp_add, Real.exp_log hGa]

/-- **Wendel's lower bound** (paper Lemma 16(ii)): `Γ(a) · (a+λ-1)^λ ≤ Γ(a+λ)`
for `a + λ > 1`, from log-convexity of `Γ`. -/
lemma le_Gamma_add (hl0 : 0 < l) (hl1 : l < 1) {a : ℝ} (ha1 : 1 < a + l) :
    Gamma a * (a + l - 1) ^ l ≤ Gamma (a + l) := by
  have hb : (0 : ℝ) < a + l - 1 := by linarith
  have ha : (0 : ℝ) < a := by linarith
  have hGa := Real.Gamma_pos_of_pos ha
  have hGb := Real.Gamma_pos_of_pos hb
  have hGal := Real.Gamma_pos_of_pos (show (0:ℝ) < a + l by linarith)
  set F : ℝ → ℝ := fun x => Real.log (Gamma x) with hF
  have hconv : ConvexOn ℝ (Set.Ioi 0) F := Real.convexOn_log_Gamma
  -- a = λ·(a+λ-1) + (1-λ)·(a+λ)
  have hcomb : l * (a + l - 1) + (1 - l) * (a + l) = a := by ring
  have hc := hconv.2 (show (a + l - 1) ∈ Set.Ioi (0:ℝ) from hb)
    (show (a + l) ∈ Set.Ioi (0:ℝ) by simp only [Set.mem_Ioi]; linarith)
    (le_of_lt hl0) (by linarith : (0:ℝ) ≤ 1 - l) (by ring : l + (1 - l) = 1)
  simp only [smul_eq_mul, hcomb] at hc
  -- hc : F a ≤ l F(a+λ-1) + (1-l) F(a+λ)
  have hstep : Gamma (a + l) = (a + l - 1) * Gamma (a + l - 1) := by
    rw [← Real.Gamma_add_one (ne_of_gt hb)]; congr 1; ring
  have hGbeq : Real.log (Gamma (a + l - 1)) = Real.log (Gamma (a + l)) - Real.log (a + l - 1) := by
    rw [hstep, Real.log_mul (ne_of_gt hb) (ne_of_gt hGb)]; ring
  have hlog : Real.log (Gamma a) ≤ Real.log (Gamma (a + l)) - l * Real.log (a + l - 1) := by
    simp only [hF] at hc
    rw [hGbeq] at hc
    nlinarith [hc]
  have hrpow : (a + l - 1) ^ l = Real.exp (l * Real.log (a + l - 1)) := by
    rw [Real.rpow_def_of_pos hb]; ring_nf
  rw [hrpow]
  rw [← Real.exp_log hGa, ← Real.exp_log hGal, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [hlog]

/-- Decay bound (paper Lemma 16(iii)): `gx λ m ≤ m^{λ-1} / Γ(λ)` for `m ≥ 1`. -/
lemma gx_le_rpow (hl0 : 0 < l) (hl1 : l < 1) {m : ℕ} (hm : 1 ≤ m) :
    gx l m ≤ (m : ℝ) ^ (l - 1) / Gamma l := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hGl := Real.Gamma_pos_of_pos hl0
  have hGm := Real.Gamma_pos_of_pos hmpos
  have hΓm1 : Gamma ((m : ℝ) + 1) = (m : ℝ) * Gamma (m : ℝ) := Real.Gamma_add_one (ne_of_gt hmpos)
  have hW := Gamma_add_le l hl0 hl1 hmpos   -- Γ(m+l) ≤ Γm * m^l
  have hrpow : (m : ℝ) ^ (l - 1) * (m : ℝ) = (m : ℝ) ^ l := by
    calc (m : ℝ) ^ (l - 1) * (m : ℝ)
        = (m : ℝ) ^ (l - 1) * (m : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (m : ℝ) ^ ((l - 1) + 1) := (Real.rpow_add hmpos _ _).symm
      _ = (m : ℝ) ^ l := by rw [show (l - 1) + 1 = l by ring]
  rw [gx_eq_Gamma l hl0 m, hΓm1, div_le_div_iff₀ (by positivity) hGl]
  have key : (m : ℝ) ^ (l - 1) * (Gamma l * ((m : ℝ) * Gamma (m : ℝ)))
      = Gamma l * Gamma (m : ℝ) * (m : ℝ) ^ l := by rw [← hrpow]; ring
  rw [key]
  calc Gamma ((m : ℝ) + l) * Gamma l
      ≤ (Gamma (m : ℝ) * (m : ℝ) ^ l) * Gamma l := mul_le_mul_of_nonneg_right hW (le_of_lt hGl)
    _ = Gamma l * Gamma (m : ℝ) * (m : ℝ) ^ l := by ring

/-- `gx λ` is antitone (nonincreasing) for `0 < λ < 1`. -/
lemma gx_antitone (hl0 : 0 < l) (hl1 : l < 1) : Antitone (gx l) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [gx_succ]
  have hpos := gx_pos l hl0 m
  have hfrac : ((m : ℝ) + l) / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  nlinarith [hpos, hfrac]

/-- `gx λ (i + j) ≤ gx λ j` (used as the dominating envelope). -/
lemma gx_add_le (hl0 : 0 < l) (hl1 : l < 1) (i j : ℕ) : gx l (i + j) ≤ gx l j :=
  gx_antitone l hl0 hl1 (by omega : j ≤ i + j)

/-- `gx λ` is square-summable for `0 < λ < 1/2`. -/
lemma gx_sq_summable (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    Summable (fun j => (gx l j) ^ 2) := by
  have hl1' : l < 1 := by linarith
  have hGl := Real.Gamma_pos_of_pos hl0
  have hp : (1 : ℝ) < 2 - 2 * l := by linarith
  -- summable p-series with p = 2 - 2λ > 1, shifted by 1
  have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 - 2 * l)) :=
    summable_one_div_nat_rpow.mpr hp
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 - 2 * l)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hps.comp_injective (add_left_injective 1)
  have hbound : Summable (fun j : ℕ => (1 / Gamma l) ^ 2 * (1 / ((j : ℝ) + 1) ^ (2 - 2 * l))) :=
    hshift.mul_left _
  -- prove summability of the shifted square sequence by comparison
  refine Summable.comp_nat_add (k := 1) ?_
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hbound
  have hj1 : 1 ≤ j + 1 := by omega
  have hjr : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hb := gx_le_rpow l hl0 hl1' hj1
  rw [Nat.cast_add, Nat.cast_one] at hb   -- gx l (j+1) ≤ ((j:ℝ)+1)^(l-1)/Γl
  have hgxnn : 0 ≤ gx l (j + 1) := (gx_pos l hl0 _).le
  have hsq : (gx l (j + 1)) ^ 2 ≤ (((j : ℝ) + 1) ^ (l - 1) / Gamma l) ^ 2 := by
    apply sq_le_sq'
    · linarith [hgxnn, hb, div_nonneg (Real.rpow_nonneg hjr.le (l - 1)) hGl.le]
    · exact hb
  refine hsq.trans (le_of_eq ?_)
  have hA2 : (((j : ℝ) + 1) ^ (l - 1)) ^ 2 = 1 / ((j : ℝ) + 1) ^ (2 - 2 * l) := by
    rw [pow_two, ← Real.rpow_add hjr,
      eq_div_iff (by positivity : ((j : ℝ) + 1) ^ (2 - 2 * l) ≠ 0), ← Real.rpow_add hjr,
      show (l - 1) + (l - 1) + (2 - 2 * l) = 0 by ring, Real.rpow_zero]
  rw [div_pow, hA2]
  field_simp

/-! ### The Γ form of `M`, its monotonicity in `n`, and the uniform envelope -/

/-- `M l n i j` in closed Γ form: a constant times `Γ(n+l)/Γ(n) · Γ(n-k-l)/Γ(n-k)`
(paper Theorem `dom-gen`), the shape used for both the limit and monotonicity. -/
lemma M_gamma (hl0 : 0 < l) (hl1 : l < 1) {n i j : ℕ} (h : i + j < n) :
    M l n i j = (Real.sin (π * l) / π) * (1 / (((i + j : ℕ) : ℝ) + l))
      * (Gamma ((n : ℝ) + l) / Gamma (n : ℝ)
        * (Gamma ((n : ℝ) - ((i + j : ℕ) : ℝ) - l) / Gamma ((n : ℝ) - ((i + j : ℕ) : ℝ)))) := by
  have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hknk : ((i + j : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : (i + j) + 1 ≤ n)
  have h1l : (0 : ℝ) < 1 - l := by linarith
  have hN : (0 : ℝ) < (n : ℝ) := by linarith
  have hNK : (0 : ℝ) < (n : ℝ) - ((i + j : ℕ) : ℝ) := by linarith
  have hNKl : (0 : ℝ) < (n : ℝ) - ((i + j : ℕ) : ℝ) - l := by linarith
  have hN1l : (0 : ℝ) < (n : ℝ) - 1 + l := by linarith
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  have hc2 : ((n - 1 - (i + j) : ℕ) : ℝ) = (n : ℝ) - ((i + j : ℕ) : ℝ) - 1 := by
    rw [show n - 1 - (i + j) = n - ((i + j) + 1) by omega, Nat.cast_sub (by omega : (i + j) + 1 ≤ n)]
    push_cast; ring
  have hgxv : gx l (n - 1) = Gamma ((n : ℝ) - 1 + l) / (Gamma l * Gamma (n : ℝ)) := by
    rw [gx_eq_Gamma l hl0 (n - 1), show ((n - 1 : ℕ) : ℝ) + l = (n : ℝ) - 1 + l by rw [hc1],
      show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by rw [hc1]; ring]
  have hgyv : gy l (n - 1 - (i + j))
      = Gamma ((n : ℝ) - ((i + j : ℕ) : ℝ) - l)
          / (Gamma (1 - l) * Gamma ((n : ℝ) - ((i + j : ℕ) : ℝ))) := by
    rw [gy_eq_Gamma l hl1 (n - 1 - (i + j)),
      show ((n - 1 - (i + j) : ℕ) : ℝ) + 1 - l = (n : ℝ) - ((i + j : ℕ) : ℝ) - l by rw [hc2]; ring,
      show ((n - 1 - (i + j) : ℕ) : ℝ) + 1 = (n : ℝ) - ((i + j : ℕ) : ℝ) by rw [hc2]; ring]
  have hne : ((n : ℝ) - 1 + l) ≠ 0 := ne_of_gt hN1l
  have he : Gamma ((n : ℝ) + l) = ((n : ℝ) - 1 + l) * Gamma ((n : ℝ) - 1 + l) := by
    rw [← Real.Gamma_add_one hne]; congr 1; ring
  have gGl : Gamma l ≠ 0 := (Real.Gamma_pos_of_pos hl0).ne'
  have gG1l : Gamma (1 - l) ≠ 0 := (Real.Gamma_pos_of_pos h1l).ne'
  have gGN : Gamma (n : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hN).ne'
  have gGNK : Gamma ((n : ℝ) - ((i + j : ℕ) : ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos hNK).ne'
  have gGNKl : Gamma ((n : ℝ) - ((i + j : ℕ) : ℝ) - l) ≠ 0 := (Real.Gamma_pos_of_pos hNKl).ne'
  have hKl : ((i + j : ℕ) : ℝ) + l ≠ 0 := by positivity
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hrefl : Real.sin (π * l) / π = 1 / (Gamma l * Gamma (1 - l)) := by
    rw [Real.Gamma_mul_Gamma_one_sub l, one_div_div]
  rw [M_closed l hl0 hl1 h, hgxv, hgyv, he, hrefl]
  field_simp

/-- Boundary value: `M l (i+j+1) i j = gx l (i+j)` (paper: "taking `n=k+1`"). -/
lemma M_succ_eq (hl0 : 0 < l) (hl1 : l < 1) (i j : ℕ) : M l (i + j + 1) i j = gx l (i + j) := by
  rw [M_closed l hl0 hl1 (show i + j < i + j + 1 by omega),
    show i + j + 1 - 1 - (i + j) = 0 by omega, show i + j + 1 - 1 = i + j by omega, gy_zero,
    show ((i + j + 1 : ℕ) : ℝ) - 1 = ((i + j : ℕ) : ℝ) by push_cast; ring,
    div_self (by positivity : ((i + j : ℕ) : ℝ) + l ≠ 0), one_mul, one_mul]

/-- `M` is nonincreasing in `n` (paper: `R_{n+1}(k)/R_n(k) < 1`). -/
lemma M_step (hl0 : 0 < l) (hl1 : l < 1) (i j n : ℕ) (h : i + j < n) :
    M l (n + 1) i j ≤ M l n i j := by
  have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hknk : ((i + j : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : (i + j) + 1 ≤ n)
  have hN : (0 : ℝ) < (n : ℝ) := by linarith
  have hNK : (0 : ℝ) < (n : ℝ) - ((i + j : ℕ) : ℝ) := by linarith
  have hNKl : (0 : ℝ) < (n : ℝ) - ((i + j : ℕ) : ℝ) - l := by linarith
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  have hc2 : ((n - 1 - (i + j) : ℕ) : ℝ) = (n : ℝ) - ((i + j : ℕ) : ℝ) - 1 := by
    rw [show n - 1 - (i + j) = n - ((i + j) + 1) by omega, Nat.cast_sub (by omega : (i + j) + 1 ≤ n)]
    push_cast; ring
  -- closed forms
  have hMn := M_closed l hl0 hl1 h
  have hMn1 := M_closed l hl0 hl1 (show i + j < n + 1 by omega)
  rw [show n + 1 - 1 - (i + j) = n - (i + j) by omega, show n + 1 - 1 = n by omega,
    show ((n + 1 : ℕ) : ℝ) - 1 + l = (n : ℝ) + l by push_cast; ring] at hMn1
  have hNne : (n : ℝ) ≠ 0 := ne_of_gt hN
  have hNKne : (n : ℝ) - ((i + j : ℕ) : ℝ) ≠ 0 := ne_of_gt hNK
  have hKl : (0 : ℝ) < ((i + j : ℕ) : ℝ) + l := by positivity
  have hKlne : ((i + j : ℕ) : ℝ) + l ≠ 0 := ne_of_gt hKl
  -- gx, gy successor ratios
  have hgxn : gx l n = gx l (n - 1) * (((n : ℝ) - 1 + l) / (n : ℝ)) := by
    have hs := gx_succ l (n - 1)
    rw [show n - 1 + 1 = n by omega, hc1, show ((n : ℝ) - 1) + 1 = (n : ℝ) by ring] at hs
    exact hs
  have hgyn : gy l (n - (i + j))
      = gy l (n - 1 - (i + j)) * (((n : ℝ) - ((i + j : ℕ) : ℝ) - l) / ((n : ℝ) - ((i + j : ℕ) : ℝ))) := by
    have hs := gy_succ l (n - 1 - (i + j))
    rw [show n - 1 - (i + j) + 1 = n - (i + j) by omega, hc2,
      show ((n : ℝ) - ((i + j : ℕ) : ℝ) - 1) + 1 - l = (n : ℝ) - ((i + j : ℕ) : ℝ) - l by ring,
      show ((n : ℝ) - ((i + j : ℕ) : ℝ) - 1) + 1 = (n : ℝ) - ((i + j : ℕ) : ℝ) by ring] at hs
    exact hs
  rw [hMn1, hgxn, hgyn, hMn]
  have hG : 0 ≤ gy l (n - 1 - (i + j)) * gx l (n - 1) :=
    mul_nonneg (gy_pos l hl1 _).le (gx_pos l hl0 _).le
  have key : ((n : ℝ) + l) / (((i + j : ℕ) : ℝ) + l)
        * (gy l (n - 1 - (i + j)) * (((n : ℝ) - ((i + j : ℕ) : ℝ) - l) / ((n : ℝ) - ((i + j : ℕ) : ℝ)))
          * (gx l (n - 1) * (((n : ℝ) - 1 + l) / (n : ℝ))))
      = ((n : ℝ) - 1 + l) / (((i + j : ℕ) : ℝ) + l) * (gy l (n - 1 - (i + j)) * gx l (n - 1))
        * (((n : ℝ) + l) * ((n : ℝ) - ((i + j : ℕ) : ℝ) - l) / ((n : ℝ) * ((n : ℝ) - ((i + j : ℕ) : ℝ)))) := by
    field_simp
  rw [key]
  have hbase : 0 ≤ ((n : ℝ) - 1 + l) / (((i + j : ℕ) : ℝ) + l) * (gy l (n - 1 - (i + j)) * gx l (n - 1)) :=
    mul_nonneg (div_nonneg (by linarith) hKl.le) hG
  have hfac : ((n : ℝ) + l) * ((n : ℝ) - ((i + j : ℕ) : ℝ) - l)
      / ((n : ℝ) * ((n : ℝ) - ((i + j : ℕ) : ℝ))) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hKl, hNKl, hN, hNK]
  exact mul_le_of_le_one_right hbase hfac

/-- **Uniform envelope** (paper: `M_n[i,j] ≤ x_{i+j}`): the majorant entries are
bounded, uniformly in `n`, by the eigenvector. -/
lemma M_le_gx (hl0 : 0 < l) (hl1 : l < 1) (i j n : ℕ) : M l n i j ≤ gx l (i + j) := by
  rcases Nat.lt_or_ge (i + j) n with hn | hn
  · -- i+j < n: descend from M_{i+j+1} = gx_{i+j}
    have hmono : ∀ p, M l (i + j + 1 + p) i j ≤ M l (i + j + 1) i j := by
      intro p
      induction p with
      | zero => simp
      | succ q ih =>
        refine le_trans ?_ ih
        rw [show i + j + 1 + (q + 1) = (i + j + 1 + q) + 1 by ring]
        exact M_step l hl0 hl1 i j (i + j + 1 + q) (by omega)
    have hp : n = i + j + 1 + (n - (i + j + 1)) := by omega
    rw [hp]
    exact (hmono (n - (i + j + 1))).trans (le_of_eq (M_succ_eq l hl0 hl1 i j))
  · rw [M_eq_zero l hn]; exact (gx_pos l hl0 _).le

/-! ### The pointwise limit of `M` in `n` -/

open Filter Topology

/-- The Γ-ratio `R_n(K) → 1` as `n → ∞` (paper: Wendel squeeze). -/
lemma Rn_tendsto (hl0 : 0 < l) (hl1 : l < 1) (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun n : ℕ => Gamma ((n : ℝ) + l) / Gamma (n : ℝ)
      * (Gamma ((n : ℝ) - K - l) / Gamma ((n : ℝ) - K))) atTop (𝓝 1) := by
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- the upper envelope (N/(N-K-1))^l tends to 1
  have hUlim : Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) - K - 1)) ^ l) atTop (𝓝 1) := by
    have hd : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - K - 1)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => (K + 1) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (K + 1)
      have h1 : Tendsto (fun n : ℕ => 1 - (K + 1) / (n : ℝ)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub h0
      rw [sub_zero] at h1
      have h1' := h1.inv₀ (by norm_num)
      rw [inv_one] at h1'
      refine h1'.congr' ?_
      filter_upwards [hNat.eventually (eventually_gt_atTop (K + 1))] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnz : (n : ℝ) ≠ 0 := hnpos.ne'
      rw [show (1 : ℝ) - (K + 1) / (n : ℝ) = ((n : ℝ) - K - 1) / (n : ℝ) by field_simp; ring,
        inv_div]
    have hcont : ContinuousAt (fun x : ℝ => x ^ l) 1 :=
      Real.continuousAt_rpow_const 1 l (Or.inl one_ne_zero)
    simpa only [Function.comp_def, Real.one_rpow] using hcont.tendsto.comp hd
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUlim ?_ ?_
  · -- eventually 1 ≤ Rn
    filter_upwards [hNat.eventually (eventually_gt_atTop (K + 1))] with n hn
    have hN : (0 : ℝ) < (n : ℝ) := by linarith
    have hNK : (0 : ℝ) < (n : ℝ) - K := by linarith
    have hNKl : (0 : ℝ) < (n : ℝ) - K - l := by linarith
    rw [div_mul_div_comm, one_le_div (by positivity)]
    have hg := g_mono l hl0 (a := (n : ℝ) - K - l) (b := (n : ℝ)) hNKl (by linarith)
    rw [show (n : ℝ) - K - l + l = (n : ℝ) - K by ring,
      div_le_div_iff₀ (by positivity) (by positivity)] at hg
    nlinarith [hg]
  · -- eventually Rn ≤ envelope
    filter_upwards [hNat.eventually (eventually_gt_atTop (K + 2))] with n hn
    have hN : (0 : ℝ) < (n : ℝ) := by linarith
    have hNK : (0 : ℝ) < (n : ℝ) - K := by linarith
    have hNKl : (0 : ℝ) < (n : ℝ) - K - l := by linarith
    have hNK1 : (0 : ℝ) < (n : ℝ) - K - 1 := by linarith
    have hGN := Real.Gamma_pos_of_pos hN
    have hGNK := Real.Gamma_pos_of_pos hNK
    have hA : Gamma ((n : ℝ) + l) / Gamma (n : ℝ) ≤ (n : ℝ) ^ l := by
      rw [div_le_iff₀ hGN, mul_comm]; exact Gamma_add_le l hl0 hl1 hN
    have hB : Gamma ((n : ℝ) - K - l) / Gamma ((n : ℝ) - K) ≤ 1 / ((n : ℝ) - K - 1) ^ l := by
      have hW := le_Gamma_add l hl0 hl1 (a := (n : ℝ) - K - l) (by linarith : 1 < (n : ℝ) - K - l + l)
      rw [show (n : ℝ) - K - l + l = (n : ℝ) - K by ring] at hW
      rw [div_le_div_iff₀ hGNK (by positivity), one_mul]; exact hW
    calc Gamma ((n : ℝ) + l) / Gamma (n : ℝ) * (Gamma ((n : ℝ) - K - l) / Gamma ((n : ℝ) - K))
        ≤ (n : ℝ) ^ l * (1 / ((n : ℝ) - K - 1) ^ l) :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = ((n : ℝ) / ((n : ℝ) - K - 1)) ^ l := by
          rw [Real.div_rpow hN.le hNK1.le, mul_one_div]

/-- **Pointwise limit** (paper Theorem `dom-gen`, tail): the majorant entries
decrease to the Hilbert entries. -/
lemma M_tendsto (hl0 : 0 < l) (hl1 : l < 1) (i j : ℕ) :
    Tendsto (fun n => M l n i j) atTop
      (𝓝 ((Real.sin (π * l) / π) * (1 / (((i + j : ℕ) : ℝ) + l)))) := by
  have hR := Rn_tendsto l hl0 hl1 ((i + j : ℕ) : ℝ) (by positivity)
  have hLR := hR.const_mul ((Real.sin (π * l) / π) * (1 / (((i + j : ℕ) : ℝ) + l)))
  rw [mul_one] at hLR
  refine hLR.congr' ?_
  filter_upwards [eventually_gt_atTop (i + j)] with n hn
  exact (M_gamma l hl0 hl1 hn).symm

/-! ### The eigenvector identity on `ℓ²` (paper Proposition `exact-eig`) -/

/-- **Exact eigenvector identity**: for `0 < λ < 1/2`,
`∑' j, gx_j / (i+j+λ) = (π/sin πλ) gx_i`. -/
lemma eigen_identity (hl0 : 0 < l) (hl1 : l < 1 / 2) (i : ℕ) :
    ∑' j, gx l j / ((i : ℝ) + (j : ℝ) + l) = (π / Real.sin (π * l)) * gx l i := by
  have hl1' : l < 1 := by linarith
  have hsin : Real.sin (π * l) ≠ 0 := (sin_pi_mul_pos l hl0 hl1').ne'
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  set c := Real.sin (π * l) / π with hc
  set g : ℕ → ℝ := fun j => c * (1 / ((i : ℝ) + (j : ℝ) + l)) * gx l j with hgdef
  have hsum := gx_sq_summable l hl0 hl1
  have hab : ∀ j, Tendsto (fun n => M l n i j * gx l j) atTop (𝓝 (g j)) := by
    intro j
    have hM := M_tendsto l hl0 hl1' i j
    rw [show (((i + j : ℕ) : ℝ) + l) = ((i : ℝ) + (j : ℝ) + l) by push_cast; ring] at hM
    simpa only [hgdef, hc] using hM.mul_const (gx l j)
  have hbound : ∀ᶠ n in atTop, ∀ j, ‖M l n i j * gx l j‖ ≤ (gx l j) ^ 2 := by
    refine Filter.Eventually.of_forall (fun n j => ?_)
    have hpos : 0 ≤ M l n i j * gx l j :=
      mul_nonneg (M_nonneg l hl0 hl1' n i j) (gx_pos l hl0 j).le
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    have h1 : M l n i j ≤ gx l j := (M_le_gx l hl0 hl1' i j n).trans (gx_add_le l hl0 hl1' i j)
    calc M l n i j * gx l j ≤ gx l j * gx l j :=
          mul_le_mul_of_nonneg_right h1 (gx_pos l hl0 j).le
      _ = (gx l j) ^ 2 := (pow_two _).symm
  have hT := tendsto_tsum_of_dominated_convergence hsum hab hbound
  have hpartial : ∀ n, i < n → ∑' j, M l n i j * gx l j = gx l i := by
    intro n hn
    rw [tsum_eq_sum (s := range n) (fun j hj => ?_)]
    · exact eig l n i hn
    · have hjn : n ≤ j := by simpa using hj
      rw [M_eq_zero l (by omega : n ≤ i + j), zero_mul]
  have hlim2 : Tendsto (fun n => ∑' j, M l n i j * gx l j) atTop (𝓝 (gx l i)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop i] with n hn
    exact (hpartial n hn).symm
  have hgi : ∑' j, g j = gx l i := tendsto_nhds_unique hT hlim2
  have hg_eq : ∑' j, g j = c * ∑' j, gx l j / ((i : ℝ) + (j : ℝ) + l) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun j => by rw [hgdef]; ring)
  rw [hg_eq] at hgi
  rw [← hgi, ← mul_assoc, hc, div_mul_div_comm,
    mul_comm π (Real.sin (π * l)), div_self (mul_ne_zero hsin hpi), one_mul]

/-! ### The norm is attained (paper Proposition `exact-eig`, conclusion) -/

/-- The double series `∑ gx_i gx_j /(i+j+λ)` is summable for `0 < λ < 1/2`. -/
lemma gx_double_summable (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    Summable (fun q : ℕ × ℕ => gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l)) := by
  have hl1' : l < 1 := by linarith
  have hsinpos := sin_pi_mul_pos l hl0 hl1'
  have hθ : 0 < π / Real.sin (π * l) := div_pos Real.pi_pos hsinpos
  have hsq := gx_sq_summable l hl0 hl1
  have hfnn : ∀ q : ℕ × ℕ, 0 ≤ gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l) := fun q =>
    div_nonneg (mul_nonneg (gx_pos l hl0 _).le (gx_pos l hl0 _).le)
      (le_of_lt (show (0:ℝ) < (q.1 : ℝ) + (q.2 : ℝ) + l by positivity))
  refine summable_of_sum_le (c := (π / Real.sin (π * l)) * ∑' i, (gx l i) ^ 2) hfnn (fun s => ?_)
  set N : ℕ := 1 + s.sup (fun q => max q.1 q.2) with hN
  have hsub : s ⊆ Finset.range N ×ˢ Finset.range N := by
    intro q hq
    have h1 : q.1 ≤ s.sup (fun q => max q.1 q.2) :=
      le_trans (le_max_left _ _) (Finset.le_sup (f := fun q => max q.1 q.2) hq)
    have h2 : q.2 ≤ s.sup (fun q => max q.1 q.2) :=
      le_trans (le_max_right _ _) (Finset.le_sup (f := fun q => max q.1 q.2) hq)
    simp only [Finset.mem_product, Finset.mem_range]; omega
  have hsqnn : (0 : ℝ) ≤ ∑ i ∈ range N, (gx l i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ∑ q ∈ s, gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l)
      ≤ ∑ q ∈ Finset.range N ×ˢ Finset.range N, gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hfnn q
    _ = ∑ i ∈ range N, ∑ j ∈ range N, gx l i * gx l j / ((i : ℝ) + (j : ℝ) + l) := by
        rw [Finset.sum_product]
    _ ≤ (π / Real.sin (π * l)) * Real.sqrt (∑ i ∈ range N, (gx l i) ^ 2)
          * Real.sqrt (∑ j ∈ range N, (gx l j) ^ 2) :=
        schur_inequality_finite l hl0 hl1' N (gx l) (gx l)
    _ = (π / Real.sin (π * l)) * ∑ i ∈ range N, (gx l i) ^ 2 := by
        rw [mul_assoc, Real.mul_self_sqrt hsqnn]
    _ ≤ (π / Real.sin (π * l)) * ∑' i, (gx l i) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hθ.le
        exact Summable.sum_le_tsum _ (fun i _ => sq_nonneg _) hsq

/-- **The norm is attained** (paper Proposition `exact-eig`): the Rayleigh quotient
of `H_λ` at the eigenvector `gx λ` equals `π csc(πλ)`. -/
lemma rayleigh (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    ∑' q : ℕ × ℕ, gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l)
      = (π / Real.sin (π * l)) * ∑' i, (gx l i) ^ 2 := by
  have hds := gx_double_summable l hl0 hl1
  rw [Summable.tsum_prod' hds (fun i => hds.prod_factor i)]
  calc ∑' i, ∑' j, gx l i * gx l j / ((i : ℝ) + (j : ℝ) + l)
      = ∑' i, gx l i * (∑' j, gx l j / ((i : ℝ) + (j : ℝ) + l)) := by
        refine tsum_congr (fun i => ?_)
        simp_rw [mul_div_assoc]
        rw [tsum_mul_left]
    _ = ∑' i, (π / Real.sin (π * l)) * (gx l i) ^ 2 := by
        refine tsum_congr (fun i => ?_)
        rw [eigen_identity l hl0 hl1 i]; ring
    _ = (π / Real.sin (π * l)) * ∑' i, (gx l i) ^ 2 := tsum_mul_left

/-- **Sharpness of Schur's bound** (paper Section 5): for `0 < λ < 1/2` the
constant `π csc(πλ)` is attained — the square-summable eigenvector `gx λ` (which
is nonzero) realizes the Rayleigh quotient `π csc(πλ)`. Together with
`schur_inequality_finite` this shows `π csc(πλ)` is the exact operator norm. -/
theorem schur_norm_attained (hl0 : 0 < l) (hl1 : l < 1 / 2) :
    (∑' q : ℕ × ℕ, gx l q.1 * gx l q.2 / ((q.1 : ℝ) + (q.2 : ℝ) + l))
        = (π / Real.sin (π * l)) * ∑' i, (gx l i) ^ 2
      ∧ 0 < ∑' i, (gx l i) ^ 2 :=
  by
  refine ⟨rayleigh l hl0 hl1, ?_⟩
  have h1 := Summable.sum_le_tsum ({0} : Finset ℕ) (fun i _ => sq_nonneg (gx l i))
    (gx_sq_summable l hl0 hl1)
  rw [Finset.sum_singleton, gx_zero] at h1
  norm_num at h1
  linarith

end HilbertPi.General
