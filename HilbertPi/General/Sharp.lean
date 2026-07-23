/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.Domination
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery

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

end HilbertPi.General
