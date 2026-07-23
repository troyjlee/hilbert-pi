/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The two sequences for general `λ` (paper Section 4)

For `0 < l < 1` we define
`gx i = ∏_{t<i} (t+l)/(t+1)  =  Γ(i+l)/(Γ(l) Γ(i+1))`
and
`gy i = ∏_{t<i} (t+1-l)/(t+1)  =  Γ(i+1-l)/(Γ(1-l) Γ(i+1))`,
prove their ratio identities, positivity, the Γ closed forms, and the
monotonicity of `g(a) = Γ(a+l)/Γ(a)` (from log-convexity of `Γ`).  These
replace the central-binomial/Wallis facts of the `λ = 1/2` warm-up.
-/

namespace HilbertPi.General

open Real Finset

variable (l : ℝ)

/-- The eigenvector sequence `gx i = ∏_{t<i} (t+l)/(t+1)`. -/
noncomputable def gx (i : ℕ) : ℝ := ∏ t ∈ range i, ((t : ℝ) + l) / ((t : ℝ) + 1)

/-- The dual sequence `gy i = ∏_{t<i} (t+1-l)/(t+1)`. -/
noncomputable def gy (i : ℕ) : ℝ := ∏ t ∈ range i, ((t : ℝ) + 1 - l) / ((t : ℝ) + 1)

lemma gx_zero : gx l 0 = 1 := by simp [gx]
lemma gy_zero : gy l 0 = 1 := by simp [gy]

/-- Ratio identity for `gx` (paper eq. (14)). -/
lemma gx_succ (i : ℕ) : gx l (i + 1) = gx l i * (((i : ℝ) + l) / ((i : ℝ) + 1)) := by
  rw [gx, gx, Finset.prod_range_succ]

/-- Ratio identity for `gy` (paper eq. (14)). -/
lemma gy_succ (i : ℕ) : gy l (i + 1) = gy l i * (((i : ℝ) + 1 - l) / ((i : ℝ) + 1)) := by
  rw [gy, gy, Finset.prod_range_succ]

lemma gx_pos (hl0 : 0 < l) (i : ℕ) : 0 < gx l i := by
  apply Finset.prod_pos
  intro t _
  have : (0 : ℝ) < (t : ℝ) + l := by positivity
  positivity

lemma gy_pos (hl1 : l < 1) (i : ℕ) : 0 < gy l i := by
  apply Finset.prod_pos
  intro t _
  have h1 : (0 : ℝ) < (t : ℝ) + 1 - l := by
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  positivity

/-- `(i+1) * gx (i+1) = (i+l) * gx i` — division-free ratio. -/
lemma succ_mul_gx_succ (i : ℕ) :
    ((i : ℝ) + 1) * gx l (i + 1) = ((i : ℝ) + l) * gx l i := by
  rw [gx_succ]
  have : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- `(i+1) * gy (i+1) = (i+1-l) * gy i` — division-free ratio. -/
lemma succ_mul_gy_succ (i : ℕ) :
    ((i : ℝ) + 1) * gy l (i + 1) = ((i : ℝ) + 1 - l) * gy l i := by
  rw [gy_succ]
  have : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- `gx i - gx (i+1) = (1-l)/(i+1) * gx i`, used in the closed form. -/
lemma gx_sub_gx_succ (i : ℕ) :
    gx l i - gx l (i + 1) = (1 - l) / ((i : ℝ) + 1) * gx l i := by
  rw [gx_succ]
  have : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp; ring

/-! ### Connection to the Γ function -/

/-- Pochhammer product: `(∏_{t<i} (t+c)) * Γ(c) = Γ(i+c)` for `c > 0`. -/
lemma prod_add_mul_Gamma (c : ℝ) (hc : 0 < c) (i : ℕ) :
    (∏ t ∈ range i, ((t : ℝ) + c)) * Gamma c = Gamma ((i : ℝ) + c) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have hne : ((n : ℝ) + c) ≠ 0 := by positivity
    have hstep : Gamma (((n : ℝ) + c) + 1) = ((n : ℝ) + c) * Gamma ((n : ℝ) + c) :=
      Real.Gamma_add_one hne
    calc (∏ t ∈ range n, ((t : ℝ) + c)) * ((n : ℝ) + c) * Gamma c
        = ((n : ℝ) + c) * ((∏ t ∈ range n, ((t : ℝ) + c)) * Gamma c) := by ring
      _ = ((n : ℝ) + c) * Gamma ((n : ℝ) + c) := by rw [ih]
      _ = Gamma (((n : ℝ) + c) + 1) := hstep.symm
      _ = Gamma (((n : ℝ) + 1) + c) := by ring_nf
      _ = Gamma (((n + 1 : ℕ) : ℝ) + c) := by push_cast; ring_nf

/-- `(∏_{t<i} (t+1)) = Γ(i+1)`. -/
lemma prod_add_one_eq_Gamma (i : ℕ) :
    (∏ t ∈ range i, ((t : ℝ) + 1)) = Gamma ((i : ℝ) + 1) := by
  have h := prod_add_mul_Gamma 1 (by norm_num) i
  rw [Real.Gamma_one, mul_one] at h
  rw [h]

/-- Γ closed form for `gx` (paper eq. (13)). -/
lemma gx_eq_Gamma (hl0 : 0 < l) (i : ℕ) :
    gx l i = Gamma ((i : ℝ) + l) / (Gamma l * Gamma ((i : ℝ) + 1)) := by
  have hp := prod_add_mul_Gamma l hl0 i
  have hq := prod_add_one_eq_Gamma i
  have hGl : Gamma l ≠ 0 := (Real.Gamma_pos_of_pos hl0).ne'
  rw [gx, Finset.prod_div_distrib, hq,
    show (∏ t ∈ range i, ((t : ℝ) + l)) = Gamma ((i : ℝ) + l) / Gamma l from by
      rw [eq_div_iff hGl]; exact hp, div_div]

/-- Γ closed form for `gy` (paper eq. (13)). -/
lemma gy_eq_Gamma (hl1 : l < 1) (i : ℕ) :
    gy l i = Gamma ((i : ℝ) + 1 - l) / (Gamma (1 - l) * Gamma ((i : ℝ) + 1)) := by
  have h1l : 0 < 1 - l := by linarith
  have hp := prod_add_mul_Gamma (1 - l) h1l i
  have hq := prod_add_one_eq_Gamma i
  have hGl : Gamma (1 - l) ≠ 0 := (Real.Gamma_pos_of_pos h1l).ne'
  have hcong : (∏ t ∈ range i, ((t : ℝ) + 1 - l))
      = (∏ t ∈ range i, ((t : ℝ) + (1 - l))) :=
    Finset.prod_congr rfl fun t _ => by ring
  rw [gy, Finset.prod_div_distrib, hq, hcong,
    show (∏ t ∈ range i, ((t : ℝ) + (1 - l))) = Gamma ((i : ℝ) + (1 - l)) / Gamma (1 - l) from by
      rw [eq_div_iff hGl]; exact hp,
    show (i : ℝ) + (1 - l) = (i : ℝ) + 1 - l by ring, div_div]

/-! ### Monotonicity of `g(a) = Γ(a+l)/Γ(a)` from log-convexity -/

/-- The increment `log Γ(a+l) - log Γ a` is nondecreasing in `a` (paper Lemma
16(i)); equivalently `g(a) = Γ(a+l)/Γ(a)` is nondecreasing. -/
lemma g_mono (hl0 : 0 < l) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Gamma (a + l) / Gamma a ≤ Gamma (b + l) / Gamma b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hGa := Real.Gamma_pos_of_pos ha
  have hGb := Real.Gamma_pos_of_pos hb
  have hGal := Real.Gamma_pos_of_pos (by linarith : (0:ℝ) < a + l)
  have hGbl := Real.Gamma_pos_of_pos (by linarith : (0:ℝ) < b + l)
  rcases eq_or_lt_of_le hab with hEq | hLt
  · rw [hEq]
  -- log-increment inequality
  set F : ℝ → ℝ := fun x => Real.log (Gamma x) with hF
  have hconv : ConvexOn ℝ (Set.Ioi 0) F := Real.convexOn_log_Gamma
  have hbal : 0 < b - a + l := by linarith
  set s : ℝ := l / (b - a + l) with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1 : 0 ≤ 1 - s := by
    rw [hs]; rw [sub_nonneg, div_le_one hbal]; linarith
  have hsum : (1 - s) + s = 1 := by ring
  have hne : (b - a + l) ≠ 0 := ne_of_gt hbal
  have hmemA : a ∈ Set.Ioi (0:ℝ) := ha
  have hmemBl : (b + l) ∈ Set.Ioi (0:ℝ) := by simp only [Set.mem_Ioi]; linarith
  have e1 : (1 - s) * a + s * (b + l) = a + l := by rw [hs]; field_simp; ring
  have e2 : s * a + (1 - s) * (b + l) = b := by rw [hs]; field_simp; ring
  have c1 := hconv.2 hmemA hmemBl hs1 hs0 hsum
  have c2 := hconv.2 hmemA hmemBl hs0 hs1 (by ring : s + (1 - s) = 1)
  simp only [smul_eq_mul, e1] at c1
  simp only [smul_eq_mul, e2] at c2
  -- c1 : F (a+l) ≤ (1-s) F a + s F (b+l)
  -- c2 : F b ≤ s F a + (1-s) F (b+l)
  have hincr : F (a + l) - F a ≤ F (b + l) - F b := by
    have := add_le_add c1 c2
    simp only [hF] at this ⊢
    nlinarith [this]
  -- convert increment inequality on logs to the ratio inequality
  have hla : Real.log (Gamma (a + l) / Gamma a) ≤ Real.log (Gamma (b + l) / Gamma b) := by
    rw [Real.log_div hGal.ne' hGa.ne', Real.log_div hGbl.ne' hGb.ne']
    simpa [hF] using hincr
  have hpos1 : 0 < Gamma (a + l) / Gamma a := by positivity
  have hpos2 : 0 < Gamma (b + l) / Gamma b := by positivity
  exact (Real.log_le_log_iff hpos1 hpos2).mp hla

end HilbertPi.General
