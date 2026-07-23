/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.EigenMatrix

/-!
# Entrywise domination for general `λ` (paper Theorem 8 / Section 4)

`T l n` is the half-Hilbert matrix with parameter `λ = l`: entries
`1/(i+j+l)` above the anti-diagonal, `0` below.  Using the Γ closed forms of
`gx`, `gy`, Euler's reflection formula, and the log-convexity monotonicity
`g_mono`, we prove `T l n i j ≤ (π / sin(π l)) * M l n i j` entrywise, and the
row bound `∑_j T l n i j * gx j ≤ (π / sin(π l)) * gx i`.
-/

namespace HilbertPi.General

open Real Finset

variable (l : ℝ)

/-- The half-Hilbert matrix with parameter `l` (paper eq. (3)). -/
noncomputable def T (n i j : ℕ) : ℝ :=
  if i + j < n then 1 / (((i : ℝ) + (j : ℝ)) + l) else 0

lemma T_nonneg (hl0 : 0 < l) (n i j : ℕ) : 0 ≤ T l n i j := by
  unfold T
  split
  · positivity
  · exact le_rfl

lemma T_symm (n i j : ℕ) : T l n i j = T l n j i := by
  unfold T
  rw [add_comm i j, add_comm (i : ℝ) (j : ℝ)]

/-- `sin (π l) > 0` for `0 < l < 1`. -/
lemma sin_pi_mul_pos (hl0 : 0 < l) (hl1 : l < 1) : 0 < Real.sin (π * l) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

/-- Core inequality (paper Theorem 8): `1/(k+l) ≤ Γ(l) Γ(1-l) * (A n k - A n (k+1))`
for `k < n`, where `Γ(l) Γ(1-l) = π/sin(π l)`. -/
lemma dom_core (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ} (hk : k < n) :
    1 / ((k : ℝ) + l) ≤ Gamma l * Gamma (1 - l) * (A l n k - A l n (k + 1)) := by
  have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hknk : ((k : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ n)
  have h1l : (0 : ℝ) < 1 - l := by linarith
  -- positivity of the relevant Γ arguments
  have hNK : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by linarith
  have hNKl : (0 : ℝ) < (n : ℝ) - (k : ℝ) - l := by linarith
  have hN : (0 : ℝ) < (n : ℝ) := by linarith
  have hN1l : (0 : ℝ) < (n : ℝ) - 1 + l := by linarith
  -- Nat casts
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  have hc2 : ((n - 1 - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
    rw [show n - 1 - k = n - (k + 1) by omega, Nat.cast_sub (by omega : k + 1 ≤ n)]
    push_cast; ring
  -- Γ closed forms with rewritten arguments
  have hgxv : gx l (n - 1) = Gamma ((n : ℝ) - 1 + l) / (Gamma l * Gamma (n : ℝ)) := by
    rw [gx_eq_Gamma l hl0 (n - 1),
      show ((n - 1 : ℕ) : ℝ) + l = (n : ℝ) - 1 + l by rw [hc1],
      show ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) by rw [hc1]; ring]
  have hgyv : gy l (n - 1 - k)
      = Gamma ((n : ℝ) - (k : ℝ) - l) / (Gamma (1 - l) * Gamma ((n : ℝ) - (k : ℝ))) := by
    rw [gy_eq_Gamma l hl1 (n - 1 - k),
      show ((n - 1 - k : ℕ) : ℝ) + 1 - l = (n : ℝ) - (k : ℝ) - l by rw [hc2]; ring,
      show ((n - 1 - k : ℕ) : ℝ) + 1 = (n : ℝ) - (k : ℝ) by rw [hc2]; ring]
  -- functional equation
  have hne : ((n : ℝ) - 1 + l) ≠ 0 := ne_of_gt hN1l
  have he : Gamma ((n : ℝ) + l) = ((n : ℝ) - 1 + l) * Gamma ((n : ℝ) - 1 + l) := by
    rw [show (n : ℝ) + l = ((n : ℝ) - 1 + l) + 1 by ring, Real.Gamma_add_one hne]
  -- nonvanishing
  have gGl : Gamma l ≠ 0 := (Real.Gamma_pos_of_pos hl0).ne'
  have gG1l : Gamma (1 - l) ≠ 0 := (Real.Gamma_pos_of_pos h1l).ne'
  have gGN : Gamma (n : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hN).ne'
  have gGNK : Gamma ((n : ℝ) - (k : ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos hNK).ne'
  have gGNKl : Gamma ((n : ℝ) - (k : ℝ) - l) ≠ 0 := (Real.Gamma_pos_of_pos hNKl).ne'
  have hKl : (0 : ℝ) < (k : ℝ) + l := by positivity
  -- the master identity
  have hprod : Gamma l * Gamma (1 - l) * (A l n k - A l n (k + 1)) * ((k : ℝ) + l)
      = (Gamma ((n : ℝ) + l) / Gamma (n : ℝ))
          / (Gamma ((n : ℝ) - (k : ℝ)) / Gamma ((n : ℝ) - (k : ℝ) - l)) := by
    rw [A_sub_A l hl0 hl1 hk, hgyv, hgxv, he]
    field_simp
  -- the ratio is at least 1, by monotonicity of g
  have hRn : (1 : ℝ) ≤ (Gamma ((n : ℝ) + l) / Gamma (n : ℝ))
      / (Gamma ((n : ℝ) - (k : ℝ)) / Gamma ((n : ℝ) - (k : ℝ) - l)) := by
    rw [one_le_div (by positivity)]
    have hg := g_mono l hl0 (a := (n : ℝ) - (k : ℝ) - l) (b := (n : ℝ)) hNKl (by linarith)
    rwa [show (n : ℝ) - (k : ℝ) - l + l = (n : ℝ) - (k : ℝ) by ring] at hg
  -- assemble
  rw [div_le_iff₀ hKl, hprod]
  exact hRn

/-- **Entrywise domination** (paper Theorem 8): `T l n i j ≤ (π/sin(πl)) * M l n i j`. -/
lemma T_le (hl0 : 0 < l) (hl1 : l < 1) (n i j : ℕ) :
    T l n i j ≤ (π / Real.sin (π * l)) * M l n i j := by
  have hrefl : π / Real.sin (π * l) = Gamma l * Gamma (1 - l) :=
    (Real.Gamma_mul_Gamma_one_sub l).symm
  rcases lt_or_ge (i + j) n with h | h
  · have hcore := dom_core l hl0 hl1 (k := i + j) h
    have hcast : ((i + j : ℕ) : ℝ) = (i : ℝ) + (j : ℝ) := by push_cast; ring
    rw [hcast] at hcore
    rw [show T l n i j = 1 / (((i : ℝ) + (j : ℝ)) + l) by rw [T, if_pos h], M, hrefl]
    exact hcore
  · rw [show T l n i j = 0 by rw [T, if_neg (by omega)], M_eq_zero l h, mul_zero]

/-- **Row bound**: `∑_j T l n i j * gx j ≤ (π/sin(πl)) * gx i` for every `i`. -/
lemma T_row_bound (hl0 : 0 < l) (hl1 : l < 1) (n i : ℕ) :
    ∑ j ∈ range n, T l n i j * gx l j ≤ (π / Real.sin (π * l)) * gx l i := by
  have hθ : 0 < π / Real.sin (π * l) := by
    have := sin_pi_mul_pos l hl0 hl1
    positivity
  rcases lt_or_ge i n with hi | hi
  · calc ∑ j ∈ range n, T l n i j * gx l j
        ≤ ∑ j ∈ range n, (π / Real.sin (π * l)) * M l n i j * gx l j := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (T_le l hl0 hl1 n i j) (gx_pos l hl0 j).le
      _ = (π / Real.sin (π * l)) * ∑ j ∈ range n, M l n i j * gx l j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = (π / Real.sin (π * l)) * gx l i := by rw [eig l n i hi]
  · have hz : ∀ j ∈ range n, T l n i j * gx l j = 0 := by
      intro j _
      rw [show T l n i j = 0 by rw [T, if_neg (by omega)], zero_mul]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    have := gx_pos l hl0 i
    positivity

end HilbertPi.General
