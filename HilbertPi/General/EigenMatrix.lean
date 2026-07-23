/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.General.Convolution

/-!
# The majorant matrix `M` and its eigenvector, general `λ` (paper Section 4)

Mirrors the `λ = 1/2` warm-up: correlation sums `A l n k = ∑_t gy t * gx (t+k)`,
the Hankel matrix `M l n i j = A l n (i+j) - A l n (i+j+1)`, the exact
eigenvector identity `M x = x`, the Gosper telescoping, and the closed form
`M l n i j = (n-1+l)/(k+l) * gy (n-1-k) * gx (n-1)`.
-/

namespace HilbertPi.General

open Finset

variable (l : ℝ)

/-- Truncated correlation sums (paper eq. (15)). -/
noncomputable def A (n k : ℕ) : ℝ := ∑ t ∈ range (n - k), gy l t * gx l (t + k)

/-- The majorant matrix (paper eq. (6)/(15)). -/
noncomputable def M (n i j : ℕ) : ℝ := A l n (i + j) - A l n (i + j + 1)

lemma A_eq_zero {n k : ℕ} (h : n ≤ k) : A l n k = 0 := by
  simp [A, Nat.sub_eq_zero_of_le h]

lemma M_eq_zero {n i j : ℕ} (h : n ≤ i + j) : M l n i j = 0 := by
  rw [M, A_eq_zero l h, A_eq_zero l (by omega), sub_zero]

/-- The row sums collapse to tail sums of `gx`, via the convolution identity. -/
lemma F_eq (n i : ℕ) :
    ∑ j ∈ range n, A l n (i + j) * gx l j = ∑ s ∈ range (n - i), gx l (s + i) := by
  have hL : ∑ j ∈ range n, A l n (i + j) * gx l j
      = ∑ j ∈ range n, ∑ t ∈ range (n - (i + j)),
          gy l t * gx l (t + (i + j)) * gx l j :=
    Finset.sum_congr rfl fun j _ => by rw [A, Finset.sum_mul]
  have hR : ∑ s ∈ range (n - i), gx l (s + i)
      = ∑ s ∈ range (n - i), ∑ c ∈ range (s + 1),
          gx l c * gy l (s - c) * gx l (s + i) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_mul, conv l s, one_mul]
  rw [hL, hR, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => ⟨p.1 + p.2, p.1⟩)
    (j := fun q => ⟨q.2, q.1 - q.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    have h1 : a < n := Finset.mem_range.mp (Finset.mem_sigma.mp hp).1
    have h2 : b < n - (i + a) := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (show a + b < n - i by omega),
        Finset.mem_range.mpr (show a < a + b + 1 by omega)⟩
  · rintro ⟨s, c⟩ hq
    have h1 : s < n - i := Finset.mem_range.mp (Finset.mem_sigma.mp hq).1
    have h2 : c < s + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (show c < n by omega),
        Finset.mem_range.mpr (show s - c < n - (i + c) by omega)⟩
  · rintro ⟨a, b⟩ _
    change (⟨a, a + b - a⟩ : Σ _ : ℕ, ℕ) = ⟨a, b⟩
    rw [show a + b - a = b by omega]
  · rintro ⟨s, c⟩ hq
    have h2 : c < s + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    change (⟨c + (s - c), c⟩ : Σ _ : ℕ, ℕ) = ⟨s, c⟩
    rw [show c + (s - c) = s by omega]
  · rintro ⟨a, b⟩ _
    change gy l b * gx l (b + (i + a)) * gx l a
      = gx l a * gy l (a + b - a) * gx l (a + b + i)
    rw [show a + b - a = b by omega, show b + (i + a) = a + b + i by omega]
    ring

/-- **Exact eigenvector identity** (paper Theorem 4, general `λ`). -/
theorem eig (n i : ℕ) (hi : i < n) :
    ∑ j ∈ range n, M l n i j * gx l j = gx l i := by
  have hsplit : ∑ j ∈ range n, M l n i j * gx l j
      = (∑ j ∈ range n, A l n (i + j) * gx l j)
        - ∑ j ∈ range n, A l n ((i + 1) + j) * gx l j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [M, show (i + 1) + j = i + j + 1 by omega]
    ring
  rw [hsplit, F_eq, F_eq]
  have hn : n - i = (n - (i + 1)) + 1 := by omega
  rw [hn, Finset.sum_range_succ' (fun s => gx l (s + i)) (n - (i + 1))]
  have hterm : ∀ s : ℕ, gx l (s + 1 + i) = gx l (s + (i + 1)) := by
    intro s; rw [show s + 1 + i = s + (i + 1) by omega]
  rw [Finset.sum_congr rfl fun s _ => hterm s]
  simp

/-- **Telescoping identity** (paper Lemma 6, general `λ`). -/
lemma gosper (hl0 : 0 < l) (hl1 : l < 1) (k T : ℕ) :
    ∑ t ∈ range T, gy l t * gx l (t + k) / ((t : ℝ) + k + 1)
      = (T : ℝ) * (gy l T * gx l (T + k)) / ((1 - l) * ((k : ℝ) + l)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have hgy : gy l (T + 1) = gy l T * (((T : ℝ) + 1 - l) / ((T : ℝ) + 1)) := gy_succ l T
    have hgx : gx l (T + 1 + k)
        = gx l (T + k) * (((T : ℝ) + (k : ℝ) + l) / ((T : ℝ) + (k : ℝ) + 1)) := by
      rw [show T + 1 + k = (T + k) + 1 by omega, gx_succ]
      push_cast; ring_nf
    rw [hgy, hgx]
    have c1 : (1 - l) ≠ 0 := by linarith
    have c2 : ((k : ℝ) + l) ≠ 0 := by positivity
    have c3 : ((T : ℝ) + (k : ℝ) + 1) ≠ 0 := by positivity
    have c4 : ((T : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **Closed form** (paper Corollary 7, general `λ`). -/
lemma A_sub_A (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ} (hk : k < n) :
    A l n k - A l n (k + 1)
      = ((n : ℝ) - 1 + l) / ((k : ℝ) + l) * (gy l (n - 1 - k) * gx l (n - 1)) := by
  have h1 : n - k = (n - k - 1) + 1 := by omega
  have h2 : n - (k + 1) = n - k - 1 := by omega
  have hidx : n - k - 1 + k = n - 1 := by omega
  have hidx2 : n - 1 - k = n - k - 1 := by omega
  have hcast : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
    rw [show n - k - 1 = n - (k + 1) by omega, Nat.cast_sub (by omega : k + 1 ≤ n)]
    push_cast; ring
  have hdiff : (∑ t ∈ range (n - k - 1), gy l t * gx l (t + k))
      - ∑ t ∈ range (n - k - 1), gy l t * gx l (t + (k + 1))
      = (1 - l) * ∑ t ∈ range (n - k - 1), gy l t * gx l (t + k) / ((t : ℝ) + k + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hx := gx_sub_gx_succ l (t + k)
    rw [show t + (k + 1) = (t + k) + 1 by omega]
    push_cast at hx
    calc gy l t * gx l (t + k) - gy l t * gx l ((t + k) + 1)
        = gy l t * (gx l (t + k) - gx l ((t + k) + 1)) := by ring
      _ = gy l t * ((1 - l) / ((t : ℝ) + (k : ℝ) + 1) * gx l (t + k)) := by rw [hx]
      _ = (1 - l) * (gy l t * gx l (t + k) / ((t : ℝ) + k + 1)) := by ring
  have hgosper := gosper l hl0 hl1 k (n - k - 1)
  rw [hidx, hcast] at hgosper
  rw [hgosper] at hdiff
  have c1 : (1 - l) ≠ 0 := by linarith
  have c2 : ((k : ℝ) + l) ≠ 0 := by positivity
  have hdiff2 : ((k : ℝ) + l) * ((∑ t ∈ range (n - k - 1), gy l t * gx l (t + k))
        - ∑ t ∈ range (n - k - 1), gy l t * gx l (t + (k + 1)))
      = ((n : ℝ) - (k : ℝ) - 1) * (gy l (n - k - 1) * gx l (n - 1)) := by
    rw [hdiff]; field_simp
  rw [A, A, h1, h2, Finset.sum_range_succ, hidx, hidx2]
  field_simp
  linear_combination hdiff2

/-- The closed form of the matrix entries above the anti-diagonal. -/
lemma M_closed (hl0 : 0 < l) (hl1 : l < 1) {n i j : ℕ} (h : i + j < n) :
    M l n i j = ((n : ℝ) - 1 + l) / (((i + j : ℕ) : ℝ) + l)
      * (gy l (n - 1 - (i + j)) * gx l (n - 1)) := by
  rw [M]; exact A_sub_A l hl0 hl1 h

lemma M_nonneg (hl0 : 0 < l) (hl1 : l < 1) (n i j : ℕ) : 0 ≤ M l n i j := by
  rcases lt_or_ge (i + j) n with h | h
  · rw [M_closed l hl0 hl1 h]
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 + l := by
      have : (1 : ℕ) ≤ n := by omega
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    have hk : (0 : ℝ) < ((i + j : ℕ) : ℝ) + l := by positivity
    have := gy_pos l hl1 (n - 1 - (i + j))
    have := gx_pos l hl0 (n - 1)
    positivity
  · rw [M_eq_zero l h]

end HilbertPi.General
