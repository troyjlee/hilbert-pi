/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import HilbertPi.Convolution

/-!
# The majorant matrix `M` and its exact eigenvector

Defines the correlation sums `A n k`, the Hankel matrix
`M n i j = A n (i+j) - A n (i+j+1)` (paper eq. (6)), and proves:

* `eig` (paper Theorem 4): `∑ j < n, M n i j * x j = x i` for `i < n`;
* `gosper` (paper Lemma 6): the telescoping closed form of
  `∑ t < T, x t * x (t+k) / (t+k+1)`;
* `M_closed` (paper Corollary 7): `M n i j = (2n-1)/(2k+1) * x (n-1) * x (n-1-k)`
  for `k = i + j ≤ n - 1`, and `M n i j = 0` below the anti-diagonal.
-/

namespace HilbertPi

open Finset

/-- Truncated correlation sums of the sequence `x` (paper eq. (5)). -/
noncomputable def A (n k : ℕ) : ℝ := ∑ t ∈ range (n - k), x t * x (t + k)

/-- The majorant matrix (paper eq. (6)): a Hankel matrix supported above the
anti-diagonal. -/
noncomputable def M (n i j : ℕ) : ℝ := A n (i + j) - A n (i + j + 1)

lemma A_eq_zero {n k : ℕ} (h : n ≤ k) : A n k = 0 := by
  simp [A, Nat.sub_eq_zero_of_le h]

lemma M_eq_zero {n i j : ℕ} (h : n ≤ i + j) : M n i j = 0 := by
  rw [M, A_eq_zero h, A_eq_zero (by omega), sub_zero]

/-- The row sums `F i = ∑ j < n, A n (i+j) * x j` collapse, via the
convolution identity, to tail sums of `x` (the computation inside paper
Theorem 4). -/
lemma F_eq (n i : ℕ) :
    ∑ j ∈ range n, A n (i + j) * x j = ∑ s ∈ range (n - i), x (s + i) := by
  have hL : ∑ j ∈ range n, A n (i + j) * x j
      = ∑ j ∈ range n, ∑ t ∈ range (n - (i + j)), x t * x (t + (i + j)) * x j :=
    Finset.sum_congr rfl fun j _ => by rw [A, Finset.sum_mul]
  have hR : ∑ s ∈ range (n - i), x (s + i)
      = ∑ s ∈ range (n - i), ∑ c ∈ range (s + 1), x c * x (s - c) * x (s + i) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_mul, conv s, one_mul]
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
  · rintro ⟨a, b⟩ hp
    change (⟨a, a + b - a⟩ : Σ _ : ℕ, ℕ) = ⟨a, b⟩
    rw [show a + b - a = b by omega]
  · rintro ⟨s, c⟩ hq
    have h2 : c < s + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    change (⟨c + (s - c), c⟩ : Σ _ : ℕ, ℕ) = ⟨s, c⟩
    rw [show c + (s - c) = s by omega]
  · rintro ⟨a, b⟩ hp
    change x b * x (b + (i + a)) * x a = x a * x (a + b - a) * x (a + b + i)
    rw [show a + b - a = b by omega, show b + (i + a) = a + b + i by omega]
    ring

/-- **Exact eigenvector identity** (paper Theorem 4): `M n x = x` on `range n`. -/
theorem eig (n i : ℕ) (hi : i < n) :
    ∑ j ∈ range n, M n i j * x j = x i := by
  have hsplit : ∑ j ∈ range n, M n i j * x j
      = (∑ j ∈ range n, A n (i + j) * x j)
        - ∑ j ∈ range n, A n ((i + 1) + j) * x j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [M, show (i + 1) + j = i + j + 1 by omega]
    ring
  rw [hsplit, F_eq, F_eq]
  have hn : n - i = (n - (i + 1)) + 1 := by omega
  rw [hn, Finset.sum_range_succ' (fun s => x (s + i)) (n - (i + 1))]
  have hterm : ∀ s : ℕ, x (s + 1 + i) = x (s + (i + 1)) := by
    intro s; rw [show s + 1 + i = s + (i + 1) by omega]
  rw [Finset.sum_congr rfl fun s _ => hterm s]
  simp

/-- **Telescoping identity** (paper Lemma 6):
`∑_{t<T} x t * x (t+k) / (t+k+1) = 4T/(2k+1) * x T * x (T+k)`. -/
lemma gosper (k T : ℕ) :
    ∑ t ∈ range T, x t * x (t + k) / ((t : ℝ) + k + 1)
      = 4 * (T : ℝ) / (2 * k + 1) * (x T * x (T + k)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have hx1 : x (T + 1) = x T * ((2 * (T : ℝ) + 1) / (2 * (T : ℝ) + 2)) := x_succ T
    have hx2 : x (T + 1 + k) = x (T + k) *
        ((2 * ((T : ℝ) + k) + 1) / (2 * ((T : ℝ) + k) + 2)) := by
      rw [show T + 1 + k = (T + k) + 1 by omega]
      have := x_succ (T + k)
      push_cast at this ⊢
      linarith [this]
    rw [hx1, hx2]
    have c1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have c2 : ((T : ℝ) + k + 1) ≠ 0 := by positivity
    have c3 : (2 * (T : ℝ) + 2) ≠ 0 := by positivity
    have c4 : (2 * ((T : ℝ) + k) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **Closed form** (paper Corollary 7): above the anti-diagonal,
`A n k - A n (k+1) = (2n-1)/(2k+1) * x (n-1) * x (n-1-k)`. -/
lemma A_sub_A {n k : ℕ} (hk : k < n) :
    A n k - A n (k + 1)
      = (2 * (n : ℝ) - 1) / (2 * (k : ℝ) + 1) * (x (n - 1) * x (n - 1 - k)) := by
  have h1 : n - k = (n - k - 1) + 1 := by omega
  have h2 : n - (k + 1) = n - k - 1 := by omega
  have hidx : n - k - 1 + k = n - 1 := by omega
  have hidx2 : n - 1 - k = n - k - 1 := by omega
  have hcast : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
    rw [show n - k - 1 = n - (k + 1) by omega, Nat.cast_sub (by omega : k + 1 ≤ n)]
    push_cast
    ring
  have hdiff : ∑ t ∈ range (n - k - 1), x t * x (t + k)
      - ∑ t ∈ range (n - k - 1), x t * x (t + (k + 1))
      = (1 / 2) * ∑ t ∈ range (n - k - 1), x t * x (t + k) / ((t : ℝ) + k + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hx := x_sub_x_succ (t + k)
    rw [show t + (k + 1) = (t + k) + 1 by omega]
    push_cast at hx
    calc x t * x (t + k) - x t * x ((t + k) + 1)
        = x t * (x (t + k) - x ((t + k) + 1)) := by ring
      _ = x t * (x (t + k) / (2 * ((t : ℝ) + k) + 2)) := by rw [hx]
      _ = 1 / 2 * (x t * x (t + k) / ((t : ℝ) + k + 1)) := by
          field_simp
  have hgosper := gosper k (n - k - 1)
  rw [hidx, hcast] at hgosper
  rw [hgosper] at hdiff
  -- division-free form of the telescoped difference
  have c1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hdiff2 : (2 * (k : ℝ) + 1) * (∑ t ∈ range (n - k - 1), x t * x (t + k)
        - ∑ t ∈ range (n - k - 1), x t * x (t + (k + 1)))
      = 2 * ((n : ℝ) - k - 1) * (x (n - k - 1) * x (n - 1)) := by
    rw [hdiff]
    field_simp
    ring
  rw [A, A, h1, h2, Finset.sum_range_succ, hidx, hidx2]
  -- goal: (∑₁ + x (n-k-1) * x (n-1)) − ∑₂ = (2n-1)/(2k+1) * (x (n-1) * x (n-k-1))
  field_simp
  linear_combination hdiff2

/-- The closed form of the matrix entries. -/
lemma M_closed {n i j : ℕ} (h : i + j < n) :
    M n i j = (2 * (n : ℝ) - 1) / (2 * ((i : ℝ) + j) + 1)
      * (x (n - 1) * x (n - 1 - (i + j))) := by
  rw [M, A_sub_A h]
  push_cast
  try ring

lemma M_nonneg (n i j : ℕ) : 0 ≤ M n i j := by
  rcases lt_or_ge (i + j) n with h | h
  · rw [M_closed h]
    have h1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := by omega
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    have := x_pos (n - 1)
    have := x_pos (n - 1 - (i + j))
    positivity
  · rw [M_eq_zero h]

end HilbertPi
