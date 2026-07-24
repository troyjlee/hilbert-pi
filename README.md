# HilbertPi: a Lean 4 proof of Hilbert's inequality, `‖H‖ ≤ π`

[![Lean Action CI](https://github.com/troyjlee/hilbert-pi/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/troyjlee/hilbert-pi/actions/workflows/lean_action_ci.yml)

A machine-checked proof of **Hilbert's inequality** — the spectral norm of the
Hilbert matrix `H[i,j] = 1/(i+j+1)` on `ℓ²(ℕ)` is at most `π` — following the
combinatorial proof in *A Combinatorial Proof of Hilbert's Inequality*
(`../monthly.tex`): an explicit Hankel majorant `M_n` built from central
binomial coefficients with exact Perron eigenvector `x_i = C(2i,i)/4^i`.

As far as we know this is the first formalization of Hilbert's inequality in
any proof assistant.

## Main results (`HilbertPi/Main.lean`)

* `half_hilbert_bound` — the bilinear form of the half-Hilbert matrix `T n`
  (entries `1/(i+j+1/2)` above the anti-diagonal) is bounded by `π‖u‖‖v‖`,
  for every finite size `n`.
* `hilbert_inequality_finite` — Hilbert's inequality for finitely supported
  sequences: `∑_{i,j<N} u_i v_j/(i+j+1) ≤ π √(∑u²) √(∑v²)`.
* `hilbert_summable`, `hilbert_inequality_l2`, `hilbert_inequality_l2'` —
  the `ℓ²` statement: for `f, g ∈ lp (fun _ : ℕ => ℝ) 2` the double series
  converges absolutely and `|∑'_{i,j} f i * g j / (i+j+1)| ≤ π ‖f‖ ‖g‖`.

## Schur's theorem, general `λ` (`HilbertPi/General/`)

The sharpening to `‖H_λ‖ ≤ π csc(πλ)` for the matrix `H_λ[i,j] = 1/(i+j+λ)`,
`0 < λ < 1` (paper Section 4):

* `HilbertPi.General.half_hilbert_bound_general` — for every `n`, the bilinear
  form of `T λ n` is bounded by `(π / sin(πλ)) ‖u‖ ‖v‖`.
* `HilbertPi.General.schur_inequality_finite` — the finitely-supported Schur
  inequality `∑_{i,j<N} u_i v_j /(i+j+λ) ≤ π csc(πλ) √(∑u²) √(∑v²)`.

Here the sequences are `gx i = ∏_{t<i}(t+λ)/(t+1) = Γ(i+λ)/(Γ(λ) i!)` and its
dual `gy`; the analytic inputs are the log-convexity of `Γ`
(`Real.convexOn_log_Gamma`) and Euler's reflection formula
(`Real.Gamma_mul_Gamma_one_sub`), which supply the entrywise domination in
place of Wallis's product. The eigenvector, telescoping, Schur test, and
embedding steps are shared with the `λ = 1/2` warm-up.

## Structure of the proof

| File | Content | Paper reference |
|---|---|---|
| `Sequence.lean` | `x i = C(2i,i)/4^i`, ratio identity, and the Wallis bound `1/π ≤ (m+1/2) x_m²` via Mathlib's `Real.Wallis.W_le` | eq. (7), Lemma 9 |
| `Convolution.lean` | `∑_{i≤m} x_i x_{m-i} = 1`, by a discrete form of the generating-function argument | Proposition 3 |
| `EigenMatrix.lean` | the majorant `M n` and the exact eigenvector identity `M n x = x`; Gosper telescoping; closed form of the entries | Theorem 4, Lemma 6, Corollary 7 |
| `Domination.lean` | entrywise bound `T n ≤ π • M n` (square-root–free) and the row bound `∑_j T n i j x_j ≤ π x_i` | Theorem 8 |
| `SchurTest.lean` | the finite Schur test for symmetric nonnegative kernels | Lemma 2 |
| `Main.lean` | assembly: finite, finitely-supported, and `ℓ²` statements | Corollaries 11–12 |
| `General/*.lean` | the same pipeline for general `λ` via the Γ function | Section 4 |
| `General/Sharp*.lean` | `ℓ²` sharpness: attained for `λ < 1/2`, approached for `λ ≥ 1/2` | Section 5 |

The only analytic input is Wallis's product, used through Mathlib's
`Real.Wallis.W_le : W k ≤ π/2`; everything else is finite `Finset` algebra.
No limits or filters appear in the proof of the upper bound.

## Paper ↔ Lean cross-reference

Each numbered result of *A Combinatorial Proof of Hilbert's Inequality* and its
Lean counterpart. Warm-up (`λ = 1/2`) names are in namespace `HilbertPi`;
general-`λ` names are in `HilbertPi.General`.

| Paper | Statement | Lean (`λ = 1/2`) | Lean (general `λ`) |
|---|---|---|---|
| Lemma (domination) | `0 ≤ A ≤ B ⟹ ‖A‖ ≤ ‖B‖` | folded into `T_row_bound` | folded into `T_row_bound` |
| Lemma (Schur test) | eigenvector norm bound | `schur_test` | `schur_test` (shared) |
| Prop. (convolution) | `∑_i x_i x_{m-i} = 1` | `conv` | `conv` |
| Theorem (eigenvector) | `M x = x` | `eig` | `eig` |
| Lemma (Gosper) | telescoped correlation sum | `gosper` | `gosper` |
| Corollary (closed form) | entries of `M` | `M_closed` / `A_sub_A` | `M_closed` / `A_sub_A` |
| Lemma (Wallis) | `1/π ≤ (m+½) x_m²` | `one_div_pi_le_u` | — (replaced by Γ) |
| Lemma (Γ tools) | `g(a)=Γ(a+λ)/Γ(a)` monotone | — | `g_mono` |
| Theorem (domination) | `T ≤ (π csc πλ) M` | `T_le_pi_mul_M` | `T_le` |
| Corollary / Theorem | `‖T_{n,λ}‖ ≤ π csc(πλ)` | `half_hilbert_bound` | `half_hilbert_bound_general` |
| Corollary / Theorem | Hilbert/Schur inequality | `hilbert_inequality_finite` | `schur_inequality_finite` |
| — | `ℓ²` statement `‖H‖ ≤ π` | `hilbert_inequality_l2` | (upper bound; `ℓ²` sharpness below) |
| Prop. (`exact-eig`) | eigenvector identity `H_λ x = θ x` | — | `eigen_identity` |
| Prop. (`exact-eig`) | norm attained: `‖H_λ‖ = π csc(πλ)` | — | `schur_norm_attained` |
| Thm. (`sharp-large`) | `‖H_λ‖ ≤ π` for `λ ≥ 1/2` | — | `hilbert_le_pi_finite` |
| Thm. (`sharp-large`) | `‖H_λ‖ ≥ π` for `λ ≥ 1/2` | — | `norm_ge_pi_sharp` |

**Sharpness, `0 < λ < 1/2`** (`HilbertPi/General/Sharp.lean`): the square-summable
eigenvector `gx λ` satisfies `∑' j, gx_j/(i+j+λ) = π csc(πλ) · gx_i`
(`eigen_identity`), and its Rayleigh quotient equals `π csc(πλ)`
(`schur_norm_attained`), so the constant is exactly attained. The proof adds
Wendel's Γ bounds, a pointwise `Γ`-ratio limit, and Tannery's theorem on top of
the finite construction.

**Sharpness, `λ ≥ 1/2`** (`HilbertPi/General/SharpLarge.lean`): here the norm is
*not* attained and equals `π`. Both halves are formalized:

* `hilbert_le_pi_finite` — the upper bound `‖H_λ‖ ≤ π`, by entrywise domination
  `1/(i+j+λ) ≤ 1/(i+j+1/2)` from the `λ = 1/2` case;
* `norm_ge_pi_sharp` — the lower bound: for every `ε > 0` some test vector
  `x(μ)`, `μ ∈ [1/4, 1/2)`, has Rayleigh quotient exceeding `π - ε`.

The lower bound uses the `μ < 1/2` eigenvectors as test vectors, the
perturbation identity `∑ H_μ = ∑ H_λ + (λ-μ)E`, the *factored* error bound
`E ≤ D²` (`E_le_D_sq`), and the divergence of `‖x(μ)‖²` as `μ ↑ 1/2`
(`norm_sq_unbounded`).

## Building

```
lake exe cache get   # fetch Mathlib build cache
lake build
```

`Test.lean` contains the axiom audit (`#print axioms` shows only
`propext, Classical.choice, Quot.sound`) and numeric sanity checks of `M₄`
against the values printed in the paper (`175/256, 35/128, 7/32, 5/16`):

```
lake env lean Test.lean
```
