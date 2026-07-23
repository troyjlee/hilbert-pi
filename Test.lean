import HilbertPi

open HilbertPi Finset

/- Axiom audit: only the three standard axioms may appear. -/
#print axioms hilbert_inequality_l2
#print axioms hilbert_inequality_l2'
#print axioms hilbert_summable
#print axioms hilbert_inequality_finite
#print axioms half_hilbert_bound

/- Numeric smoke test against the paper's M₄ (monthly.tex §3):
   first row 175/256, 35/128, 7/32, 5/16; and M₄[3,3] = 0. -/
example : M 4 0 0 = 175 / 256 := by
  norm_num [M, A, x, Nat.centralBinom, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero]
example : M 4 0 1 = 35 / 128 := by
  norm_num [M, A, x, Nat.centralBinom, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero]
example : M 4 0 2 = 7 / 32 := by
  norm_num [M, A, x, Nat.centralBinom, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero]
example : M 4 0 3 = 5 / 16 := by
  norm_num [M, A, x, Nat.centralBinom, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero]
example : M 4 3 3 = 0 := M_eq_zero (by norm_num)

/- Eigenvector components x = (1, 1/2, 3/8, 5/16). -/
example : x 2 = 3 / 8 := by norm_num [x, Nat.centralBinom, Nat.choose]
example : x 3 = 5 / 16 := by norm_num [x, Nat.centralBinom, Nat.choose]

/- Half-Hilbert matrix entries: 1/(i+j+1/2) above the anti-diagonal. -/
example : T 4 1 2 = 1 / (7 / 2) := by norm_num [T]
example : T 4 2 2 = 0 := by norm_num [T]


/- General-λ (Schur) results. -/
#print axioms HilbertPi.General.half_hilbert_bound_general
#print axioms HilbertPi.General.schur_inequality_finite

/- At λ = 1/2, gx and gy both reduce to the central-binomial sequence. -/
example : HilbertPi.General.gx (1/2 : ℝ) 2 = 3/8 := by
  norm_num [HilbertPi.General.gx, Finset.prod_range_succ]
example : HilbertPi.General.gy (1/2 : ℝ) 2 = 3/8 := by
  norm_num [HilbertPi.General.gy, Finset.prod_range_succ]

/- ℓ² sharpness (paper §5): the norm π csc(πλ) is attained. -/
#print axioms HilbertPi.General.eigen_identity
#print axioms HilbertPi.General.schur_norm_attained
