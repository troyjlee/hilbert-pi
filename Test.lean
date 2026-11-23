import HilbertPi

open HilbertPi Finset

set_option linter.style.longLine false

/-! ## Axiom audit

`#guard_msgs` turns each `#print axioms` from diagnostic output into an
assertion: if any declaration below ever acquires a further axiom — `sorryAx`
in particular — the elaboration of this file fails and so does `lake build`
(`Test` is one of the package's default targets). -/

/-- info: 'HilbertPi.half_hilbert_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms half_hilbert_bound

/-- info: 'HilbertPi.hilbert_inequality_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hilbert_inequality_finite

/-- info: 'HilbertPi.hilbert_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hilbert_summable

/-- info: 'HilbertPi.hilbert_inequality_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hilbert_inequality_l2

/-- info: 'HilbertPi.hilbert_inequality_l2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hilbert_inequality_l2'

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


/-! ### General-λ (Schur) results -/

/-- info: 'HilbertPi.General.half_hilbert_bound_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.half_hilbert_bound_general

/-- info: 'HilbertPi.General.schur_inequality_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.schur_inequality_finite

/-- info: 'HilbertPi.General.schur_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.schur_summable

/-- info: 'HilbertPi.General.schur_inequality_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.schur_inequality_l2

/-- info: 'HilbertPi.General.schur_inequality_l2'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.schur_inequality_l2'

/- At λ = 1/2, gx and gy both reduce to the central-binomial sequence. -/
example : HilbertPi.General.gx (1/2 : ℝ) 2 = 3/8 := by
  norm_num [HilbertPi.General.gx, Finset.prod_range_succ]
example : HilbertPi.General.gy (1/2 : ℝ) 2 = 3/8 := by
  norm_num [HilbertPi.General.gy, Finset.prod_range_succ]

/-! ### Sharpness (paper §5) -/

/-- info: 'HilbertPi.General.eigen_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.eigen_identity

/-- info: 'HilbertPi.General.schur_norm_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.schur_norm_attained

/-- info: 'HilbertPi.General.hilbert_le_pi_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.hilbert_le_pi_finite

/-- info: 'HilbertPi.General.norm_ge_pi_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.norm_ge_pi_sharp

/-! ### The operator norm itself: `‖H_λ‖ = π csc(πλ)` and `‖H_λ‖ = π` -/

/-- info: 'HilbertPi.General.opNorm_eq_csc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.opNorm_eq_csc

/-- info: 'HilbertPi.General.pi_le_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.pi_le_opNorm

/-- info: 'HilbertPi.General.opNorm_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.opNorm_eq_pi

/-- info: 'HilbertPi.General.schur_norm_attained_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.schur_norm_attained_l2

/-- info: 'HilbertPi.General.sSup_bilinValuesL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HilbertPi.General.sSup_bilinValuesL2
