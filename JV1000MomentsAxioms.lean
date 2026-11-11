import SubsetSumL25.Row.JV1000Moments

/- Axiom banner for `SubsetSumL25.Row.JV1000Quadrature` + `SubsetSumL25.Row.JV1000Moments`:
`#print axioms` on every theorem of both new modules.  House triple only
(propext, Classical.choice, Quot.sound); fail-closed in `jv1000_moment_receipts.py`.

The point of this banner is narrow and load-bearing: the two refutations in §2 are the
only *new mathematical content* of this round, and a refutation carrying `sorryAx` or
`native_decide` would be worth exactly nothing.  Every one of them must come back in the
house triple. -/
open SubsetSumL25.Row

-- §quadrature: the trapezoid rule against a Lipschitz constant
#print axioms SubsetSumL25.Row.integral_self
#print axioms SubsetSumL25.Row.chord_dev_le
#print axioms SubsetSumL25.Row.chord_dev_le_const
#print axioms SubsetSumL25.Row.integral_lerp
#print axioms SubsetSumL25.Row.trap_error_le
#print axioms SubsetSumL25.Row.trap_error_panels

-- §1: the row data the bounds use
#print axioms SubsetSumL25.Row.jv_lip16_value_r
#print axioms SubsetSumL25.Row.jv_lip16_value_s
#print axioms SubsetSumL25.Row.jvLogDensityR_zero
#print axioms SubsetSumL25.Row.jvLogDensityS_zero
#print axioms SubsetSumL25.Row.jv_r_lip_zero
#print axioms SubsetSumL25.Row.jv_s_lip_zero

-- §2: the two refutations
#print axioms SubsetSumL25.Row.jv_moment_window_lb
#print axioms SubsetSumL25.Row.jv_momentRho0_gt_two
#print axioms SubsetSumL25.Row.jv_momentBand_gt_two
#print axioms SubsetSumL25.Row.jv_rhopow_lt_two
#print axioms SubsetSumL25.Row.jv_m1_stated_false
#print axioms SubsetSumL25.Row.jv_m2_stated_false

-- §3: the corrected obligations (definitions + the count)
#print axioms SubsetSumL25.Row.jv_residue_partition_relocated
#check @SubsetSumL25.Row.jvU
#check @SubsetSumL25.Row.jvV
#check @SubsetSumL25.Row.jvMomentRho0Cert
#check @SubsetSumL25.Row.jvMomentBandCert
#check @SubsetSumL25.Row.JV1000Moments
