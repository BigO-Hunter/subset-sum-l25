import SubsetSumL25.Row.JV1000Instance

/- Axiom banner for `SubsetSumL25.Row.JV1000Instance`: `#print axioms` on every
   theorem of the module, plus the `J = 1` collapse data.  House triple only
   (propext, Classical.choice, Quot.sound); fail-closed in `jv1000_receipts.py`. -/
open SubsetSumL25.Row

#print axioms SubsetSumL25.Row.jv_slack_pos
#print axioms SubsetSumL25.Row.jv_T_eq
#print axioms SubsetSumL25.Row.jv_tau0_eps_slack
#print axioms SubsetSumL25.Row.jv_subexp_absorb
#print axioms SubsetSumL25.Row.jv_poly_absorb
#print axioms SubsetSumL25.Row.jv_poly_threshold_ten
#print axioms SubsetSumL25.Row.jv_runtime_absorb
#print axioms SubsetSumL25.Row.jv_harmonic_le
#print axioms SubsetSumL25.Row.jv_r_mod_term
#print axioms SubsetSumL25.Row.jv_s_mod_term
#print axioms SubsetSumL25.Row.jv_r_mod_sum
#print axioms SubsetSumL25.Row.jv_s_mod_sum
#print axioms SubsetSumL25.Row.jv_amp_mod_cert_r
#print axioms SubsetSumL25.Row.jv_amp_mod_cert_s
#print axioms SubsetSumL25.Row.jv_abs_density_r
#print axioms SubsetSumL25.Row.jv_abs_density_s
#print axioms SubsetSumL25.Row.jv_log_bounded
#print axioms SubsetSumL25.Row.jv_amp16_value_r
#print axioms SubsetSumL25.Row.jv_amp16_value_s
#print axioms SubsetSumL25.Row.jv_amp16_exceeds
#print axioms SubsetSumL25.Row.jv_check_C6_r_pos
#print axioms SubsetSumL25.Row.jv_check_C6_r_lt_tau0
#print axioms SubsetSumL25.Row.jv_check_C6_l_lt_tau0
#print axioms SubsetSumL25.Row.jv_check_C7
#print axioms SubsetSumL25.Row.jv_log2_three_lt
#print axioms SubsetSumL25.Row.jv_check_C8
#print axioms SubsetSumL25.Row.jv_check_C8_rat
#print axioms SubsetSumL25.Row.jv_check_S1
#print axioms SubsetSumL25.Row.jv_check_S2
#print axioms SubsetSumL25.Row.jv_check_Delta_pos
#print axioms SubsetSumL25.Row.jv_check_Gamma_pos
#print axioms SubsetSumL25.Row.jv_check_B1
#print axioms SubsetSumL25.Row.jv_check_B3
#print axioms SubsetSumL25.Row.jv_check_A71_l
#print axioms SubsetSumL25.Row.jv_check_A71_r
#print axioms SubsetSumL25.Row.jv_check_A71_mu
#print axioms SubsetSumL25.Row.jv_check_A73
#print axioms SubsetSumL25.Row.jv_check_A74
#print axioms SubsetSumL25.Row.jv_check_prime_draw
#print axioms SubsetSumL25.Row.jv_check_B2
#print axioms SubsetSumL25.Row.jv_check_rho0
#print axioms SubsetSumL25.Row.jv_check_rhoBand
#print axioms SubsetSumL25.Row.jv_check_sum_z
#print axioms SubsetSumL25.Row.jv_check_eps0_gt
#print axioms SubsetSumL25.Row.jv_check_mu_lt
#print axioms SubsetSumL25.Row.jv_check_count
#print axioms SubsetSumL25.Row.jv_inv_log2_le
#print axioms SubsetSumL25.Row.jv_log2_inv_a_le
#print axioms SubsetSumL25.Row.jv_log2_inv_2a_le
#print axioms SubsetSumL25.Row.jvH2_le
#print axioms SubsetSumL25.Row.jvH2_half_sub_ge
#print axioms SubsetSumL25.Row.jv_check_S5
#print axioms SubsetSumL25.Row.jv_check_S3
#print axioms SubsetSumL25.Row.jv_collapse_image
#print axioms SubsetSumL25.Row.jv_residue_is_nine

-- the J = 1 collapse data and the two moment shapes
#check @SubsetSumL25.Row.jvZRho0
#check @SubsetSumL25.Row.jvZBand
#check @SubsetSumL25.Row.jvZBand9
#check @SubsetSumL25.Row.jvCollapseMoment
#check @SubsetSumL25.Row.jvMomentRho0
#check @SubsetSumL25.Row.jvMomentBand
