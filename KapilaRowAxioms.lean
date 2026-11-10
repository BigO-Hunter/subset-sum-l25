import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaGuard

/-! Axiom banner for the row assembly.  Every declaration the row's claim
rests on must report only the house triple `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no `native_decide`. -/

open SubsetSumL25.Row

#print axioms kapila_row
#print axioms rowHorizon_bigO
#print axioms runtime_absorb
#print axioms envE_absorb
#print axioms exec_eq_of_halted
#print axioms count_congr
#print axioms const_le_two_pow

-- the D7 seam, cut per branch
#print axioms D7.agrees
#print axioms D7.ofBranches
#print axioms fallback_agrees_iff
-- the guard's coverage
#print axioms count_const
#print axioms correctAt_of_fallback_det
#print axioms two_mul_sq_lt_two_pow
#print axioms log2_mul_le_self
#print axioms guardOk_eventually

-- agrees_main, measured: the routing on its false side, the fuel transport,
-- the main branch's four segment leaves
#print axioms exec_mono_halted
#print axioms fallback_eq_false_iff
#print axioms fallback_false_of_guard
#print axioms fallback_false_eventually
#print axioms run_eq_of_prelim_some
#print axioms run_eq_false_of_alias_none
#print axioms run_eq_false_of_checksum_none
#print axioms run_eq_rowTest
#print axioms rowTest_cons_cons
#print axioms abs_ge_half_iff
#print axioms agrees_main_iff_leaves
#print axioms agrees_main_of_leaves

-- the reification: the first field's program, the seam field it discharges,
-- and the multi-word charge's absorption
#print axioms fallback_agrees_of_mitmProg
#print axioms D7.ofMitmProg
#print axioms rowTest_eq_of_rules
#print axioms wordOpFactor_le_cube
#print axioms withinEnvelope_wordop_absorb
