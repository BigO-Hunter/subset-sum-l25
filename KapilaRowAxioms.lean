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
