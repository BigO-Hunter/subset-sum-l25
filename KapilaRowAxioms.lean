import SubsetSumL25.Row.KapilaRow

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
