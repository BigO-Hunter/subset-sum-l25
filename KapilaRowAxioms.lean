import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaGuard
import SubsetSumL25.Row.KapilaPrelim
import SubsetSumL25.Row.KapilaAlias
import SubsetSumL25.Row.KapilaChecksum
import SubsetSumL25.Row.KapilaTest
import SubsetSumL25.Row.KapilaLoop
import SubsetSumL25.Row.KapilaEstimate
import SubsetSumL25.Row.KapilaEstimate

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

-- Proposition P's instruction text: the program, its agreement, and the leaf
-- it discharges
#print axioms prelim_run
#print axioms prelim_sound
#print axioms prelim_agrees_iff_run
#print axioms prelim_agrees_spec
#print axioms run_of_prelim_agrees
#print axioms LeafP_of_prelim_agrees
#print axioms LeafP_of_prelim_run

-- Theorem A's instruction text: the program, its witness leg's soundness, the
-- `isSome` convention's divergence, and the leaf it discharges
#print axioms inF_two
#print axioms alias_run
#print axioms alias_sound
#print axioms yes_of_pair
#print axioms alias_agrees_spec
#print axioms alias_run_of_field
#print axioms isSome_ne_failToNo
#print axioms LeafAnone_of_alias_agrees
#print axioms LeafAnone_of_alias_run

-- Theorem B's instruction text: the third input cell, the program, its witness
-- leg's soundness (and its bin reading), the agreement, and the leaf it
-- discharges
#print axioms inF_three
#print axioms ofFn_sum_ite_triple
#print axioms yes_of_triple
#print axioms checksum_run
#print axioms checksum_sound
#print axioms checksum_support_in_bin
#print axioms checksum_agrees_spec
#print axioms checksum_run_of_field
#print axioms LeafBnone_of_checksum_agrees
#print axioms LeafBnone_of_checksum_run

-- LeafTest's first obligation: the payload convention (two list-valued exits
-- defined from the exit memory, the estimate `d`, and the three rules that
-- determine `rowTest`)
#print axioms payloadBlock
#print axioms PayloadConvention.Ahat_length
#print axioms PayloadConvention.dAt_eq
#print axioms PayloadConvention.verdict_eq_rowTest
#print axioms PayloadConvention.verdict_Ahat_Vhat
#print axioms payload_rules_iff
#print axioms rowTest_separates_payloads
#print axioms isSome_not_enough
#print axioms LeafTest_of_payload_exit

-- the loop (§7 step 7's scan): the three exit equations, the iteration, the loop
#print axioms scan_fold_rules
#print axioms anyHit_eq_rowTest
#print axioms hitWord_eq_ratTest
#print axioms payloadBlock_memOf
#print axioms scan_head
#print axioms scan_body
#print axioms scan_loop
#print axioms scan_epilogue
#print axioms selfLoop_never_halts

-- §L8: the prologue, the run at fuel `12·N + 6`, and §7 step 7's verdict at the
-- exit (the `1 ≤ w` hypothesis and the fact that it is free at the lane's w)
#print axioms wordLength_ge_one
#print axioms one_lt_two_pow
#print axioms scan_prologue
#print axioms scan_run
#print axioms scan_run_eq_rowTest

-- §L9: the scan's word-operation charge at its true degree (quartic), the
-- additive absorption twin with the degree abstracted, and the tight `K + 4`
-- (the residual's loose `^7` / `K + 7` kept beside it, discharged and labelled)
#print axioms scanWordOps
#print axioms wordOpFactor_le_sq
#print axioms scanWordOps_le
#print axioms scanWordOps_le_pow7
#print axioms scanWordOps_composed_le
#print axioms withinEnvelope_add_absorb
#print axioms scan_cost_absorbed
#print axioms scan_cost_absorbed_pow7

-- §L10: the estimates' arithmetic relation — the accumulators named, `dAt` as
-- one-denominator accumulator difference and as the s-th entry difference, the
-- verdict reading only the `dAt` list, the bin-sum seam's exact contract, and
-- the proved limit of the one-word reading (item 4's shape)
#print axioms memOf_toNat
#print axioms Ahat_eq_toQ
#print axioms Vhat_eq_toQ
#print axioms dAt_eq_accum
#print axioms dAt_eq_accum_div
#print axioms abs_dAt_eq
#print axioms hitWord_eq_dAt
#print axioms Ahat_getElem?
#print axioms Vhat_getElem?
#print axioms dAt_of_getElem?
#print axioms zipWith_diag
#print axioms rowTest_Ahat
#print axioms BinSumAgrees
#print axioms rowTest_eq_binSum
#print axioms est_lt_two_pow
#print axioms abs_dAt_mul_lt
#print axioms abs_dAt_lt_half
#print axioms payloadStride
#print axioms placeValue
#print axioms placeValue_one
