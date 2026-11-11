import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaGuard
import SubsetSumL25.Row.KapilaPrelim
import SubsetSumL25.Row.KapilaAlias
import SubsetSumL25.Row.KapilaChecksum
import SubsetSumL25.Row.KapilaTest
import SubsetSumL25.Row.KapilaLoop
import SubsetSumL25.Row.KapilaEstimate
import SubsetSumL25.Row.KapilaWide
import SubsetSumL25.Row.KapilaDigitwise
import SubsetSumL25.Row.KapilaBinSum
import SubsetSumL25.Row.KapilaCmpSeg
import SubsetSumL25.Row.KapilaCmpSegLoop
import SubsetSumL25.Row.KapilaCmpSegStride
import SubsetSumL25.Row.KapilaCmpSegStrideProg

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

-- §L11: the multi-word layout — the scale identity, the carry chain, the block
-- sizing, exactness, and item 3's bin-sum contract restated about `placeValue`
-- (item 4's layout written; the read loop's stride arithmetic named as residual)
#print axioms placeValue_nonneg
#print axioms placeValue_scale
#print axioms placeValueAt
#print axioms placeValue_eq_placeValueAt
#print axioms placeValueAt_zero
#print axioms mod_mul_split
#print axioms sum_base_digits
#print axioms placeValueAt_succ
#print axioms payloadStride_mul_spec
#print axioms placeValueAt_digits
#print axioms placeValueAt_payloadStride
#print axioms placeValue_payloadStride
#print axioms getElem?_map_range
#print axioms dAt_eq_of_map
#print axioms rowTest_eq_map
#print axioms WideLayout
#print axioms WideBinSumAgrees
#print axioms dAt_eq_widePlaceValue
#print axioms rowTest_eq_wideBinSum
#print axioms dAt_eq_placeValue_one
#print axioms wideBinSumAgrees_one_iff

-- §W1–§W5: residual (i) — the stride-`k` block reader, its identity with the
-- place value, the obstruction that the k-word sum is not word-resident, the
-- loop's step at stride k with the wide exit shape, and the stated cost shape
#print axioms numAt
#print axioms numAt_zero
#print axioms numAt_succ
#print axioms numAt_one
#print axioms numAt_one_lt
#print axioms numBlock
#print axioms numBlock_zero
#print axioms numBlock_succ
#print axioms numBlock_one_eq_wordList
#print axioms numAt_cast
#print axioms numAt_eq_placeValueAt_scale
#print axioms placeValue_eq_scale_numAt
#print axioms numBlock_map_toQ_eq_placeValue
#print axioms wideLayout_of_numBlock
#print axioms dAt_eq_reader
#print axioms numAt_ge_top
#print axioms numAt_not_word
#print axioms numAt_not_word_one
#print axioms hitCount_numBlock_step
#print axioms sum_range_map_succ
#print axioms hitCount_map_range
#print axioms hitCount_numBlock_eq_sum
#print axioms wideExit_eq_rowTest
#print axioms wideExit_eq_binSum
#print axioms wideExit_eq_binSum'
#print axioms scanWordOpsWide
#print axioms scanWordOpsWide_eq_scanWordOps
#print axioms scanWordOpsWide_le
#print axioms scanWordOpsWide_one

-- residual (i) re-specified as the digitwise comparison: the decision lemma and
-- the compare segment's shape
#print axioms halfTest_iff_wordDiff
#print axioms placeValueAt_eq_scale_numAt
#print axioms numAt_add_one_le
#print axioms numAt_lt_pow
#print axioms numAt_eq_of_lt
#print axioms numAt_split
#print axioms mul_add_le_iff
#print axioms cmpDigitsFrom
#print axioms cmpDigitsFrom_iff
#print axioms hit_of_above
#print axioms hit_of_below
#print axioms tie_hit_iff
#print axioms tieA_hit_iff
#print axioms miss_of_close
#print axioms digHalf
#print axioms digHalf_eq_threshold_pow
#print axioms digHalf_eq_threshold
#print axioms digHalf_eq_ratTest
#print axioms digHalf_eq_placeValueTest
#print axioms cmpSeg
#print axioms cmpSeg_length
#print axioms cmpSegFuel
#print axioms cmpSegFuel_linear
#print axioms cmpSegFuel_zero

-- residual (ii): the bin sums constructed — the aggregate fixed, the contract inhabited
#print axioms binDigits_zero
#print axioms binDigits_eq_numAt_sub
#print axioms placeValue_sub_scale
#print axioms binSum_eq_placeValue_sub
#print axioms wideBinSumAgrees_binSum
#print axioms PayloadCarries
#print axioms wideBinSumAgrees_carried
#print axioms wideExit_eq_binSumDigits
#print axioms halfTest_diff_iff_wordDiff
#print axioms binSumTest_iff_wordDiff
#print axioms hitWord_binSumTest

-- residual (i): the compare segment, walked
#print axioms cmpSeg_reaches
#print axioms cmpSeg_reaches_bound
#print axioms cmpSeg_walk
#print axioms cmpSegCost_le
#print axioms cmpSegCost_tight
#print axioms cmpSegment_getD
#print axioms cmpSeg_cell6_iff_wordTest
#print axioms cmpSeg_spot_tieA
#print axioms cmpSeg_spot_tieV_zero

-- residual (iii): the program-entry reach — the reload, the re-entry, and the loop step
#print axioms cmpSegReload
#print axioms cmpSegReentry
#print axioms cmpSegLoopTail
#print axioms cmpSegment_getD_tail
#print axioms cmpSeg_reentry
#print axioms cmpSeg_loopStep
#print axioms cmpSeg_loopCharge_le
#print axioms cmpSegReentrySpot
#print axioms cmpSegLoopSpot
#print axioms cmpSegReentrySpotTail
#print axioms cmpSeg_spot_reentry
#print axioms cmpSeg_spot_reentry_short
#print axioms cmpSeg_spot_loop
#print axioms cmpSeg_spot_loop_short
#print axioms cmpSeg_spot_loop_first

-- residual (iii)'s two named successors: the `getD`-agreement transfer (§C10) and the
-- loop induction on the comparison counter (§C11)
#print axioms cmpSeg_reaches_program
#print axioms cmpSeg_reaches_gen
#print axioms cmpSeg_walk_gen
#print axioms cmpSeg_head_gen
#print axioms cmpSeg_tieA_gen
#print axioms cmpSeg_tieV_gen
#print axioms cmpHitTail
#print axioms CmpLoopFrame
#print axioms cmpLoopFrame_13
#print axioms cmpLoopFrame_fit
#print axioms up_up_absorb
#print axioms cmpDigitsFrom_congr
#print axioms digHalf_congr
#print axioms walkCost_congr
#print axioms cmpSegCost_congr
#print axioms cmpLoopHits
#print axioms cmpLoopFuel
#print axioms cmpSeg_hitCharge_le
#print axioms cmpSeg_hitBody
#print axioms cmpSeg_guard_taken
#print axioms cmpSeg_guard_exit
#print axioms cmpSeg_hitIter
#print axioms cmpSeg_loop
#print axioms cmpLoopFuel_le

-- residual (iv): the horizon restated (§C12)
#print axioms sum_range_shift
#print axioms cmpLoopFuel_eq_sum
#print axioms cmpLoopFuel_le_mul
#print axioms cmpLoopFuel_le_tight
#print axioms cmpLoopFuel_fits

-- §S6: the seam record at the test path — the data premise, classified and placed
#print axioms isWrite
#print axioms writePositions
#print axioms noBackEdge
#print axioms prelimProg_writes
#print axioms aliasProg_writes
#print axioms checksumProg_writes
#print axioms prelimProg_straightLine
#print axioms aliasProg_straightLine
#print axioms checksumProg_straightLine
#print axioms phaseTexts_no_accumulation
#print axioms payloadCarries_iff_numBlock
#print axioms PayloadSeam
#print axioms PayloadSeam.agrees

-- §C13: residual (iv)'s last gap — the stride-`k` payload read in the test segment
#print axioms strideFold
#print axioms strideFold_zero
#print axioms strideFold_succ
#print axioms strideFold_eq_numAt
#print axioms strideFold_eq_numAt_block
#print axioms numAt_term_at_estimate
#print axioms numAt_split_at_estimate
#print axioms digHalf_estimate_eq_threshold
#print axioms payloadStride_fits_digit
#print axioms digHalf_estimate_payloadStride
#print axioms isLoad
#print axioms readPositions
#print axioms cmpSeg_readPositions
#print axioms cmpSegReload_couples_roles
#print axioms estFuel
#print axioms estFuel_zero
#print axioms estFuel_succ
#print axioms estFuel_le
#print axioms estFuel_le_landed
#print axioms estFuel_eq_sum
#print axioms estFuel_le_paper
#print axioms estFuel_fits
#print axioms digitwise_is_wide_at_digit
#print axioms digitwiseWordOps_le_wide
#print axioms cmpSegStride_reaches_program
#print axioms cmpSegStride_iter
#print axioms cmpSegStride_loop
#print axioms strideHits_le
#print axioms cmpSegStride_to_guard
#print axioms cmpSegStride_run_step
#print axioms cmpSegStride_run_halts
