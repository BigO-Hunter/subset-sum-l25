/-
§C14 — the stride tail as a **program**: the variant, and its reach against estFuel.

§C13 (Row/KapilaCmpSegStride) restated the arithmetic of the stride-k read and named
what was still missing: estFuel is the drift-free charge, but no *program* ran it.
The reason is cmpSegReload_couples_roles — the landed reload reloads the walk's digit
position from the counter, which is the digit address offset.  At stride = 1 those are
the same number; at stride = k they are not, and sim_stride.py D2/D2b measure the
consequence (the walk's span grows with the estimate index, and on a constructed block
the verdict flips).

## §C14.1 — the variant

strideTail is six instructions and sim_stride.py D7 pins it entry for entry:

  29  add 15 15 6    accumulate the verdict
  30  add 13 13 16   advance the counter by the STRIDE constant in cell 16
  31  add 0 11 13    digit address V = baseV + counter
  32  add 1 12 13    digit address A = baseA + counter
  33  add 2 17 7     digit position = p (cell 17, NOT the counter) — the D2b fix
  34  blt 13 14 0    loop while counter < blockLen·k + p

So the stride lives in cell 16's VALUE and the walk's digit position lives in cell 17's
VALUE; the instruction text is (k, p)-independent.  The prefix is cmpSeg 29 untouched,
so §C10's transfer applies to the variant verbatim (cmpSegStride_getD).

## §C14.2 — what is proved

* strideTail_reads: the tail adds NO load instruction, so the variant reads exactly where
  the segment did (positions 0,1,21,22).
* cmpSegStride_reaches_program: §C10's reach, transferred — the segment of the variant
  reaches position 29 in exactly cmpSegCost steps with the verdict in cell 6.
* cmpSegStride_tail_step: the six tail instructions reach position 0 in exactly 6 steps,
  leaving acc + verdict, the advanced counter, and the segment's precondition
  re-established at the next estimate's digit addresses.
* cmpSegStride_iter: one comparison, end to end — cmpSegCost + 6 steps.
* cmpSegStride_loop: m comparisons at estFuel h (baseV + j·k) (baseA + j·k) k p r m steps,
  accumulating strideHits.

The digit position is a CONSTANT in every one of them, which is why the charge is
blockLen · (20 + 9p) rather than §C12's m · (20 + 9(p+m)).

Nothing in Statement.lean is touched; this module is a leaf of the import DAG.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaCmpSegStride

set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §C14.1 — the tail, the program, and the getD agreement -/

/-- **The stride tail.**  Six instructions; sim_stride.py D7 pins this exact list. -/
def strideTail : List Instr :=
  [ .add 15 15 6, .add 13 13 16, .add 0 11 13, .add 1 12 13, .add 2 17 7, .blt 13 14 0 ]

theorem strideTail_length : strideTail.length = 6 := rfl

/-- The variant program: the *same* compare segment, the stride tail after it. -/
def cmpSegStrideProgram (tail : List Instr) : List Instr :=
  cmpSeg 29 ++ (strideTail ++ tail)

/-- **The tail adds no read.**  So the variant reads memory exactly where the segment
did — the charge is a function of the digits visited, not of the stride. -/
theorem strideTail_reads : readPositions strideTail = [] := rfl

/-- **The segment's getD facts transfer to the variant.**  Positions 0…28 are cmpSeg's
own — the variant changed only what follows. -/
theorem cmpSegStride_getD (tail : List Instr) {i : Nat} (hi : i ≤ 28) :
    (cmpSegStrideProgram tail).getD i Instr.reject = (cmpSeg 29).getD i Instr.reject := by
  unfold cmpSegStrideProgram
  have hlen : i < (cmpSeg 29).length := by rw [cmpSeg_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]

/-- **The tail's getD facts** — positions 29…34 of the variant are strideTail's. -/
theorem cmpSegStride_getD_tail (tail : List Instr) {i : Nat} (hi : i < 6) :
    (cmpSegStrideProgram tail).getD (29 + i) Instr.reject = strideTail.getD i Instr.reject := by
  unfold cmpSegStrideProgram
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append]
  rw [cmpSeg_length]
  rw [if_neg (by omega : ¬ (29 + i < 29))]
  rw [show 29 + i - 29 = i from by omega]
  rw [List.getElem?_append_left (by rw [strideTail_length]; exact hi)]

theorem cmpSegStride_s29 (tail : List Instr) :
    (cmpSegStrideProgram tail).getD 29 Instr.reject = Instr.add 15 15 6 := by
  rw [show (29 : Nat) = 29 + 0 from rfl, cmpSegStride_getD_tail (tail := tail) (i := 0) (by omega)]
  rfl

theorem cmpSegStride_s30 (tail : List Instr) :
    (cmpSegStrideProgram tail).getD 30 Instr.reject = Instr.add 13 13 16 := by
  rw [show (30 : Nat) = 29 + 1 from rfl, cmpSegStride_getD_tail (tail := tail) (i := 1) (by omega)]
  rfl

theorem cmpSegStride_s31 (tail : List Instr) :
    (cmpSegStrideProgram tail).getD 31 Instr.reject = Instr.add 0 11 13 := by
  rw [show (31 : Nat) = 29 + 2 from rfl, cmpSegStride_getD_tail (tail := tail) (i := 2) (by omega)]
  rfl

theorem cmpSegStride_s32 (tail : List Instr) :
    (cmpSegStrideProgram tail).getD 32 Instr.reject = Instr.add 1 12 13 := by
  rw [show (32 : Nat) = 29 + 3 from rfl, cmpSegStride_getD_tail (tail := tail) (i := 3) (by omega)]
  rfl

theorem cmpSegStride_s33 (tail : List Instr) :
    (cmpSegStrideProgram tail).getD 33 Instr.reject = Instr.add 2 17 7 := by
  rw [show (33 : Nat) = 29 + 4 from rfl, cmpSegStride_getD_tail (tail := tail) (i := 4) (by omega)]
  rfl

theorem cmpSegStride_s34 (tail : List Instr) :
    (cmpSegStrideProgram tail).getD 34 Instr.reject = Instr.blt 13 14 0 := by
  rw [show (34 : Nat) = 29 + 5 from rfl, cmpSegStride_getD_tail (tail := tail) (i := 5) (by omega)]
  rfl

/-! ### §C14.2 — the segment reach, transferred -/

/-- **THE SEGMENT'S REACH ON THE VARIANT PROGRAM.**  §C10 instantiated at
cmpSegStrideProgram tail, whose agreement hypothesis is cmpSegStride_getD.  The segment
of the variant runs from position 0 to position 29 in exactly cmpSegCost steps, with the
verdict in cell 6 and the frame intact. -/
theorem cmpSegStride_reaches_program (tail : List Instr) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h9 : h 9 = 2 ^ r)
    (k0 : st 0 = addrV + p) (k1 : st 1 = addrA + p) (k2 : st 2 = p)
    (hadA : h (addrA + p) + 2 ^ r < 2 ^ w)
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w)
    (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSegStrideProgram tail) ρ (S + cmpSegCost h addrV addrA p r) 0 0 (memOf w st)
        = exec (cmpSegStrideProgram tail) ρ S 29 0 (memOf w st') :=
  cmpSeg_reaches_gen (fun _i hi => cmpSegStride_getD tail hi)
    hfitH hV hA h7 h8 h9 k0 k1 k2 hadA hadV hag hfit S

/-! ### §C14.3 — the tail: six instructions, and the roles separated -/

/-- **THE TAIL, RUN.**  From position 29 with the counter in cell 13, the six tail
instructions reach position 0 in exactly 6 steps, leaving

* cell 15 = acc + verdict (the accumulator threaded),
* cell 13 = c + k (the counter advanced by the STRIDE, not by one),
* cells 0/1 = the next estimate's digit addresses, cell 2 = p (the digit position
  UNCHANGED, read from cell 17 and not from the counter).

The guard is taken here; cmpSegStride_guard_exit is the other branch. -/
theorem cmpSegStride_tail_step (tail : List Instr) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {baseV baseA k p c limit acc : Nat} {st : Nat → Nat}
    (h7 : h 7 = 0) (h11 : h 11 = baseV) (h12 : h 12 = baseA)
    (h14 : h 14 = limit) (h16 : h 16 = k) (h17 : h 17 = p)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w)
    (h13 : st 13 = c) (h15 : st 15 = acc) (h6le : st 6 ≤ 1) (hacc1 : acc + 1 < 2 ^ w)
    (hcw : c + k < 2 ^ w) (hvw : baseV + (c + k) < 2 ^ w) (haw : baseA + (c + k) < 2 ^ w)
    (hpw : p < 2 ^ w) (S : Nat) :
    ∃ st', (st' 0 = baseV + (c + k)) ∧ (st' 1 = baseA + (c + k)) ∧ (st' 2 = p) ∧
        (st' 13 = c + k) ∧ (st' 15 = acc + st 6) ∧ (st' 6 = st 6) ∧
        (∀ z, ¬ CmpCell z → st' z = up (up h 15 (acc + st 6)) 13 (c + k) z) ∧
        (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSegStrideProgram tail) ρ (S + 5) 29 0 (memOf w st)
        = exec (cmpSegStrideProgram tail) ρ S 34 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s11 : st 11 = baseV := by rw [hag 11 (not_cmpCell_high (by omega))]; exact h11
  have s12 : st 12 = baseA := by rw [hag 12 (not_cmpCell_high (by omega))]; exact h12
  have s16 : st 16 = k := by rw [hag 16 (not_cmpCell_high (by omega))]; exact h16
  have s17 : st 17 = p := by rw [hag 17 (not_cmpCell_high (by omega))]; exact h17
  -- 29: accumulate the verdict
  rw [exec_add_step (S := S + 5) (hS := by omega) (cmpSegStride_s29 tail)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have e15 : st 15 + st 6 = acc + st 6 := by rw [h15]
  rw [e15]
  set a0 : Nat → Nat := up st 15 (acc + st 6) with ha0
  have hf0 : ∀ z, a0 z < 2 ^ w := upFit hfit (by omega)
  have ag0 : ∀ z, ¬ CmpCell z → a0 z = up h 15 (acc + st 6) z := by
    intro z hz
    rw [ha0]
    by_cases hz15 : z = 15
    · subst hz15; rw [up_eq, up_eq]
    · rw [up_ne hz15, hag z hz, up_ne hz15]
  have e13 : a0 13 = c := by rw [ha0, up_ne (by decide : (13 : Nat) ≠ 15)]; exact h13
  have e16 : a0 16 = k := by rw [ha0, up_ne (by decide : (16 : Nat) ≠ 15)]; exact s16
  have e11 : a0 11 = baseV := by rw [ha0, up_ne (by decide : (11 : Nat) ≠ 15)]; exact s11
  have e12 : a0 12 = baseA := by rw [ha0, up_ne (by decide : (12 : Nat) ≠ 15)]; exact s12
  have e17 : a0 17 = p := by rw [ha0, up_ne (by decide : (17 : Nat) ≠ 15)]; exact s17
  have e7 : a0 7 = 0 := by rw [ha0, up_ne (by decide : (7 : Nat) ≠ 15)]; exact s7
  have e6 : a0 6 = st 6 := by rw [ha0, up_ne (by decide : (6 : Nat) ≠ 15)]
  -- 30: advance the counter by the stride constant
  rw [exec_add_step (S := S + 4) (hS := by omega) (cmpSegStride_s30 tail)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  rw [show a0 13 + a0 16 = c + k from by rw [e13, e16]]
  set a1 : Nat → Nat := up a0 13 (c + k) with ha1
  have hf1 : ∀ z, a1 z < 2 ^ w := upFit hf0 hcw
  have ag1 : ∀ z, ¬ CmpCell z → a1 z = up (up h 15 (acc + st 6)) 13 (c + k) z := by
    intro z hz
    rw [ha1]
    by_cases hz13 : z = 13
    · subst hz13; rw [up_eq, up_eq]
    · rw [up_ne hz13, ag0 z hz, up_ne hz13]
  have f13 : a1 13 = c + k := by rw [ha1, up_eq]
  have f11 : a1 11 = baseV := by rw [ha1, up_ne (by decide : (11 : Nat) ≠ 13)]; exact e11
  have f12 : a1 12 = baseA := by rw [ha1, up_ne (by decide : (12 : Nat) ≠ 13)]; exact e12
  have f17 : a1 17 = p := by rw [ha1, up_ne (by decide : (17 : Nat) ≠ 13)]; exact e17
  have f7 : a1 7 = 0 := by rw [ha1, up_ne (by decide : (7 : Nat) ≠ 13)]; exact e7
  have f6 : a1 6 = st 6 := by rw [ha1, up_ne (by decide : (6 : Nat) ≠ 13)]; exact e6
  -- 31: digit address V = baseV + counter
  rw [exec_add_step (S := S + 3) (hS := by omega) (cmpSegStride_s31 tail)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  rw [show a1 11 + a1 13 = baseV + (c + k) from by rw [f11, f13]]
  set a2 : Nat → Nat := up a1 0 (baseV + (c + k)) with ha2
  have hf2 : ∀ z, a2 z < 2 ^ w := upFit hf1 hvw
  have ag2 : ∀ z, ¬ CmpCell z → a2 z = up (up h 15 (acc + st 6)) 13 (c + k) z :=
    cmpAgree_up cmpCell_zero ag1
  have g13 : a2 13 = c + k := by rw [ha2, up_ne (by decide : (13 : Nat) ≠ 0)]; exact f13
  have g12 : a2 12 = baseA := by rw [ha2, up_ne (by decide : (12 : Nat) ≠ 0)]; exact f12
  have g17 : a2 17 = p := by rw [ha2, up_ne (by decide : (17 : Nat) ≠ 0)]; exact f17
  have g7 : a2 7 = 0 := by rw [ha2, up_ne (by decide : (7 : Nat) ≠ 0)]; exact f7
  have g6 : a2 6 = st 6 := by rw [ha2, up_ne (by decide : (6 : Nat) ≠ 0)]; exact f6
  -- 32: digit address A = baseA + counter
  rw [exec_add_step (S := S + 2) (hS := by omega) (cmpSegStride_s32 tail)]
  rw [show S + 2 - 1 = S + 1 from rfl]
  rw [show a2 12 + a2 13 = baseA + (c + k) from by rw [g12, g13]]
  set a3 : Nat → Nat := up a2 1 (baseA + (c + k)) with ha3
  have hf3 : ∀ z, a3 z < 2 ^ w := upFit hf2 haw
  have ag3 : ∀ z, ¬ CmpCell z → a3 z = up (up h 15 (acc + st 6)) 13 (c + k) z :=
    cmpAgree_up cmpCell_one ag2
  have i13 : a3 13 = c + k := by rw [ha3, up_ne (by decide : (13 : Nat) ≠ 1)]; exact g13
  have i17 : a3 17 = p := by rw [ha3, up_ne (by decide : (17 : Nat) ≠ 1)]; exact g17
  have i7 : a3 7 = 0 := by rw [ha3, up_ne (by decide : (7 : Nat) ≠ 1)]; exact g7
  have i6 : a3 6 = st 6 := by rw [ha3, up_ne (by decide : (6 : Nat) ≠ 1)]; exact g6
  -- 33: digit position = p, from the CONSTANT (the D2b fix)
  rw [exec_add_step (S := S + 1) (hS := by omega) (cmpSegStride_s33 tail)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  rw [show a3 17 + a3 7 = p from by rw [i17, i7, Nat.add_zero]]
  refine ⟨up a3 2 p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [up_ne (by decide : (0 : Nat) ≠ 2), ha3, up_ne (by decide : (0 : Nat) ≠ 1), ha2]
    exact up_eq a1 0 _
  · rw [up_ne (by decide : (1 : Nat) ≠ 2), ha3]
    exact up_eq a2 1 _
  · exact up_eq a3 2 _
  · rw [up_ne (by decide : (13 : Nat) ≠ 2), ha3, up_ne (by decide : (13 : Nat) ≠ 1),
      ha2, up_ne (by decide : (13 : Nat) ≠ 0)]
    exact f13
  · rw [up_ne (by decide : (15 : Nat) ≠ 2), ha3, up_ne (by decide : (15 : Nat) ≠ 1),
      ha2, up_ne (by decide : (15 : Nat) ≠ 0), ha1, up_ne (by decide : (15 : Nat) ≠ 13),
      ha0, up_eq]
  · rw [up_ne (by decide : (6 : Nat) ≠ 2), ha3, up_ne (by decide : (6 : Nat) ≠ 1),
      ha2, up_ne (by decide : (6 : Nat) ≠ 0), ha1, up_ne (by decide : (6 : Nat) ≠ 13)]
    exact e6
  · exact cmpAgree_up cmpCell_two ag3
  · exact upFit hf3 hpw
  · simp

/-- **The guard taken** — c + k < limit sends the loop back to position 0. -/
theorem cmpSegStride_guard_taken (tail : List Instr) {ρ : Nat → BitVec w} {c limit : Nat}
    {st : Nat → Nat} (h13 : st 13 = c) (h14 : st 14 = limit) (hl : c < limit)
    (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    exec (cmpSegStrideProgram tail) ρ (S + 1) 34 0 (memOf w st)
      = exec (cmpSegStrideProgram tail) ρ S 0 0 (memOf w st) := by
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) (cmpSegStride_s34 tail) hfit
    (by rw [h13, h14]; exact hl)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  rfl

/-- **The guard not taken** — the loop's exit at position 35, past the tail. -/
theorem cmpSegStride_guard_exit (tail : List Instr) {ρ : Nat → BitVec w} {c limit : Nat}
    {st : Nat → Nat} (h13 : st 13 = c) (h14 : st 14 = limit) (hl : ¬ c < limit)
    (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    exec (cmpSegStrideProgram tail) ρ (S + 1) 34 0 (memOf w st)
      = exec (cmpSegStrideProgram tail) ρ S 35 0 (memOf w st) := by
  rw [exec_blt_ge_step (S := S + 1) (hS := by omega) (cmpSegStride_s34 tail) hfit
    (by rw [h13, h14]; exact hl)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  rfl

/-! ### §C14.4 — one comparison, end to end: the segment, the tail, the guard -/

/-- **ONE COMPARISON AT STRIDE k.**  From the segment's register precondition at the
estimate bases aV/aA with the counter c, the program runs cmpSegCost + 6 steps and returns
to position 0 with the counter advanced to c + k, the accumulator incremented by the
verdict, and the precondition re-established at aV + p + k / aA + p + k with the digit
position still p.  This is §C10's transfer and §C14.3's re-entry composed into the one
step a loop induction consumes. -/
theorem cmpSegStride_iter (tail : List Instr) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {baseV baseA aV aA k p c limit acc r : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 16 ≤ aV) (hA : 16 ≤ aA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h9 : h 9 = 2 ^ r)
    (h11 : h 11 = baseV) (h12 : h 12 = baseA) (h14 : h 14 = limit)
    (h16 : h 16 = k) (h17 : h 17 = p)
    (k0 : st 0 = aV + p) (k1 : st 1 = aA + p) (k2 : st 2 = p)
    (hbV : aV + p = baseV + c) (hbA : aA + p = baseA + c)
    (hadA : h (aA + p) + 2 ^ r < 2 ^ w) (hadV : h (aV + p) + 2 ^ r < 2 ^ w)
    (hag : ∀ z, ¬ CmpCell z → st z = CmpLoopFrame h c acc z)
    (hfit : ∀ z, st z < 2 ^ w) (hacc1 : acc + 1 < 2 ^ w)
    (hcw : c + k < 2 ^ w) (hvw : baseV + (c + k) < 2 ^ w) (haw : baseA + (c + k) < 2 ^ w)
    (hpw : p < 2 ^ w) (hl : c + k < limit) (S : Nat) :
    ∃ st', (st' 0 = aV + p + k) ∧ (st' 1 = aA + p + k) ∧ (st' 2 = p) ∧
        (st' 13 = c + k) ∧
        (∀ z, ¬ CmpCell z →
          st' z = CmpLoopFrame h (c + k)
            (acc + (if digHalf h h aV aA p r then 1 else 0)) z) ∧
        (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSegStrideProgram tail) ρ (S + (cmpSegCost h aV aA p r + 6)) 0 0 (memOf w st)
        = exec (cmpSegStrideProgram tail) ρ S 0 0 (memOf w st') := by
  set g : Nat → Nat := CmpLoopFrame h c acc with hg
  have g13 : g 13 = c := by rw [hg]; exact cmpLoopFrame_13 h c acc
  have g15 : g 15 = acc := by rw [hg]; exact cmpLoopFrame_15 h c acc
  have g7 : g 7 = 0 := by rw [hg, cmpLoopFrame_7]; exact h7
  have g8 : g 8 = 1 := by rw [hg, cmpLoopFrame_8]; exact h8
  have g9 : g 9 = 2 ^ r := by rw [hg, cmpLoopFrame_9]; exact h9
  have g11 : g 11 = baseV := by rw [hg, cmpLoopFrame_11]; exact h11
  have g12 : g 12 = baseA := by rw [hg, cmpLoopFrame_12]; exact h12
  have g14 : g 14 = limit := by rw [hg, cmpLoopFrame_14]; exact h14
  have g16 : g 16 = k := by
    rw [hg, cmpLoopFrame_digit (by omega) (by omega)]; exact h16
  have g17 : g 17 = p := by
    rw [hg, cmpLoopFrame_digit (by omega) (by omega)]; exact h17
  have gfit : ∀ z, g z < 2 ^ w := by
    intro z; rw [hg]
    exact cmpLoopFrame_fit (h := h) (p := c) (acc := acc) hfitH (by omega) (by omega) z
  have gdigV : ∀ i, g (aV + i) = h (aV + i) := by
    intro i; rw [hg, cmpLoopFrame_digit (by omega) (by omega)]
  have gdigA : ∀ i, g (aA + i) = h (aA + i) := by
    intro i; rw [hg, cmpLoopFrame_digit (by omega) (by omega)]
  have hadAg : g (aA + p) + 2 ^ r < 2 ^ w := by rw [gdigA p]; exact hadA
  have hadVg : g (aV + p) + 2 ^ r < 2 ^ w := by rw [gdigV p]; exact hadV
  have hcost : cmpSegCost g aV aA p r = cmpSegCost h aV aA p r :=
    cmpSegCost_congr gdigV gdigA
  obtain ⟨s1, h6, hags, hfits, hstep1⟩ :=
    cmpSegStride_reaches_program tail (ρ := ρ) (h := g) (addrV := aV) (addrA := aA)
      (p := p) (r := r) (st := st) (S := S + 6)
      gfit (by omega) (by omega) g7 g8 g9 k0 k1 k2 hadAg hadVg hag hfit
  rw [hcost] at hstep1
  have s13 : s1 13 = c := (hags 13 (not_cmpCell_high (by omega))).trans g13
  have s15 : s1 15 = acc := (hags 15 (not_cmpCell_high (by omega))).trans g15
  have s11 : s1 11 = baseV := (hags 11 (not_cmpCell_high (by omega))).trans g11
  have s12 : s1 12 = baseA := (hags 12 (not_cmpCell_high (by omega))).trans g12
  have s14 : s1 14 = limit := (hags 14 (not_cmpCell_high (by omega))).trans g14
  have s16 : s1 16 = k := (hags 16 (not_cmpCell_high (by omega))).trans g16
  have s17 : s1 17 = p := (hags 17 (not_cmpCell_high (by omega))).trans g17
  have s7 : s1 7 = 0 := (hags 7 not_cmpCell_seven).trans g7
  obtain ⟨s2, r0, r1, r2, r13, r15, r6, rframe, rfit, hstep2⟩ :=
    cmpSegStride_tail_step tail (h := g) (baseV := baseV) (baseA := baseA) (k := k)
      (p := p) (c := c) (limit := limit) (acc := acc) (st := s1) (S := S + 1)
      g7 g11 g12 g14 g16 g17 hags hfits s13 s15 (by rw [h6]; split <;> omega)
      hacc1 hcw hvw haw hpw
  have dh : (if digHalf g g aV aA p r then 1 else 0)
      = (if digHalf h h aV aA p r then 1 else 0) := by
    rw [digHalf_congr (f := g) (g := g) (f' := h) (g' := h) (addrV := aV)
      (addrA := aA) (p := p) (r := r) gdigV gdigA]
  have s2f : s2 14 = limit := by
    rw [rframe 14 (not_cmpCell_high (by omega))]
    rw [up_ne (by decide : (14 : Nat) ≠ 13), up_ne (by decide : (14 : Nat) ≠ 15)]
    exact g14
  have fr : ∀ z, ¬ CmpCell z →
      s2 z = CmpLoopFrame h (c + k)
        (acc + (if digHalf h h aV aA p r then 1 else 0)) z := by
    intro z hz
    have key := congrFun (up_up_absorb h c acc
      (acc + (if digHalf h h aV aA p r then 1 else 0)) (c + k)) z
    simp only [CmpLoopFrame] at key ⊢
    rw [rframe z hz, h6, dh]
    rw [show g = up (up h 13 c) 15 acc from by rw [hg]; rfl]
    exact key
  have hstep3 := cmpSegStride_guard_taken tail (ρ := ρ) (st := s2) (c := c + k)
    (limit := limit) r13 s2f hl rfit (S := S)
  refine ⟨s2, ?_, ?_, r2, r13, fr, rfit, ?_⟩
  · rw [r0]; omega
  · rw [r1]; omega
  · have eA : exec (cmpSegStrideProgram tail) ρ
        (S + (cmpSegCost h aV aA p r + 6)) 0 0 (memOf w st)
        = exec (cmpSegStrideProgram tail) ρ (S + 6) 29 0 (memOf w s1) := by
      rw [show S + (cmpSegCost h aV aA p r + 6)
          = S + 6 + cmpSegCost h aV aA p r from by omega]
      exact hstep1
    have eB : exec (cmpSegStrideProgram tail) ρ (S + 6) 29 0 (memOf w s1)
        = exec (cmpSegStrideProgram tail) ρ (S + 1) 34 0 (memOf w s2) := by
      rw [show S + 6 = S + 1 + 5 from by omega]
      exact hstep2
    exact eA.trans (eB.trans hstep3)

/-! ### §C14.5 — the induction: m comparisons, and the estFuel reach -/

/-- **The verdict count at stride k.**  digHalf at each estimate's OWN address, folded
recursively with the bases shifted by the stride so the loop induction peels. -/
def strideHits (h : Nat → Nat) (baseV baseA k p r : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if digHalf h h baseV baseA p r then 1 else 0)
      + strideHits h (baseV + k) (baseA + k) k p r n

theorem strideHits_zero (h : Nat → Nat) (baseV baseA k p r : Nat) :
    strideHits h baseV baseA k p r 0 = 0 := rfl

theorem strideHits_succ (h : Nat → Nat) (baseV baseA k p r n : Nat) :
    strideHits h baseV baseA k p r (n + 1)
      = (if digHalf h h baseV baseA p r then 1 else 0)
        + strideHits h (baseV + k) (baseA + k) k p r n := rfl

/-- Each estimate contributes at most one verdict. -/
theorem strideHits_le (h : Nat → Nat) (baseV baseA k p r : Nat) :
    ∀ n, strideHits h baseV baseA k p r n ≤ n := by
  intro n
  induction n generalizing baseV baseA with
  | zero => exact Nat.zero_le 0
  | succ m ih =>
    rw [strideHits_succ]
    have hrec := ih (baseV + k) (baseA + k)
    split <;> omega

/-- **THE LOOP AT STRIDE k, AND THE estFuel REACH.**  m comparisons starting at estimate
j cost exactly estFuel h (baseV + j·k) (baseA + j·k) k p r m and accumulate exactly
strideHits, returning to position 0 with the counter at (j+m)·k + p and the frame
re-parametrized at (acc + strideHits …).  The digit position is p throughout — which is
why §C13's estFuel_le bounds the run by blockLen·(20+9p) with no drift term. -/
theorem cmpSegStride_loop (tail : List Instr) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {baseV baseA k p r limit : Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 16 ≤ baseV) (hA : 16 ≤ baseA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h9 : h 9 = 2 ^ r)
    (h11 : h 11 = baseV) (h12 : h 12 = baseA) (h14 : h 14 = limit)
    (h16 : h 16 = k) (h17 : h 17 = p) (hpw : p < 2 ^ w) :
    ∀ (m j acc : Nat) (st : Nat → Nat),
      st 0 = baseV + (j * k + p) → st 1 = baseA + (j * k + p) →
      st 2 = p → st 13 = j * k + p →
      (∀ z, ¬ CmpCell z → st z = CmpLoopFrame h (j * k + p) acc z) →
      (∀ z, st z < 2 ^ w) → acc + m < 2 ^ w →
      (∀ i, i < m → (j + i) * k + p + k < limit) →
      (∀ i, i < m → (j + i) * k + p + k < 2 ^ w) →
      (∀ i, i < m → baseV + ((j + i) * k + p + k) < 2 ^ w) →
      (∀ i, i < m → baseA + ((j + i) * k + p + k) < 2 ^ w) →
      (∀ i, i < m → h (baseV + ((j + i) * k + p)) + 2 ^ r < 2 ^ w) →
      (∀ i, i < m → h (baseA + ((j + i) * k + p)) + 2 ^ r < 2 ^ w) →
      ∀ (S : Nat),
      ∃ st', (st' 0 = baseV + ((j + m) * k + p)) ∧
          (st' 1 = baseA + ((j + m) * k + p)) ∧ (st' 2 = p) ∧
          (st' 13 = (j + m) * k + p) ∧
          (∀ z, ¬ CmpCell z →
            st' z = CmpLoopFrame h ((j + m) * k + p)
              (acc + strideHits h (baseV + j * k) (baseA + j * k) k p r m) z) ∧
          (∀ z, st' z < 2 ^ w) ∧
        exec (cmpSegStrideProgram tail) ρ
            (S + estFuel h (baseV + j * k) (baseA + j * k) k p r m) 0 0 (memOf w st)
          = exec (cmpSegStrideProgram tail) ρ S 0 0 (memOf w st') := by
  intro m
  induction m with
  | zero =>
    intro j acc st k0 k1 k2 k13 hag hfit hacc hg1 hg2 hg3 hg4 hg5 hg6 S
    simp only [Nat.add_zero, strideHits_zero, estFuel_zero] at k0 k1 k2 k13 ⊢
    exact ⟨st, k0, k1, k2, k13, hag, hfit, rfl⟩
  | succ m ih =>
    intro j acc st k0 k1 k2 k13 hag hfit hacc hg1 hg2 hg3 hg4 hg5 hg6 S
    obtain ⟨s1, n0, n1, n2, n13, nframe, nfit, hstep1⟩ :=
      cmpSegStride_iter tail (h := h) (baseV := baseV) (baseA := baseA)
        (aV := baseV + j * k) (aA := baseA + j * k) (k := k) (p := p)
        (c := j * k + p) (limit := limit) (acc := acc) (r := r) (st := st)
        (S := S + estFuel h (baseV + j * k + k) (baseA + j * k + k) k p r m)
        hfitH (by omega) (by omega) h7 h8 h9 h11 h12 h14 h16 h17
        (by omega) (by omega) k2 (by omega) (by omega)
        (by have h0 := hg6 0 (by omega)
            rw [show baseA + ((j + 0) * k + p) = (baseA + j * k) + p from by
              rw [Nat.add_zero]; omega] at h0
            exact h0)
        (by have h0 := hg5 0 (by omega)
            rw [show baseV + ((j + 0) * k + p) = (baseV + j * k) + p from by
              rw [Nat.add_zero]; omega] at h0
            exact h0)
        hag hfit (by omega)
        (by have h0 := hg2 0 (by omega); rw [Nat.add_zero] at h0; exact h0)
        (by have h0 := hg3 0 (by omega); rw [Nat.add_zero] at h0; exact h0)
        (by have h0 := hg4 0 (by omega); rw [Nat.add_zero] at h0; exact h0)
        hpw
        (by have h0 := hg1 0 (by omega); rw [Nat.add_zero] at h0; exact h0)
    obtain ⟨s2, o0, o1, o2, o13, oframe, ofit, hstep2⟩ :=
      ih (j + 1)
        (acc + (if digHalf h h (baseV + j * k) (baseA + j * k) p r then 1 else 0)) s1
        (by rw [Nat.succ_mul]; rw [n0]; omega)
        (by rw [Nat.succ_mul]; rw [n1]; omega)
        n2
        (by rw [Nat.succ_mul]; rw [n13]; omega)
        (fun z hz => by
          rw [show ((j + 1) * k) + p = ((j * k) + p) + k from by
            rw [Nat.succ_mul]; omega]
          exact nframe z hz)
        nfit
        (by split <;> omega)
        (fun i hi => by
          have h0 := hg1 (i + 1) (by omega)
          rwa [show j + (i + 1) = (j + 1) + i from by omega] at h0)
        (fun i hi => by
          have h0 := hg2 (i + 1) (by omega)
          rwa [show j + (i + 1) = (j + 1) + i from by omega] at h0)
        (fun i hi => by
          have h0 := hg3 (i + 1) (by omega)
          rwa [show j + (i + 1) = (j + 1) + i from by omega] at h0)
        (fun i hi => by
          have h0 := hg4 (i + 1) (by omega)
          rwa [show j + (i + 1) = (j + 1) + i from by omega] at h0)
        (fun i hi => by
          have h0 := hg5 (i + 1) (by omega)
          rwa [show j + (i + 1) = (j + 1) + i from by omega] at h0)
        (fun i hi => by
          have h0 := hg6 (i + 1) (by omega)
          rwa [show j + (i + 1) = (j + 1) + i from by omega] at h0)
        S
    have hF : estFuel h (baseV + (j + 1) * k) (baseA + (j + 1) * k) k p r m
        = estFuel h (baseV + j * k + k) (baseA + j * k + k) k p r m := by
      rw [show baseV + (j + 1) * k = baseV + j * k + k from by rw [Nat.succ_mul]; omega,
        show baseA + (j + 1) * k = baseA + j * k + k from by rw [Nat.succ_mul]; omega]
    rw [hF] at hstep2
    refine ⟨s2, ?_, ?_, o2, ?_, ?_, ofit, ?_⟩
    · rw [show j + (m + 1) = (j + 1) + m from by omega]; exact o0
    · rw [show j + (m + 1) = (j + 1) + m from by omega]; exact o1
    · rw [show j + (m + 1) = (j + 1) + m from by omega]; exact o13
    · intro z hz
      rw [oframe z hz]
      rw [show j + (m + 1) = (j + 1) + m from by omega]
      rw [strideHits_succ]
      rw [show baseV + (j + 1) * k = baseV + j * k + k from by rw [Nat.succ_mul]; omega]
      rw [show baseA + (j + 1) * k = baseA + j * k + k from by rw [Nat.succ_mul]; omega]
      rw [show acc + ((if digHalf h h (baseV + j * k) (baseA + j * k) p r then 1 else 0)
                + strideHits h (baseV + j * k + k) (baseA + j * k + k) k p r m)
              = (acc + (if digHalf h h (baseV + j * k) (baseA + j * k) p r then 1 else 0))
                + strideHits h (baseV + j * k + k) (baseA + j * k + k) k p r m from by omega]
    · rw [show estFuel h (baseV + j * k) (baseA + j * k) k p r (m + 1)
          = cmpSegCost h (baseV + j * k) (baseA + j * k) p r + 6
            + estFuel h (baseV + j * k + k) (baseA + j * k + k) k p r m from rfl]
      rw [show S + (cmpSegCost h (baseV + j * k) (baseA + j * k) p r + 6
              + estFuel h (baseV + j * k + k) (baseA + j * k + k) k p r m)
            = S + estFuel h (baseV + j * k + k) (baseA + j * k + k) k p r m
              + (cmpSegCost h (baseV + j * k) (baseA + j * k) p r + 6) from by omega]
      exact hstep1.trans hstep2

end SubsetSumL25.Row
