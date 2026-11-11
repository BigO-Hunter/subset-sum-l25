/-
`KapilaCmpSeg`'s two named residuals — (**A**) the `getD`-agreement transfer of
§C4–§C6 to the composed program, and (**B**) the loop induction on the comparison
counter — in one module.

§C9 left both open by name, with the seam stated: `cmpSeg_reaches` is proved on
`cmpSeg cont`, the program that executes is `cmpSegmentProgram tail = cmpSeg 29 ++ tail`,
and the two differ at position `29`, which is exactly where the segment's last step
jumps.  So the composition is *not* a congruence of `exec`; it is a replay of the
chain against an abstract program agreeing with `cmpSeg 29` on `0…28` (§C10), and then
an induction that consumes that replay plus the re-entry once per comparison (§C11).

The two rounds' corrections are carried, not absorbed: §C9's `+4 → +5` (a terminating
loop pays the advance) and this round's `+5 → +6` (a *counting* loop pays the
accumulate, `scan_loop`'s shape — the row's verdict is `0 < hitCount`, so a count is
what the loop is for).  Per comparison: `cmpSegCost + 6 ≤ 20 + 9p`.

Nothing here touches `Statement.lean`, `KapilaAlgo.cost`, `D7.agrees`'s horizon
(residual (iv)) or `PayloadCarries` (residual (ii)'s named premise, still named).
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaDigitwise
import SubsetSumL25.Row.KapilaCmpSeg

set_option autoImplicit true
set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §C10 — THE TRANSFER: §C4–§C6 replayed for an abstract program `P`

§C9 left one seam open and said so: `cmpSeg_reaches` is stated on `cmpSeg cont`, the
program that runs is `cmpSegmentProgram tail = cmpSeg 29 ++ tail`, and the two differ
at position `29` — precisely where the segment's last step jumps.  Comparing the two
`exec` chains therefore cannot be a congruence: at `29` the plain program reads
`Instr.reject` (the `getD` fallback) and the composed one reads the tail.

What *is* true — and is all the loop needs — is that a program agreeing with
`cmpSeg 29` on positions `0…28` walks the identical trace below `29`, so the segment's
whole chain replays against it.  Simulation first, as always: `sim_loop.py` arm A
records the two traces step for step over six digit blocks and finds them equal in pc
*and* memory up to the arrival at `29`, and equal there too; only the instruction
`getD 29` differs, and that difference is the composition, not a defect.

The declarations below are that replay, and they are mechanically generated from
§C4–§C6 by `gen_transfer.py` (the six rewrites are listed in its docstring; the script
prints which declarations it copied and which it skipped).  No step is re-argued: the
only things that change are the `getD` facts — `rfl` becomes `hgd` — and the word
`cont`, which becomes `29`, the position the abstract program is run into.  The
`_gen` suffix is deliberate: the free-`cont` originals stay exactly as they were, so
nothing here can break them.

`cmpSeg_reaches_program` is the only instantiation the loop uses.
-/

theorem cmpSeg_walk_head_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA n : Nat} {st : Nat → Nat}
    (hV : 11 ≤ addrV) (hA : 11 ≤ addrA) (hfitH : ∀ z, h z < 2 ^ w)
    (h2 : st 2 = n) (h8 : h 8 = 1)
    (h0 : st 0 = addrV + n) (h1 : st 1 = addrA + n)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (hn : 1 ≤ n)
    (S : Nat) :
    ∃ st', (st' 0 = addrV + (n - 1) ∧ st' 1 = addrA + (n - 1) ∧ st' 2 = n ∧
        st' 3 = h (addrV + (n - 1)) ∧ st' 4 = h (addrA + (n - 1)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w)) ∧
      exec P ρ (S + 4) 19 0 (memOf w st)
        = exec P ρ S 23 0 (memOf w st') := by
  have hb0 : st 0 < 2 ^ w := hfit 0
  have hb1 : st 1 < 2 ^ w := hfit 1
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d19 : P.getD 19 Instr.reject = Instr.sub 0 0 8 := by rw [hgd 19 (by omega)]; rfl
  rw [exec_sub_step (S := S + 4) (hS := by omega) d19 hfit (by rw [s8]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have v19 : st 0 - st 8 = addrV + (n - 1) := by rw [h0, s8]; omega
  rw [v19]
  set s1 : Nat → Nat := up st 0 (addrV + (n - 1)) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (by omega)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_zero hag
  have e1 : s1 1 = addrA + n := by
    rw [hs1, up_ne (by decide : (1 : Nat) ≠ 0)]; exact h1
  have e1' : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 0)]; exact s8
  have hb1' : s1 1 < 2 ^ w := by rw [e1]; omega
  have d20 : P.getD 20 Instr.reject = Instr.sub 1 1 8 := by rw [hgd 20 (by omega)]; rfl
  rw [exec_sub_step (S := S + 3) (hS := by omega) d20 hf1 (by rw [e1, e1']; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have v20 : s1 1 - s1 8 = addrA + (n - 1) := by rw [e1, e1']; omega
  rw [v20]
  set s2 : Nat → Nat := up s1 1 (addrA + (n - 1)) with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 (by omega)
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_one ha1
  have e0' : s2 0 = addrV + (n - 1) := by
    rw [hs2, up_ne (by decide : (0 : Nat) ≠ 1)]; exact up_eq st 0 _
  have d21 : P.getD 21 Instr.reject = Instr.load 3 0 := by rw [hgd 21 (by omega)]; rfl
  rw [exec_load_step (S := S + 2) (hS := by omega) d21 hf2]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v21 : s2 (s2 0) = h (addrV + (n - 1)) := by
    rw [e0']
    exact ha2 (addrV + (n - 1)) (not_cmpCell_high (by omega))
  rw [v21]
  set s3 : Nat → Nat := up s2 3 (h (addrV + (n - 1))) with hs3
  have hf3 : ∀ z, s3 z < 2 ^ w := upFit hf2 (hfitH _)
  have ha3 : ∀ z, ¬ CmpCell z → s3 z = h z := cmpAgree_up cmpCell_three ha2
  have e1'' : s3 1 = addrA + (n - 1) := by
    rw [hs3, up_ne (by decide : (1 : Nat) ≠ 3), hs2]; exact up_eq s1 1 _
  have d22 : P.getD 22 Instr.reject = Instr.load 4 1 := by rw [hgd 22 (by omega)]; rfl
  rw [exec_load_step (S := S + 1) (hS := by omega) d22 hf3]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have v22 : s3 (s3 1) = h (addrA + (n - 1)) := by
    rw [e1'']
    exact ha3 (addrA + (n - 1)) (not_cmpCell_high (by omega))
  rw [v22]
  refine ⟨up s3 4 (h (addrA + (n - 1))), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [up_ne (by decide : (0 : Nat) ≠ 4), hs3, up_ne (by decide : (0 : Nat) ≠ 3),
      hs2, up_ne (by decide : (0 : Nat) ≠ 1), hs1]
    exact up_eq st 0 _
  · rw [up_ne (by decide : (1 : Nat) ≠ 4), hs3, up_ne (by decide : (1 : Nat) ≠ 3), hs2]
    exact up_eq s1 1 _
  · rw [up_ne (by decide : (2 : Nat) ≠ 4), hs3, up_ne (by decide : (2 : Nat) ≠ 3),
      hs2, up_ne (by decide : (2 : Nat) ≠ 1), hs1, up_ne (by decide : (2 : Nat) ≠ 0)]
    exact h2
  · rw [up_ne (by decide : (3 : Nat) ≠ 4), hs3]
    exact up_eq s2 3 _
  · exact up_eq s3 4 _
  · exact cmpAgree_up cmpCell_four ha3
  · exact upFit hf3 (hfitH _)
  · simp

theorem cmpSeg_walk_lt_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA m : Nat} {st : Nat → Nat}
    (h3 : st 3 = h (addrV + m)) (h4 : st 4 = h (addrA + m))
    (hlt : h (addrV + m) < h (addrA + m)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    ∃ st', (st' 6 = 0) ∧ (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 3) 23 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d23 : P.getD 23 Instr.reject = Instr.blt 3 4 14 := by rw [hgd 23 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d23 hfit (by rw [h3, h4]; exact hlt)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d14 : P.getD 14 Instr.reject = Instr.rem 6 7 7 := by rw [hgd 14 (by omega)]; rfl
  rw [exec_rem_step (S := S + 2) (hS := by omega) d14 hfit]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v14 : st 7 % st 7 = 0 := by rw [s7]
  rw [v14]
  set s1 : Nat → Nat := up st 6 0 with hs1
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_six hag
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (Nat.two_pow_pos w)
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 6)]; exact s7
  have e8 : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d15 : P.getD 15 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 15 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d15 hf1 (by rw [e7, e8]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s1, up_eq st 6 0, ha1, hf1, ?_⟩
  simp

theorem cmpSeg_walk_gt_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA m : Nat} {st : Nat → Nat}
    (h3 : st 3 = h (addrV + m)) (h4 : st 4 = h (addrA + m))
    (hgt : h (addrA + m) < h (addrV + m)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    ∃ st', (st' 6 = 1) ∧ (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 5) 23 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  have hb3 : st 3 < 2 ^ w := hfit 3
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d23 : P.getD 23 Instr.reject = Instr.blt 3 4 14 := by rw [hgd 23 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d23 hfit (by rw [h3, h4]; omega)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d24 : P.getD 24 Instr.reject = Instr.sub 5 3 4 := by rw [hgd 24 (by omega)]; rfl
  rw [exec_sub_step (S := S + 4) (hS := by omega) d24 hfit (by rw [h3, h4]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have v24 : st 3 - st 4 = h (addrV + m) - h (addrA + m) := by rw [h3, h4]
  rw [v24]
  set s1 : Nat → Nat := up st 5 (h (addrV + m) - h (addrA + m)) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (by rw [h3] at hb3; omega)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have d25 : P.getD 25 Instr.reject = Instr.blt 7 5 12 := by rw [hgd 25 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d25 hf1
    (by rw [e7, hs1, up_eq]; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : P.getD 12 Instr.reject = Instr.one 6 := by rw [hgd 12 (by omega)]; rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s2 : Nat → Nat := up s1 6 1 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 h8w
  have e7' : s2 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7
  have e8' : s2 8 = 1 := by rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d13 : P.getD 13 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 13 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf2 (by rw [e7', e8']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s2, up_eq s1 6 1, ha2, hf2, ?_⟩
  simp

theorem cmpSeg_walk_eq_step_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA m : Nat} {st : Nat → Nat}
    (h0 : st 0 = addrV + m) (h1 : st 1 = addrA + m) (h2 : st 2 = m + 1)
    (h3 : st 3 = h (addrV + m)) (h4 : st 4 = h (addrA + m))
    (heq : h (addrV + m) = h (addrA + m)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (hm : 1 ≤ m)
    (S : Nat) :
    ∃ st', (st' 0 = addrV + m) ∧ (st' 1 = addrA + m) ∧ (st' 2 = m) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 5) 23 0 (memOf w st)
        = exec P ρ S 19 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d23 : P.getD 23 Instr.reject = Instr.blt 3 4 14 := by rw [hgd 23 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d23 hfit (by rw [h3, h4, heq]; omega)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d24 : P.getD 24 Instr.reject = Instr.sub 5 3 4 := by rw [hgd 24 (by omega)]; rfl
  rw [exec_sub_step (S := S + 4) (hS := by omega) d24 hfit (by rw [h3, h4]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have v24 : st 3 - st 4 = 0 := by rw [h3, h4, heq]; omega
  rw [v24]
  set s1 : Nat → Nat := up st 5 0 with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (Nat.two_pow_pos w)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have e5 : s1 5 = 0 := up_eq st 5 0
  have d25 : P.getD 25 Instr.reject = Instr.blt 7 5 12 := by rw [hgd 25 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 3) (hS := by omega) d25 hf1 (by rw [e7, e5]; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d26 : P.getD 26 Instr.reject = Instr.sub 2 2 8 := by rw [hgd 26 (by omega)]; rfl
  have e2 : s1 2 = m + 1 := by
    rw [hs1, up_ne (by decide : (2 : Nat) ≠ 5)]; exact h2
  have e8 : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 5)]; exact s8
  have hb2 : s1 2 < 2 ^ w := hf1 2
  rw [exec_sub_step (S := S + 2) (hS := by omega) d26 hf1 (by rw [e2, e8]; omega)]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v26 : s1 2 - s1 8 = m := by rw [e2, e8]; omega
  rw [v26]
  set s2 : Nat → Nat := up s1 2 m with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 (by rw [e2] at hb2; omega)
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_two ha1
  have e7' : s2 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 2)]; exact e7
  have e2' : s2 2 = m := up_eq s1 2 m
  have d27 : P.getD 27 Instr.reject = Instr.blt 7 2 19 := by rw [hgd 27 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d27 hf2 (by rw [e7', e2']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s2, ?_, ?_, e2', ha2, hf2, ?_⟩
  · rw [hs2, up_ne (by decide : (0 : Nat) ≠ 2), hs1, up_ne (by decide : (0 : Nat) ≠ 5)]
    exact h0
  · rw [hs2, up_ne (by decide : (1 : Nat) ≠ 2), hs1, up_ne (by decide : (1 : Nat) ≠ 5)]
    exact h1
  · simp

theorem cmpSeg_walk_eq_term_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA : Nat} {st : Nat → Nat}
    (h2 : st 2 = 1) (h3 : st 3 = h (addrV + 0)) (h4 : st 4 = h (addrA + 0))
    (heq : h (addrV + 0) = h (addrA + 0)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    ∃ st', (st' 6 = 1) ∧ (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 8) 23 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d23 : P.getD 23 Instr.reject = Instr.blt 3 4 14 := by rw [hgd 23 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 8) (hS := by omega) d23 hfit (by rw [h3, h4, heq]; omega)]
  rw [show S + 8 - 1 = S + 7 from rfl]
  have d24 : P.getD 24 Instr.reject = Instr.sub 5 3 4 := by rw [hgd 24 (by omega)]; rfl
  rw [exec_sub_step (S := S + 7) (hS := by omega) d24 hfit (by rw [h3, h4]; omega)]
  rw [show S + 7 - 1 = S + 6 from rfl]
  have v24 : st 3 - st 4 = 0 := by rw [h3, h4, heq]; omega
  rw [v24]
  set s1 : Nat → Nat := up st 5 0 with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (Nat.two_pow_pos w)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have e5 : s1 5 = 0 := up_eq st 5 0
  have d25 : P.getD 25 Instr.reject = Instr.blt 7 5 12 := by rw [hgd 25 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 6) (hS := by omega) d25 hf1 (by rw [e7, e5]; omega)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d26 : P.getD 26 Instr.reject = Instr.sub 2 2 8 := by rw [hgd 26 (by omega)]; rfl
  have e2 : s1 2 = 1 := by rw [hs1, up_ne (by decide : (2 : Nat) ≠ 5)]; exact h2
  have e8 : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 5)]; exact s8
  rw [exec_sub_step (S := S + 5) (hS := by omega) d26 hf1 (by rw [e2, e8])]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have v26 : s1 2 - s1 8 = 0 := by rw [e2, e8]
  rw [v26]
  set s2 : Nat → Nat := up s1 2 0 with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 (Nat.two_pow_pos w)
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_two ha1
  have e7' : s2 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 2)]; exact e7
  have e2' : s2 2 = 0 := up_eq s1 2 0
  have d27 : P.getD 27 Instr.reject = Instr.blt 7 2 19 := by rw [hgd 27 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d27 hf2 (by rw [e7', e2']; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have e8' : s2 8 = 1 := by
    rw [hs2, up_ne (by decide : (8 : Nat) ≠ 2), hs1, up_ne (by decide : (8 : Nat) ≠ 5)]
    exact s8
  have d28 : P.getD 28 Instr.reject = Instr.blt 7 8 12 := by rw [hgd 28 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d28 hf2 (by rw [e7', e8']; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : P.getD 12 Instr.reject = Instr.one 6 := by rw [hgd 12 (by omega)]; rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s3 : Nat → Nat := up s2 6 1 with hs3
  have ha3 : ∀ z, ¬ CmpCell z → s3 z = h z := cmpAgree_up cmpCell_six ha2
  have hf3 : ∀ z, s3 z < 2 ^ w := upFit hf2 h8w
  have e7'' : s3 7 = 0 := by rw [hs3, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7'
  have e8'' : s3 8 = 1 := by rw [hs3, up_ne (by decide : (8 : Nat) ≠ 6)]; exact e8'
  have d13 : P.getD 13 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 13 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf3 (by rw [e7'', e8'']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s3, up_eq s2 6 1, ha3, hf3, ?_⟩
  simp

theorem cmpSeg_walk_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA : Nat}
    (hfit : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) :
    ∀ (n : Nat) (st : Nat → Nat) (S : Nat), 1 ≤ n →
      st 0 = addrV + n → st 1 = addrA + n → st 2 = n →
      (∀ z, ¬ CmpCell z → st z = h z) → (∀ z, st z < 2 ^ w) →
      ∃ st', (st' 6 = (if cmpDigitsFrom h h addrV addrA n then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
        exec P ρ (S + walkCost h addrV addrA n) 19 0 (memOf w st)
          = exec P ρ S 29 0 (memOf w st') := by
  intro n
  induction n with
  | zero => intro _ _ _ hn; omega
  | succ m ih =>
    intro st S hn h0 h1 h2 hag hf
    rw [walkCost_succ]
    by_cases hlt : h (addrV + m) < h (addrA + m)
    · -- downward: `cmpDigitsFrom` answers `false`
      rw [if_neg (by omega : ¬ h (addrV + m) = h (addrA + m)), if_pos hlt]
      obtain ⟨s4, ⟨e0, e1, e2, e3, e4, hag4, hf4⟩, hstep4⟩ :=
        cmpSeg_walk_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
          (n := m + 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega) (S := S + 3)
      have hv : s4 3 = h (addrV + m) := by simpa using e3
      have ha : s4 4 = h (addrA + m) := by simpa using e4
      obtain ⟨st', h6, hag', hf', hstep⟩ :=
        cmpSeg_walk_lt_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
          hv ha hlt h7 h8 hag4 hf4 S
      have hcd : cmpDigitsFrom h h addrV addrA (m + 1) = false := by
        rw [cmpDigitsFrom, if_neg (by omega), decide_eq_false (by omega)]
      refine ⟨st', ?_, hag', hf', ?_⟩
      · rw [hcd]; exact h6
      · rw [show S + 7 = S + 3 + 4 from by omega, hstep4, hstep]
    · by_cases hgt : h (addrA + m) < h (addrV + m)
      · -- upward: `cmpDigitsFrom` answers `true`
        rw [if_neg (by omega : ¬ h (addrV + m) = h (addrA + m)),
          if_neg (by omega : ¬ h (addrV + m) < h (addrA + m))]
        obtain ⟨s4, ⟨e0, e1, e2, e3, e4, hag4, hf4⟩, hstep4⟩ :=
          cmpSeg_walk_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            (n := m + 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega) (S := S + 5)
        have hv : s4 3 = h (addrV + m) := by simpa using e3
        have ha : s4 4 = h (addrA + m) := by simpa using e4
        obtain ⟨st', h6, hag', hf', hstep⟩ :=
          cmpSeg_walk_gt_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            hv ha hgt h7 h8 hag4 hf4 S
        have hcd : cmpDigitsFrom h h addrV addrA (m + 1) = true := by
          rw [cmpDigitsFrom, if_neg (by omega), decide_eq_true (by omega)]
        refine ⟨st', ?_, hag', hf', ?_⟩
        · rw [hcd]; exact h6
        · rw [show S + 9 = S + 5 + 4 from by omega, hstep4, hstep]
      · -- equal digits: recurse, or take the all-equal exit at `n = 1`
        have heq : h (addrV + m) = h (addrA + m) := by omega
        rw [if_pos heq]
        have hcd : cmpDigitsFrom h h addrV addrA (m + 1)
            = cmpDigitsFrom h h addrV addrA m := by
          rw [cmpDigitsFrom, if_pos heq]
        rcases Nat.eq_zero_or_pos m with hm0 | hm
        · -- the terminal digit: every digit matched
          subst hm0
          rw [if_pos rfl]
          obtain ⟨s4, ⟨e0, e1, e2, e3, e4, hag4, hf4⟩, hstep4⟩ :=
            cmpSeg_walk_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              (n := 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega) (S := S + 8)
          have hv : s4 3 = h (addrV + 0) := by simpa using e3
          have ha : s4 4 = h (addrA + 0) := by simpa using e4
          have e2' : s4 2 = 1 := e2
          obtain ⟨st', h6, hag', hf', hstep⟩ :=
            cmpSeg_walk_eq_term_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              e2' hv ha heq h7 h8 hag4 hf4 S
          refine ⟨st', ?_, hag', hf', ?_⟩
          · rw [hcd]; rw [cmpDigitsFrom]; exact h6
          · rw [show S + 12 = S + 8 + 4 from by omega, hstep4, hstep]
        · -- a digit matched and more remain: 5 steps back to the walk head
          rw [if_neg (by omega : ¬ m = 0)]
          obtain ⟨s4, ⟨e0, e1, e2, e3, e4, hag4, hf4⟩, hstep4⟩ :=
            cmpSeg_walk_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              (n := m + 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega)
              (S := S + 5 + walkCost h addrV addrA m)
          have hv : s4 3 = h (addrV + m) := by simpa using e3
          have ha : s4 4 = h (addrA + m) := by simpa using e4
          have e2' : s4 2 = m + 1 := e2
          obtain ⟨s5, f0, f1, f2, hag5, hf5, hstep5⟩ :=
            cmpSeg_walk_eq_step_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              (m := m) e0 e1 e2' hv ha heq h7 h8 hag4 hf4 hm
              (S := S + walkCost h addrV addrA m)
          obtain ⟨st', h6, hag', hf', hstep⟩ := ih s5 S hm f0 f1 f2 hag5 hf5
          refine ⟨st', ?_, hag', hf', ?_⟩
          · rw [hcd]; exact h6
          · rw [show S + (9 + walkCost h addrV addrA m)
                = (S + 5 + walkCost h addrV addrA m) + 4 from by omega,
              hstep4,
              show S + 5 + walkCost h addrV addrA m
                = (S + walkCost h addrV addrA m) + 5 from by omega,
              hstep5, hstep]

theorem cmpSeg_head_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hV : 11 ≤ addrV) (hA : 11 ≤ addrA) (hfitH : ∀ z, h z < 2 ^ w) (h9 : h 9 = 2 ^ r)
    (h0 : st 0 = addrV + p) (h1 : st 1 = addrA + p) (h2 : st 2 = p)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w)
    (hadA : h (addrA + p) + 2 ^ r < 2 ^ w) (S : Nat) :
    ∃ st', CmpHead w h st' addrV addrA p r ∧
      exec P ρ (S + 3) 0 0 (memOf w st)
        = exec P ρ S 3 0 (memOf w st') := by
  have d0 : P.getD 0 Instr.reject = Instr.load 3 0 := by rw [hgd 0 (by omega)]; rfl
  rw [exec_load_step (S := S + 3) (hS := by omega) d0 hfit]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have v0 : st (st 0) = h (addrV + p) := by
    rw [h0]; exact hag _ (not_cmpCell_high (by omega))
  rw [v0]
  set s1 : Nat → Nat := up st 3 (h (addrV + p)) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (hfitH _)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_three hag
  have e1 : s1 1 = addrA + p := by rw [hs1, up_ne (by decide : (1 : Nat) ≠ 3)]; exact h1
  have d1 : P.getD 1 Instr.reject = Instr.load 4 1 := by rw [hgd 1 (by omega)]; rfl
  rw [exec_load_step (S := S + 2) (hS := by omega) d1 hf1]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v1 : s1 (s1 1) = h (addrA + p) := by
    rw [e1]; exact ha1 _ (not_cmpCell_high (by omega))
  rw [v1]
  set s2 : Nat → Nat := up s1 4 (h (addrA + p)) with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 (hfitH _)
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_four ha1
  have e4 : s2 4 = h (addrA + p) := up_eq s1 4 _
  have e9 : s2 9 = 2 ^ r := by
    rw [hs2, up_ne (by decide : (9 : Nat) ≠ 4), hs1, up_ne (by decide : (9 : Nat) ≠ 3),
      hag 9 not_cmpCell_nine, h9]
  have d2 : P.getD 2 Instr.reject = Instr.add 5 4 9 := by rw [hgd 2 (by omega)]; rfl
  rw [exec_add_step (S := S + 1) (hS := by omega) d2]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have v2 : s2 4 + s2 9 = h (addrA + p) + 2 ^ r := by rw [e4, e9]
  rw [v2]
  refine ⟨up s2 5 (h (addrA + p) + 2 ^ r), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [up_ne (by decide : (0 : Nat) ≠ 5), hs2, up_ne (by decide : (0 : Nat) ≠ 4),
      hs1, up_ne (by decide : (0 : Nat) ≠ 3)]
    exact h0
  · rw [up_ne (by decide : (1 : Nat) ≠ 5), hs2, up_ne (by decide : (1 : Nat) ≠ 4),
      hs1, up_ne (by decide : (1 : Nat) ≠ 3)]
    exact h1
  · rw [up_ne (by decide : (2 : Nat) ≠ 5), hs2, up_ne (by decide : (2 : Nat) ≠ 4),
      hs1, up_ne (by decide : (2 : Nat) ≠ 3)]
    exact h2
  · rw [up_ne (by decide : (3 : Nat) ≠ 5), hs2, up_ne (by decide : (3 : Nat) ≠ 4)]
    exact up_eq st 3 _
  · rw [up_ne (by decide : (4 : Nat) ≠ 5)]
    exact up_eq s1 4 _
  · exact up_eq s2 5 _
  · exact cmpAgree_up cmpCell_five ha2
  · exact upFit hf2 hadA
  · simp

theorem cmpSeg_above_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA p r)
    (hnlt : ¬ h (addrV + p) < h (addrA + p) + 2 ^ r)
    (habove : h (addrA + p) + 2 ^ r < h (addrV + p))
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 4) 3 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : P.getD 3 Instr.reject = Instr.blt 3 5 8 := by rw [hgd 3 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hnlt)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have d4 : P.getD 4 Instr.reject = Instr.blt 5 3 12 := by rw [hgd 4 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d4 hfit (by rw [k3, k5]; exact habove)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : P.getD 12 Instr.reject = Instr.one 6 := by rw [hgd 12 (by omega)]; rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s1 : Nat → Nat := up st 6 1 with hs1
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_six hag
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit h8w
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 6)]; exact s7
  have e8 : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d13 : P.getD 13 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 13 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf1 (by rw [e7, e8]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have hdh : digHalf h h addrV addrA p r = true := by
    rw [digHalf, if_pos habove]
  refine ⟨s1, ?_, ha1, hf1, ?_⟩
  · rw [hdh]; exact up_eq st 6 1
  · simp

theorem cmpSeg_miss_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA p r) (h9 : h 9 = 2 ^ r)
    (hvlt : h (addrV + p) < h (addrA + p) + 2 ^ r)
    (halt : h (addrA + p) < h (addrV + p) + 2 ^ r)
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 5) 3 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d3 : P.getD 3 Instr.reject = Instr.blt 3 5 8 := by rw [hgd 3 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 5) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d8 : P.getD 8 Instr.reject = Instr.add 5 3 9 := by rw [hgd 8 (by omega)]; rfl
  rw [exec_add_step (S := S + 4) (hS := by omega) d8]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have e3 : st 3 = h (addrV + p) := k3
  have e9 : st 9 = 2 ^ r := by rw [hag 9 not_cmpCell_nine]; exact h9
  rw [show st 3 + st 9 = h (addrV + p) + 2 ^ r from by rw [e3, e9]]
  set s1 : Nat → Nat := up st 5 (h (addrV + p) + 2 ^ r) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit hadV
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e4 : s1 4 = h (addrA + p) := by
    rw [hs1, up_ne (by decide : (4 : Nat) ≠ 5)]; exact k4
  have e5 : s1 5 = h (addrV + p) + 2 ^ r := up_eq st 5 _
  have d9 : P.getD 9 Instr.reject = Instr.blt 4 5 14 := by rw [hgd 9 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact halt)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d14 : P.getD 14 Instr.reject = Instr.rem 6 7 7 := by rw [hgd 14 (by omega)]; rfl
  rw [exec_rem_step (S := S + 2) (hS := by omega) d14 hf1]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have e7' : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  rw [show s1 7 % s1 7 = 0 from by rw [e7']]
  set s2 : Nat → Nat := up s1 6 0 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 (Nat.two_pow_pos w)
  have e7'' : s2 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7'
  have e8' : s2 8 = 1 := by
    rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6), hs1, up_ne (by decide : (8 : Nat) ≠ 5)]
    exact s8
  have d15 : P.getD 15 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 15 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d15 hf2 (by rw [e7'', e8']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have hdh : digHalf h h addrV addrA p r = false := by
    have ht : 0 < 2 ^ r := Nat.two_pow_pos r
    have hb3 : ¬ h (addrV + p) = h (addrA + p) + 2 ^ r := by omega
    have hb4 : ¬ h (addrA + p) = h (addrV + p) + 2 ^ r := by omega
    rw [digHalf, if_neg (by omega : ¬ h (addrA + p) + 2 ^ r < h (addrV + p)),
      if_neg (by omega : ¬ h (addrV + p) + 2 ^ r < h (addrA + p)), if_neg hb3, if_neg hb4]
  refine ⟨s2, ?_, ha2, hf2, ?_⟩
  · rw [hdh]; exact up_eq s1 6 0
  · simp

theorem cmpSeg_below_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA p r) (h9 : h 9 = 2 ^ r)
    (hvlt : h (addrV + p) < h (addrA + p) + 2 ^ r)
    (hnat : ¬ h (addrA + p) < h (addrV + p) + 2 ^ r)
    (hbelow : h (addrV + p) + 2 ^ r < h (addrA + p))
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 6) 3 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : P.getD 3 Instr.reject = Instr.blt 3 5 8 := by rw [hgd 3 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 6) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d8 : P.getD 8 Instr.reject = Instr.add 5 3 9 := by rw [hgd 8 (by omega)]; rfl
  rw [exec_add_step (S := S + 5) (hS := by omega) d8]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have e9 : st 9 = 2 ^ r := by rw [hag 9 not_cmpCell_nine]; exact h9
  rw [show st 3 + st 9 = h (addrV + p) + 2 ^ r from by rw [k3, e9]]
  set s1 : Nat → Nat := up st 5 (h (addrV + p) + 2 ^ r) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit hadV
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e4 : s1 4 = h (addrA + p) := by
    rw [hs1, up_ne (by decide : (4 : Nat) ≠ 5)]; exact k4
  have e5 : s1 5 = h (addrV + p) + 2 ^ r := up_eq st 5 _
  have d9 : P.getD 9 Instr.reject = Instr.blt 4 5 14 := by rw [hgd 9 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact hnat)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have d10 : P.getD 10 Instr.reject = Instr.blt 5 4 12 := by rw [hgd 10 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d10 hf1 (by rw [e4, e5]; exact hbelow)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : P.getD 12 Instr.reject = Instr.one 6 := by rw [hgd 12 (by omega)]; rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s2 : Nat → Nat := up s1 6 1 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 h8w
  have e7 : s2 7 = 0 := by
    rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6), hs1, up_ne (by decide : (7 : Nat) ≠ 5)]
    exact s7
  have e8' : s2 8 = 1 := by
    rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6), hs1, up_ne (by decide : (8 : Nat) ≠ 5)]
    exact s8
  have d13 : P.getD 13 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 13 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf2 (by rw [e7, e8']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have hdh : digHalf h h addrV addrA p r = true := by
    rw [digHalf, if_neg (by omega : ¬ h (addrA + p) + 2 ^ r < h (addrV + p)),
      if_pos hbelow]
  refine ⟨s2, ?_, ha2, hf2, ?_⟩
  · rw [hdh]; exact up_eq s1 6 1
  · simp

theorem cmpSeg_tieV_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (hH : CmpHead w h st addrV addrA p r)
    (hnlt : ¬ h (addrV + p) < h (addrA + p) + 2 ^ r)
    (hnab : ¬ h (addrA + p) + 2 ^ r < h (addrV + p))
    (h7 : h 7 = 0) (h8 : h 8 = 1) (hp : 1 ≤ p) (S : Nat) :
    ∃ st', (st' 0 = addrV + p) ∧ (st' 1 = addrA + p) ∧ (st' 2 = p) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 4) 3 0 (memOf w st)
        = exec P ρ S 19 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s2 : st 2 = p := k2
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : P.getD 3 Instr.reject = Instr.blt 3 5 8 := by rw [hgd 3 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hnlt)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have d4 : P.getD 4 Instr.reject = Instr.blt 5 3 12 := by rw [hgd 4 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 3) (hS := by omega) d4 hfit (by rw [k3, k5]; exact hnab)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d5 : P.getD 5 Instr.reject = Instr.add 6 7 8 := by rw [hgd 5 (by omega)]; rfl
  rw [exec_add_step (S := S + 2) (hS := by omega) d5]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have e7 : st 7 = 0 := s7
  have e8 : st 8 = 1 := s8
  rw [show st 7 + st 8 = 1 from by rw [e7, e8]]
  set s1 : Nat → Nat := up st 6 1 with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit h8w
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_six hag
  have e2 : s1 2 = p := by rw [hs1, up_ne (by decide : (2 : Nat) ≠ 6)]; exact s2
  have e7' : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 6)]; exact s7
  have d6 : P.getD 6 Instr.reject = Instr.blt 7 2 19 := by rw [hgd 6 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d6 hf1 (by rw [e7', e2]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s1, ?_, ?_, ?_, ha1, hf1, ?_⟩
  · rw [hs1, up_ne (by decide : (0 : Nat) ≠ 6)]; exact k0
  · rw [hs1, up_ne (by decide : (1 : Nat) ≠ 6)]; exact k1
  · exact e2
  · simp

theorem cmpSeg_tieA_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (hH : CmpHead w h st addrV addrA p r) (h9 : h 9 = 2 ^ r)
    (hvlt : h (addrV + p) < h (addrA + p) + 2 ^ r)
    (hnat : ¬ h (addrA + p) < h (addrV + p) + 2 ^ r)
    (hnbe : ¬ h (addrV + p) + 2 ^ r < h (addrA + p))
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (hp : 1 ≤ p) (S : Nat) :
    ∃ st', (st' 0 = addrA + p) ∧ (st' 1 = addrV + p) ∧ (st' 2 = p) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 8) 3 0 (memOf w st)
        = exec P ρ S 19 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d3 : P.getD 3 Instr.reject = Instr.blt 3 5 8 := by rw [hgd 3 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 8) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 8 - 1 = S + 7 from rfl]
  have d8 : P.getD 8 Instr.reject = Instr.add 5 3 9 := by rw [hgd 8 (by omega)]; rfl
  rw [exec_add_step (S := S + 7) (hS := by omega) d8]
  rw [show S + 7 - 1 = S + 6 from rfl]
  have e9 : st 9 = 2 ^ r := by rw [hag 9 not_cmpCell_nine]; exact h9
  rw [show st 3 + st 9 = h (addrV + p) + 2 ^ r from by rw [k3, e9]]
  set s1 : Nat → Nat := up st 5 (h (addrV + p) + 2 ^ r) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit hadV
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e4 : s1 4 = h (addrA + p) := by
    rw [hs1, up_ne (by decide : (4 : Nat) ≠ 5)]; exact k4
  have e5 : s1 5 = h (addrV + p) + 2 ^ r := up_eq st 5 _
  have d9 : P.getD 9 Instr.reject = Instr.blt 4 5 14 := by rw [hgd 9 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 6) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact hnat)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d10 : P.getD 10 Instr.reject = Instr.blt 5 4 12 := by rw [hgd 10 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d10 hf1 (by rw [e4, e5]; exact hnbe)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have e2 : s1 2 = p := by
    rw [hs1, up_ne (by decide : (2 : Nat) ≠ 5)]; exact k2
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have d11 : P.getD 11 Instr.reject = Instr.blt 7 2 16 := by rw [hgd 11 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 4) (hS := by omega) d11 hf1 (by rw [e7, e2]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  -- 16, 17, 18: exchange cells 0 and 1 through cell 10
  have d16 : P.getD 16 Instr.reject = Instr.add 10 0 7 := by rw [hgd 16 (by omega)]; rfl
  have e7' : s1 7 = 0 := e7
  have e0 : s1 0 = addrV + p := by
    rw [hs1, up_ne (by decide : (0 : Nat) ≠ 5)]; exact k0
  rw [exec_add_step (S := S + 3) (hS := by omega) d16]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have hb0 : s1 0 < 2 ^ w := hf1 0
  rw [show s1 0 + s1 7 = addrV + p from by rw [e0, e7', Nat.add_zero]]
  set s2 : Nat → Nat := up s1 10 (addrV + p) with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 (by rw [e0] at hb0; omega)
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_ten ha1
  have e1 : s2 1 = addrA + p := by
    rw [hs2, up_ne (by decide : (1 : Nat) ≠ 10), hs1, up_ne (by decide : (1 : Nat) ≠ 5)]
    exact k1
  have e72 : s2 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 10)]; exact e7'
  have d17 : P.getD 17 Instr.reject = Instr.add 0 1 7 := by rw [hgd 17 (by omega)]; rfl
  rw [exec_add_step (S := S + 2) (hS := by omega) d17]
  rw [show S + 2 - 1 = S + 1 from rfl]
  rw [show s2 1 + s2 7 = addrA + p from by rw [e1, e72, Nat.add_zero]]
  have hb1 : s2 1 < 2 ^ w := hf2 1
  set s3 : Nat → Nat := up s2 0 (addrA + p) with hs3
  have hf3 : ∀ z, s3 z < 2 ^ w := upFit hf2 (by rw [e1] at hb1; omega)
  have ha3 : ∀ z, ¬ CmpCell z → s3 z = h z := cmpAgree_up cmpCell_zero ha2
  have e10 : s3 10 = addrV + p := by
    rw [hs3, up_ne (by decide : (10 : Nat) ≠ 0)]; exact up_eq s1 10 _
  have e73 : s3 7 = 0 := by rw [hs3, up_ne (by decide : (7 : Nat) ≠ 0)]; exact e72
  have d18 : P.getD 18 Instr.reject = Instr.add 1 10 7 := by rw [hgd 18 (by omega)]; rfl
  rw [exec_add_step (S := S + 1) (hS := by omega) d18]
  rw [show S + 1 - 1 = S + 0 from rfl]
  rw [show s3 10 + s3 7 = addrV + p from by rw [e10, e73, Nat.add_zero]]
  refine ⟨up s3 1 (addrV + p), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [up_ne (by decide : (0 : Nat) ≠ 1), hs3]; exact up_eq s2 0 _
  · rw [up_eq]
  · rw [up_ne (by decide : (2 : Nat) ≠ 1), hs3, up_ne (by decide : (2 : Nat) ≠ 0),
      hs2, up_ne (by decide : (2 : Nat) ≠ 10), hs1, up_ne (by decide : (2 : Nat) ≠ 5)]
    exact k2
  · exact cmpAgree_up cmpCell_one ha3
  · exact upFit hf3 (by rw [e0] at hb0; omega)
  · simp

theorem cmpSeg_tieV_zero_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA 0 r)
    (hnlt : ¬ h (addrV + 0) < h (addrA + 0) + 2 ^ r)
    (hnab : ¬ h (addrA + 0) + 2 ^ r < h (addrV + 0))
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA 0 r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 7) 3 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s2 : st 2 = 0 := k2
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : P.getD 3 Instr.reject = Instr.blt 3 5 8 := by rw [hgd 3 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 7) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hnlt)]
  rw [show S + 7 - 1 = S + 6 from rfl]
  have d4 : P.getD 4 Instr.reject = Instr.blt 5 3 12 := by rw [hgd 4 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 6) (hS := by omega) d4 hfit (by rw [k3, k5]; exact hnab)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d5 : P.getD 5 Instr.reject = Instr.add 6 7 8 := by rw [hgd 5 (by omega)]; rfl
  rw [exec_add_step (S := S + 5) (hS := by omega) d5]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have e7 : st 7 = 0 := s7
  have e8 : st 8 = 1 := s8
  rw [show st 7 + st 8 = 1 from by rw [e7, e8]]
  set s1 : Nat → Nat := up st 6 1 with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit h8w
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_six hag
  have e2 : s1 2 = 0 := by rw [hs1, up_ne (by decide : (2 : Nat) ≠ 6)]; exact s2
  have e7' : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 6)]; exact s7
  have d6 : P.getD 6 Instr.reject = Instr.blt 7 2 19 := by rw [hgd 6 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d6 hf1 (by rw [e7', e2]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have e8' : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d7 : P.getD 7 Instr.reject = Instr.blt 7 8 12 := by rw [hgd 7 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d7 hf1 (by rw [e7', e8']; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : P.getD 12 Instr.reject = Instr.one 6 := by rw [hgd 12 (by omega)]; rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s2' : Nat → Nat := up s1 6 1 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2' z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2' z < 2 ^ w := upFit hf1 h8w
  have e72 : s2' 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7'
  have e82 : s2' 8 = 1 := by rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6)]; exact e8'
  have d13 : P.getD 13 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 13 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf2 (by rw [e72, e82]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have hdh : digHalf h h addrV addrA 0 r = true := by
    have ht : 0 < 2 ^ r := Nat.two_pow_pos r
    have hb3 : h (addrV + 0) = h (addrA + 0) + 2 ^ r := by omega
    rw [digHalf, if_neg (by omega : ¬ h (addrA + 0) + 2 ^ r < h (addrV + 0)),
      if_neg (by omega : ¬ h (addrV + 0) + 2 ^ r < h (addrA + 0)), if_pos hb3]
    exact cmpDigitsFrom_zero h h addrV addrA
  refine ⟨s2', ?_, ha2, hf2, ?_⟩
  · rw [hdh]; exact up_eq s1 6 1
  · simp

theorem cmpSeg_tieA_zero_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA 0 r) (h9 : h 9 = 2 ^ r)
    (hvlt : h (addrV + 0) < h (addrA + 0) + 2 ^ r)
    (hnat : ¬ h (addrA + 0) < h (addrV + 0) + 2 ^ r)
    (hnbe : ¬ h (addrV + 0) + 2 ^ r < h (addrA + 0))
    (hadV : h (addrV + 0) + 2 ^ r < 2 ^ w)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA 0 r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec P ρ (S + 7) 3 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s2 : st 2 = 0 := k2
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : P.getD 3 Instr.reject = Instr.blt 3 5 8 := by rw [hgd 3 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 7) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 7 - 1 = S + 6 from rfl]
  have d8 : P.getD 8 Instr.reject = Instr.add 5 3 9 := by rw [hgd 8 (by omega)]; rfl
  rw [exec_add_step (S := S + 6) (hS := by omega) d8]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have e9 : st 9 = 2 ^ r := by rw [hag 9 not_cmpCell_nine]; exact h9
  rw [show st 3 + st 9 = h (addrV + 0) + 2 ^ r from by rw [k3, e9]]
  set s1 : Nat → Nat := up st 5 (h (addrV + 0) + 2 ^ r) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit hadV
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e4 : s1 4 = h (addrA + 0) := by
    rw [hs1, up_ne (by decide : (4 : Nat) ≠ 5)]; exact k4
  have e5 : s1 5 = h (addrV + 0) + 2 ^ r := up_eq st 5 _
  have d9 : P.getD 9 Instr.reject = Instr.blt 4 5 14 := by rw [hgd 9 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact hnat)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d10 : P.getD 10 Instr.reject = Instr.blt 5 4 12 := by rw [hgd 10 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d10 hf1 (by rw [e4, e5]; exact hnbe)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have e2 : s1 2 = 0 := by rw [hs1, up_ne (by decide : (2 : Nat) ≠ 5)]; exact s2
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have d11 : P.getD 11 Instr.reject = Instr.blt 7 2 16 := by rw [hgd 11 (by omega)]; rfl
  rw [exec_blt_ge_step (S := S + 3) (hS := by omega) d11 hf1 (by rw [e7, e2]; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : P.getD 12 Instr.reject = Instr.one 6 := by rw [hgd 12 (by omega)]; rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s2' : Nat → Nat := up s1 6 1 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2' z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2' z < 2 ^ w := upFit hf1 h8w
  have e72 : s2' 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7
  have e82 : s2' 8 = 1 := by
    rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6), hs1, up_ne (by decide : (8 : Nat) ≠ 5)]
    exact s8
  have d13 : P.getD 13 Instr.reject = Instr.blt 7 8 29 := by rw [hgd 13 (by omega)]; rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf2 (by rw [e72, e82]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have hdh : digHalf h h addrV addrA 0 r = true := by
    have ht : 0 < 2 ^ r := Nat.two_pow_pos r
    have hb3 : ¬ h (addrV + 0) = h (addrA + 0) + 2 ^ r := by omega
    have hb4 : h (addrA + 0) = h (addrV + 0) + 2 ^ r := by omega
    rw [digHalf, if_neg (by omega : ¬ h (addrA + 0) + 2 ^ r < h (addrV + 0)),
      if_neg (by omega : ¬ h (addrV + 0) + 2 ^ r < h (addrA + 0)), if_neg hb3, if_pos hb4]
    exact cmpDigitsFrom_zero h h addrA addrV
  refine ⟨s2', ?_, ha2, hf2, ?_⟩
  · rw [hdh]; exact up_eq s1 6 1
  · simp

theorem cmpSeg_reaches_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
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
      exec P ρ (S + cmpSegCost h addrV addrA p r) 0 0 (memOf w st)
        = exec P ρ S 29 0 (memOf w st') := by
  unfold cmpSegCost
  by_cases b1 : h (addrV + p) < h (addrA + p) + 2 ^ r
  · rw [if_pos b1]
    by_cases b2 : h (addrA + p) < h (addrV + p) + 2 ^ r
    · -- the decided miss: 8 = 3 + 5
      rw [if_pos b2]
      obtain ⟨s3, hH, hstep1⟩ :=
        cmpSeg_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 5)
      obtain ⟨st', h6, hag', hf', hstep2⟩ :=
        cmpSeg_miss_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hH h9 b1 b2 hadV h7 h8 S
      exact ⟨st', h6, hag', hf', by rw [show S + 8 = S + 5 + 3 from by omega, hstep1, hstep2]⟩
    · rw [if_neg b2]
      by_cases b3 : h (addrV + p) + 2 ^ r < h (addrA + p)
      · -- the V-side decided hit: 9 = 3 + 6
        rw [if_pos b3]
        obtain ⟨s3, hH, hstep1⟩ :=
          cmpSeg_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 6)
        obtain ⟨st', h6, hag', hf', hstep2⟩ :=
          cmpSeg_below_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hH h9 b1 b2 b3 hadV h7 h8 S
        exact ⟨st', h6, hag', hf',
          by rw [show S + 9 = S + 6 + 3 from by omega, hstep1, hstep2]⟩
      · rw [if_neg b3]
        by_cases hp0 : p = 0
        · -- the A-side tie at `p = 0`: hit outright, 10 = 3 + 7
          rw [if_pos hp0]
          subst hp0
          obtain ⟨s3, hH, hstep1⟩ :=
            cmpSeg_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              (p := 0) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 7)
          obtain ⟨st', h6, hag', hf', hstep2⟩ :=
            cmpSeg_tieA_zero_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              (r := r) hH h9 b1 b2 b3 hadV h7 h8 S
          exact ⟨st', h6, hag', hf',
            by rw [show S + 10 = S + 7 + 3 from by omega, hstep1, hstep2]⟩
        · -- the A-side tie: swap, then the walk
          rw [if_neg hp0]
          have hp1 : 1 ≤ p := by omega
          obtain ⟨s3, hH, hstep1⟩ :=
            cmpSeg_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA
              (S := S + 8 + walkCost h addrA addrV p)
          obtain ⟨s4, g0, g1, g2, hag4, hf4, hstep2⟩ :=
            cmpSeg_tieA_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
              (p := p) (r := r) hfitH hV hA hH h9 b1 b2 b3 hadV h7 h8 hp1
              (S := S + walkCost h addrA addrV p)
          obtain ⟨st', h6, hag', hf', hstep3⟩ :=
            cmpSeg_walk_gen (hgd := hgd) (h := h) (addrV := addrA) (addrA := addrV)
              hfitH hA hV h7 h8 p s4 S hp1 g0 g1 g2 hag4 hf4
          have hdh : digHalf h h addrV addrA p r = cmpDigitsFrom h h addrA addrV p := by
            have ht : 0 < 2 ^ r := Nat.two_pow_pos r
            have hb3 : ¬ h (addrV + p) = h (addrA + p) + 2 ^ r := by omega
            have hb4 : h (addrA + p) = h (addrV + p) + 2 ^ r := by omega
            rw [digHalf, if_neg (by omega : ¬ h (addrA + p) + 2 ^ r < h (addrV + p)),
              if_neg (by omega : ¬ h (addrV + p) + 2 ^ r < h (addrA + p)), if_neg hb3,
              if_pos hb4]
          refine ⟨st', ?_, hag', hf', ?_⟩
          · rw [hdh]; exact h6
          · rw [show S + (11 + walkCost h addrA addrV p)
                = (S + 8 + walkCost h addrA addrV p) + 3 from by omega,
              hstep1,
              show S + 8 + walkCost h addrA addrV p
                = (S + walkCost h addrA addrV p) + 8 from by omega,
              hstep2, hstep3]
  · rw [if_neg b1]
    by_cases b4 : h (addrA + p) + 2 ^ r < h (addrV + p)
    · -- the A-side decided hit: 7 = 3 + 4
      rw [if_pos b4]
      obtain ⟨s3, hH, hstep1⟩ :=
        cmpSeg_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 4)
      obtain ⟨st', h6, hag', hf', hstep2⟩ :=
        cmpSeg_above_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hH b1 b4 h7 h8 S
      exact ⟨st', h6, hag', hf', by rw [show S + 7 = S + 4 + 3 from by omega, hstep1, hstep2]⟩
    · rw [if_neg b4]
      by_cases hp0 : p = 0
      · -- the V-side tie at `p = 0`: hit outright, 10 = 3 + 7
        rw [if_pos hp0]
        subst hp0
        obtain ⟨s3, hH, hstep1⟩ :=
          cmpSeg_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            (p := 0) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 7)
        obtain ⟨st', h6, hag', hf', hstep2⟩ :=
          cmpSeg_tieV_zero_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            (r := r) hH b1 b4 h7 h8 S
        exact ⟨st', h6, hag', hf',
          by rw [show S + 10 = S + 7 + 3 from by omega, hstep1, hstep2]⟩
      · -- the V-side tie: the walk without the swap
        rw [if_neg hp0]
        have hp1 : 1 ≤ p := by omega
        obtain ⟨s3, hH, hstep1⟩ :=
          cmpSeg_head_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA
            (S := S + 4 + walkCost h addrV addrA p)
        obtain ⟨s4, g0, g1, g2, hag4, hf4, hstep2⟩ :=
          cmpSeg_tieV_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hfitH hV hA hH b1 b4 h7 h8 hp1
            (S := S + walkCost h addrV addrA p)
        obtain ⟨st', h6, hag', hf', hstep3⟩ :=
          cmpSeg_walk_gen (hgd := hgd) (h := h) (addrV := addrV) (addrA := addrA)
            hfitH hV hA h7 h8 p s4 S hp1 g0 g1 g2 hag4 hf4
        have hdh : digHalf h h addrV addrA p r = cmpDigitsFrom h h addrV addrA p := by
          have ht : 0 < 2 ^ r := Nat.two_pow_pos r
          have hb3 : h (addrV + p) = h (addrA + p) + 2 ^ r := by omega
          rw [digHalf, if_neg (by omega : ¬ h (addrA + p) + 2 ^ r < h (addrV + p)),
            if_neg (by omega : ¬ h (addrV + p) + 2 ^ r < h (addrA + p)), if_pos hb3]
        refine ⟨st', ?_, hag', hf', ?_⟩
        · rw [hdh]; exact h6
        · rw [show S + (7 + walkCost h addrV addrA p)
              = (S + 4 + walkCost h addrV addrA p) + 3 from by omega,
            hstep1,
            show S + 4 + walkCost h addrV addrA p
              = (S + walkCost h addrV addrA p) + 4 from by omega,
            hstep2, hstep3]

theorem cmpSeg_reaches_bound_gen {P : List Instr} (hgd : ∀ i, i ≤ 28 → P.getD i Instr.reject = (cmpSeg 29).getD i Instr.reject) {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h9 : h 9 = 2 ^ r)
    (k0 : st 0 = addrV + p) (k1 : st 1 = addrA + p) (k2 : st 2 = p)
    (hadA : h (addrA + p) + 2 ^ r < 2 ^ w)
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w)
    (S : Nat) :
    ∃ k, k ≤ cmpSegFuel p ∧
      ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
        exec P ρ (S + k) 0 0 (memOf w st)
          = exec P ρ S 29 0 (memOf w st') := by
  obtain ⟨st', h6, hag', hf', hstep⟩ := cmpSeg_reaches_gen hgd hfitH hV hA h7 h8 h9 k0 k1 k2
    hadA hadV hag hfit S
  exact ⟨_, cmpSegCost_le h addrV addrA p r, st', h6, hag', hf', hstep⟩

/-- **THE ADJUDICATED ENTRY REACH, ON THE REAL PROGRAM.**  Instantiate §C10's
chain at `P := cmpSegmentProgram tail`, whose agreement hypothesis is exactly
`cmpSegment_getD`.  This is the statement §C9 could not make: the segment's own run,
from position `0` of the *composed* program, reaches position `29` in exactly
`cmpSegCost` steps with the verdict in cell `6` and the frame intact — the same
state-level conclusion as `cmpSeg_reaches`, but on the bytes that actually execute. -/
theorem cmpSeg_reaches_program (tail : List Instr) {ρ : Nat → BitVec w} {h : Nat → Nat}
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
      exec (cmpSegmentProgram tail) ρ (S + cmpSegCost h addrV addrA p r) 0 0 (memOf w st)
        = exec (cmpSegmentProgram tail) ρ S 29 0 (memOf w st') :=
  cmpSeg_reaches_gen (fun i hi => cmpSegment_getD tail hi) hfitH hV hA h7 h8 h9 k0 k1 k2 hadA hadV hag hfit S


/-! ### §C11 — the loop: one counting iteration, and the induction on `p`

§C10 closed the entry reach on the real program and §C9's `cmpSeg_loopStep` closed the
re-entry *given* `p` in cell `13`.  What a loop adds on top is the **accumulator**:
`KapilaLoop`'s `scan_loop` carries `acc + hitCount …` across its iterations, and the
row's verdict is `0 < hitCount` (`hitCount_pos_iff`).  So the iteration tail here is
`cmpSegLoopTail` plus **one** instruction — the accumulate — and the per-comparison
charge is `cmpSegCost + 6`, **not** `+ 5`.

That is the second stated-shape correction of this lane (the first was `+4 → +5` in
§C9): `cmpSeg_loopCharge_le`'s `19 + 9p` is the price of a loop that does *not* count.
A counting loop pays `20 + 9p`.  Measured before proved, as always — `sim_loop.py`
arm B: at `cmpSegCost + 5` the run is still inside the tail at pc `34`, so the sixth
step is real; arm C then checks that `cmpLoopFuel` is exactly the halting fuel and that
the accumulator's increments sum to `cmpLoopHits` over six digit blocks.

The frame is parametrized by `(p, acc)` — `CmpLoopFrame h p acc = up (up h 13 p) 15 acc`
— so each iteration's `up (up …) 13 (p+1)` lands back on the same shape and the
induction needs one rewrite per iteration instead of a growing nest of `up`s.  Cell
`15` is the accumulator.  It is free because the digits live at `addrV + i`,
`addrA + i` with `16 ≤ addrV`, `addrA`: the layout hypothesis this module *states*
rather than assumes, and the reason every digit agreement below goes through
`addrV + i ≠ 13`, `addrV + i ≠ 15`.
-/

/-- The counting iteration tail: the accumulator takes the verdict (cell `6`) the
segment has just written, then `cmpSegLoopTail`'s five — advance, reload, guarded
back-edge.  Six instructions, at positions `29…34`. -/
def cmpHitTail : List Instr := [ .add 15 15 6 ] ++ cmpSegLoopTail

theorem cmpHitTail_length : cmpHitTail.length = 6 := rfl

/-- The loop's frame at counter `p` and accumulator `acc`.  `h` is the caller's frame
and does not change across iterations; `13` and `15` are the two cells the loop owns. -/
def CmpLoopFrame (h : Nat → Nat) (p acc : Nat) : Nat → Nat := up (up h 13 p) 15 acc

theorem cmpLoopFrame_7 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 7 = h 7 := by
  unfold CmpLoopFrame
  rw [up_ne (by decide : (7 : Nat) ≠ 15), up_ne (by decide : (7 : Nat) ≠ 13)]

theorem cmpLoopFrame_8 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 8 = h 8 := by
  unfold CmpLoopFrame
  rw [up_ne (by decide : (8 : Nat) ≠ 15), up_ne (by decide : (8 : Nat) ≠ 13)]

theorem cmpLoopFrame_9 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 9 = h 9 := by
  unfold CmpLoopFrame
  rw [up_ne (by decide : (9 : Nat) ≠ 15), up_ne (by decide : (9 : Nat) ≠ 13)]

theorem cmpLoopFrame_11 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 11 = h 11 := by
  unfold CmpLoopFrame
  rw [up_ne (by decide : (11 : Nat) ≠ 15), up_ne (by decide : (11 : Nat) ≠ 13)]

theorem cmpLoopFrame_12 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 12 = h 12 := by
  unfold CmpLoopFrame
  rw [up_ne (by decide : (12 : Nat) ≠ 15), up_ne (by decide : (12 : Nat) ≠ 13)]

theorem cmpLoopFrame_14 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 14 = h 14 := by
  unfold CmpLoopFrame
  rw [up_ne (by decide : (14 : Nat) ≠ 15), up_ne (by decide : (14 : Nat) ≠ 13)]

theorem cmpLoopFrame_13 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 13 = p := by
  unfold CmpLoopFrame
  rw [up_ne (by decide : (13 : Nat) ≠ 15), up_eq]

theorem cmpLoopFrame_15 (h : Nat → Nat) (p acc : Nat) : CmpLoopFrame h p acc 15 = acc := by
  unfold CmpLoopFrame
  rw [up_eq]

/-- The loop frame keeps the word fit, given the fit of the base frame and of the two
cells the loop writes. -/
theorem cmpLoopFrame_fit {h : Nat → Nat} {w p acc : Nat} (hfit : ∀ z, h z < 2 ^ w)
    (hp : p < 2 ^ w) (ha : acc < 2 ^ w) : ∀ z, CmpLoopFrame h p acc z < 2 ^ w := by
  intro z
  unfold CmpLoopFrame
  by_cases hz15 : z = 15
  · subst hz15; rw [up_eq]; exact ha
  · rw [up_ne hz15]
    by_cases hz13 : z = 13
    · subst hz13; rw [up_eq]; exact hp
    · rw [up_ne hz13]; exact hfit z

/-- The loop frame agrees with the caller's frame off the two cells the loop owns —
which is why the digits, at addresses `≠ 13`, `≠ 15`, are read identically. -/
theorem cmpLoopFrame_digit {h : Nat → Nat} {p acc z : Nat} (hz13 : z ≠ 13) (hz15 : z ≠ 15) :
    CmpLoopFrame h p acc z = h z := by
  unfold CmpLoopFrame
  rw [up_ne hz15, up_ne hz13]

/-- **The nest collapses.**  An iteration's writes — the accumulator, then the counter,
then the accumulator again with the accumulated value, then the counter again with the
advanced value — are the same function as re-parametrizing the frame at the new
`(p, acc)`.  This is what makes the loop induction one rewrite per iteration. -/
theorem up_up_absorb (h : Nat → Nat) (P0 A X D : Nat) :
    up (up (up (up h 13 P0) 15 A) 15 X) 13 D = CmpLoopFrame h D X := by
  funext z
  unfold CmpLoopFrame
  by_cases h13 : z = 13 <;> by_cases h15 : z = 15 <;> simp [up, h13, h15]

/-! #### The digit readings survive the frame's re-parametrization

`digHalf` reads only the digit cells, so re-parametrizing the frame at `(p, acc)` —
which touches cells `13` and `15` only — cannot change the verdict.  Stated as the
congruence it is, so the loop uses the *caller's* `digHalf` and not the frame's. -/

theorem cmpDigitsFrom_congr {f g f' g' : Nat → Nat} {addrV addrA : Nat}
    (hf : ∀ i, f (addrV + i) = f' (addrV + i))
    (hg : ∀ i, g (addrA + i) = g' (addrA + i)) :
    ∀ n, cmpDigitsFrom f g addrV addrA n = cmpDigitsFrom f' g' addrV addrA n
  | 0 => rfl
  | n + 1 => by
    have ih := cmpDigitsFrom_congr hf hg n
    simp only [cmpDigitsFrom, hf n, hg n, ih]

/-- **The verdict is invariant under the frame's re-parametrization.**  Both frames
agree at *every* digit address, and `digHalf` reads nothing else. -/
theorem digHalf_congr {f g f' g' : Nat → Nat} {addrV addrA p r : Nat}
    (hf : ∀ i, f (addrV + i) = f' (addrV + i))
    (hg : ∀ i, g (addrA + i) = g' (addrA + i)) :
    digHalf f g addrV addrA p r = digHalf f' g' addrV addrA p r := by
  have d1 : f (addrV + p) = f' (addrV + p) := hf p
  have d2 : g (addrA + p) = g' (addrA + p) := hg p
  simp only [digHalf, d1, d2]
  by_cases b1 : g' (addrA + p) + 2 ^ r < f' (addrV + p)
  · simp only [b1, if_true]
  · simp only [b1, if_false]
    by_cases b2 : f' (addrV + p) + 2 ^ r < g' (addrA + p)
    · simp only [b2, if_true]
    · simp only [b2, if_false]
      by_cases b3 : f' (addrV + p) = g' (addrA + p) + 2 ^ r
      · simp only [b3, if_true]
        exact cmpDigitsFrom_congr hf hg p
      · simp only [b3, if_false]
        by_cases b4 : g' (addrA + p) = f' (addrV + p) + 2 ^ r
        · simp only [b4, if_true]
          exact cmpDigitsFrom_congr hg hf p
        · simp only [b4, if_false]

/-! #### The counting loop's cost as a function of the run

Both are structural recursions on the number of comparisons remaining, so the induction
never has to resolve an existential — the discipline §C3 applies to the segment. -/

/-- The accumulated verdict count over `m` comparisons from `p` — `scan_loop`'s
`hitCount`, at the loop's own granularity. -/
def cmpLoopHits (h : Nat → Nat) (addrV addrA p m r : Nat) : Nat :=
  match m with
  | 0 => 0
  | m + 1 => (if digHalf h h addrV addrA p r then 1 else 0)
      + cmpLoopHits h addrV addrA (p + 1) m r

/-- The same run's step count: `cmpSegCost + 6` per comparison. -/
def cmpLoopFuel (h : Nat → Nat) (addrV addrA p m r : Nat) : Nat :=
  match m with
  | 0 => 0
  | m + 1 => cmpSegCost h addrV addrA p r + 6 + cmpLoopFuel h addrV addrA (p + 1) m r

/-- **THE PER-COMPARISON CHARGE OF A COUNTING LOOP**, bounded.  `20 + 9p`, one more
than `cmpSeg_loopCharge_le`'s `19 + 9p` — the accumulate is an instruction, and the
difference is the measurement, not the arithmetic. -/
theorem cmpSeg_hitCharge_le (h : Nat → Nat) (addrV addrA p r : Nat) :
    cmpSegCost h addrV addrA p r + 6 ≤ 20 + 9 * p := by
  have := cmpSegCost_le h addrV addrA p r
  unfold cmpSegFuel at this
  omega

/-! #### The price is a function of the digits, not of the frame

`cmpSegCost` and `walkCost` read the digit cells only, so re-parametrizing the frame at
`(p, acc)` cannot change what a comparison costs.  Without this, the segment's chain —
which is run against the *loop's* frame `g` — would be priced in `g` while the loop's
fuel is priced in the caller's `h`, and the induction could not chain its arithmetic. -/

theorem walkCost_congr {f f' : Nat → Nat} {addrV addrA : Nat}
    (hf : ∀ i, f (addrV + i) = f' (addrV + i))
    (hg : ∀ i, f (addrA + i) = f' (addrA + i)) :
    ∀ n, walkCost f addrV addrA n = walkCost f' addrV addrA n
  | 0 => rfl
  | n + 1 => by
    have e1 : f (addrV + n) = f' (addrV + n) := hf n
    have e2 : f (addrA + n) = f' (addrA + n) := hg n
    by_cases hc : f' (addrV + n) = f' (addrA + n)
    · have hc' : f (addrV + n) = f (addrA + n) := by rw [e1, e2]; exact hc
      rw [walkCost_succ, walkCost_succ, if_pos hc', if_pos hc]
      by_cases hn : n = 0
      · rw [if_pos hn, if_pos hn]
      · rw [if_neg hn, if_neg hn, walkCost_congr hf hg n]
    · have hc' : ¬ f (addrV + n) = f (addrA + n) := by rw [e1, e2]; exact hc
      rw [walkCost_succ, walkCost_succ, if_neg hc', if_neg hc]
      by_cases hlt : f' (addrV + n) < f' (addrA + n)
      · have hlt' : f (addrV + n) < f (addrA + n) := by rw [e1, e2]; exact hlt
        rw [if_pos hlt', if_pos hlt]
      · have hlt' : ¬ f (addrV + n) < f (addrA + n) := by rw [e1, e2]; exact hlt
        rw [if_neg hlt', if_neg hlt]

/-- **The comparison's price is invariant under the frame's re-parametrization.** -/
theorem cmpSegCost_congr {f f' : Nat → Nat} {addrV addrA p r : Nat}
    (hf : ∀ i, f (addrV + i) = f' (addrV + i))
    (hg : ∀ i, f (addrA + i) = f' (addrA + i)) :
    cmpSegCost f addrV addrA p r = cmpSegCost f' addrV addrA p r := by
  have e1 : f (addrV + p) = f' (addrV + p) := hf p
  have e2 : f (addrA + p) = f' (addrA + p) := hg p
  unfold cmpSegCost
  by_cases b1 : f' (addrV + p) < f' (addrA + p) + 2 ^ r
  · have b1' : f (addrV + p) < f (addrA + p) + 2 ^ r := by rw [e1, e2]; exact b1
    rw [if_pos b1', if_pos b1]
    by_cases b2 : f' (addrA + p) < f' (addrV + p) + 2 ^ r
    · have b2' : f (addrA + p) < f (addrV + p) + 2 ^ r := by rw [e1, e2]; exact b2
      rw [if_pos b2', if_pos b2]
    · have b2' : ¬ f (addrA + p) < f (addrV + p) + 2 ^ r := by rw [e1, e2]; exact b2
      rw [if_neg b2', if_neg b2]
      by_cases b3 : f' (addrV + p) + 2 ^ r < f' (addrA + p)
      · have b3' : f (addrV + p) + 2 ^ r < f (addrA + p) := by rw [e1, e2]; exact b3
        rw [if_pos b3', if_pos b3]
      · have b3' : ¬ f (addrV + p) + 2 ^ r < f (addrA + p) := by rw [e1, e2]; exact b3
        rw [if_neg b3', if_neg b3]
        by_cases hp0 : p = 0
        · rw [if_pos hp0, if_pos hp0]
        · rw [if_neg hp0, if_neg hp0, walkCost_congr hg hf p]
  · have b1' : ¬ f (addrV + p) < f (addrA + p) + 2 ^ r := by rw [e1, e2]; exact b1
    rw [if_neg b1', if_neg b1]
    by_cases b4 : f' (addrA + p) + 2 ^ r < f' (addrV + p)
    · have b4' : f (addrA + p) + 2 ^ r < f (addrV + p) := by rw [e1, e2]; exact b4
      rw [if_pos b4', if_pos b4]
    · have b4' : ¬ f (addrA + p) + 2 ^ r < f (addrV + p) := by rw [e1, e2]; exact b4
      rw [if_neg b4', if_neg b4]
      by_cases hp0 : p = 0
      · rw [if_pos hp0, if_pos hp0]
      · rw [if_neg hp0, if_neg hp0, walkCost_congr hf hg p]

/-- **The bounded charge of the whole run.**  `m` comparisons cost at most
`m * (20 + 9 * (p + m))` — the per-comparison bound summed, with the counter drifting
to `p + m`.  This is the number residual (iv)'s horizon reads. -/
theorem cmpLoopFuel_le {h : Nat → Nat} {addrV addrA p m r : Nat} :
    cmpLoopFuel h addrV addrA p m r ≤ m * (20 + 9 * (p + m)) := by
  induction m generalizing p with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hmono : cmpSegCost h addrV addrA p r + 6 ≤ 20 + 9 * (p + m + 1) := by
      have := cmpSeg_hitCharge_le h addrV addrA p r
      omega
    have ih2 := ih (p := p + 1)
    rw [show p + 1 + m = p + m + 1 from by omega] at ih2
    rw [show cmpLoopFuel h addrV addrA p (m + 1) r
          = cmpSegCost h addrV addrA p r + 6
            + cmpLoopFuel h addrV addrA (p + 1) m r from rfl]
    rw [show (m + 1) * (20 + 9 * (p + (m + 1)))
          = (m + 1) * (20 + 9 * (p + m + 1)) from by
        rw [show p + (m + 1) = p + m + 1 from by omega]]
    rw [Nat.succ_mul]
    omega

/-! #### The tail in two pieces: the body, then the guard

The guard is the only instruction whose successor depends on the data, so it is proved
once per case at one instruction each, and the body above it is proved once. -/

/-- **THE COUNTING TAIL'S BODY** (`pc 29 → pc 34`, 5 steps): the accumulate, the
advance, the reload.  Cell `6`, the verdict, is preserved, and the frame lands on
`up (up h 15 (h 15 + h 6)) 13 (p + 1)` — the `(p, acc)` re-parametrization §C11 makes
the loop's invariant. -/
theorem cmpSeg_hitBody {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p limit : Nat} {st : Nat → Nat}
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h11 : h 11 = addrV) (h12 : h 12 = addrA)
    (h14 : h 14 = limit)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w)
    (h13 : st 13 = p) (h6le : st 6 ≤ 1) (hacc1 : st 15 + 1 < 2 ^ w)
    (hdV : addrV + (p + 1) < 2 ^ w) (hdA : addrA + (p + 1) < 2 ^ w)
    (hpw : p + 1 < 2 ^ w) (S : Nat) :
    ∃ st', (st' 0 = addrV + (p + 1)) ∧ (st' 1 = addrA + (p + 1)) ∧ (st' 2 = p + 1) ∧
        (st' 13 = p + 1) ∧ (st' 6 = st 6) ∧
        (∀ z, ¬ CmpCell z → st' z = up (up h 15 (h 15 + st 6)) 13 (p + 1) z) ∧
        (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSegmentProgram cmpHitTail) ρ (S + 5) 29 0 (memOf w st)
        = exec (cmpSegmentProgram cmpHitTail) ρ S 34 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have s11 : st 11 = addrV := by rw [hag 11 (not_cmpCell_high (by omega))]; exact h11
  have s12 : st 12 = addrA := by rw [hag 12 (not_cmpCell_high (by omega))]; exact h12
  have s14 : st 14 = limit := by rw [hag 14 (not_cmpCell_high (by omega))]; exact h14
  have s15 : st 15 = h 15 := hag 15 (not_cmpCell_high (by omega))
  -- 29: the accumulate
  have d29 : (cmpSegmentProgram cmpHitTail).getD 29 Instr.reject = Instr.add 15 15 6 := by
    rw [show (29 : Nat) = 29 + 0 from rfl, cmpSegment_getD_tail]
    rfl
  rw [exec_add_step (S := S + 5) (hS := by omega) d29]
  rw [show S + 5 - 1 = S + 4 from rfl]
  set a0 : Nat → Nat := up st 15 (st 15 + st 6) with ha0
  have hfa0 : ∀ z, a0 z < 2 ^ w := upFit hfit (by omega)
  have hha0 : ∀ z, ¬ CmpCell z → a0 z = up h 15 (h 15 + st 6) z := by
    intro z hz
    rw [ha0]
    by_cases hz15 : z = 15
    · subst hz15; rw [up_eq, up_eq, s15]
    · rw [up_ne hz15, hag z hz, up_ne hz15]
  have e13 : a0 13 = p := by rw [ha0, up_ne (by decide : (13 : Nat) ≠ 15)]; exact h13
  have e7 : a0 7 = 0 := by rw [ha0, up_ne (by decide : (7 : Nat) ≠ 15)]; exact s7
  have e8 : a0 8 = 1 := by rw [ha0, up_ne (by decide : (8 : Nat) ≠ 15)]; exact s8
  have e6 : a0 6 = st 6 := by rw [ha0, up_ne (by decide : (6 : Nat) ≠ 15)]
  have e11 : a0 11 = addrV := by rw [ha0, up_ne (by decide : (11 : Nat) ≠ 15)]; exact s11
  have e12 : a0 12 = addrA := by rw [ha0, up_ne (by decide : (12 : Nat) ≠ 15)]; exact s12
  -- 30: the advance
  have d30 : (cmpSegmentProgram cmpHitTail).getD 30 Instr.reject = Instr.add 13 13 8 := by
    rw [show (30 : Nat) = 29 + 1 from rfl, cmpSegment_getD_tail]
    rfl
  rw [exec_add_step (S := S + 4) (hS := by omega) d30]
  rw [show S + 4 - 1 = S + 3 from rfl]
  rw [show a0 13 + a0 8 = p + 1 from by rw [e13, e8]]
  set s1 : Nat → Nat := up a0 13 (p + 1) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfa0 hpw
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = up (up h 15 (h 15 + st 6)) 13 (p + 1) z := by
    intro z hz
    rw [hs1]
    by_cases hz13 : z = 13
    · subst hz13; rw [up_eq, up_eq]
    · rw [up_ne hz13, hha0 z hz, up_ne hz13]
  have e13' : s1 13 = p + 1 := up_eq a0 13 _
  have e11' : s1 11 = addrV := by rw [hs1, up_ne (by decide : (11 : Nat) ≠ 13)]; exact e11
  have e7' : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 13)]; exact e7
  -- 31: reload cell 0
  have d31 : (cmpSegmentProgram cmpHitTail).getD 31 Instr.reject = Instr.add 0 11 13 := by
    rw [show (31 : Nat) = 29 + 2 from rfl, cmpSegment_getD_tail]
    rfl
  rw [exec_add_step (S := S + 3) (hS := by omega) d31]
  rw [show S + 3 - 1 = S + 2 from rfl]
  rw [show s1 11 + s1 13 = addrV + (p + 1) from by rw [e11', e13']]
  set s2 : Nat → Nat := up s1 0 (addrV + (p + 1)) with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 hdV
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = up (up h 15 (h 15 + st 6)) 13 (p + 1) z :=
    cmpAgree_up cmpCell_zero ha1
  have e13'' : s2 13 = p + 1 := by rw [hs2, up_ne (by decide : (13 : Nat) ≠ 0)]; exact e13'
  have e12' : s2 12 = addrA := by
    rw [hs2, up_ne (by decide : (12 : Nat) ≠ 0), hs1, up_ne (by decide : (12 : Nat) ≠ 13)]
    exact e12
  -- 32: reload cell 1
  have d32 : (cmpSegmentProgram cmpHitTail).getD 32 Instr.reject = Instr.add 1 12 13 := by
    rw [show (32 : Nat) = 29 + 3 from rfl, cmpSegment_getD_tail]
    rfl
  rw [exec_add_step (S := S + 2) (hS := by omega) d32]
  rw [show S + 2 - 1 = S + 1 from rfl]
  rw [show s2 12 + s2 13 = addrA + (p + 1) from by rw [e12', e13'']]
  set s3 : Nat → Nat := up s2 1 (addrA + (p + 1)) with hs3
  have hf3 : ∀ z, s3 z < 2 ^ w := upFit hf2 hdA
  have ha3 : ∀ z, ¬ CmpCell z → s3 z = up (up h 15 (h 15 + st 6)) 13 (p + 1) z :=
    cmpAgree_up cmpCell_one ha2
  have e13''' : s3 13 = p + 1 := by rw [hs3, up_ne (by decide : (13 : Nat) ≠ 1)]; exact e13''
  have e7'' : s3 7 = 0 := by
    rw [hs3, up_ne (by decide : (7 : Nat) ≠ 1), hs2, up_ne (by decide : (7 : Nat) ≠ 0)]
    exact e7'
  -- 33: reload cell 2
  have d33 : (cmpSegmentProgram cmpHitTail).getD 33 Instr.reject = Instr.add 2 13 7 := by
    rw [show (33 : Nat) = 29 + 4 from rfl, cmpSegment_getD_tail]
    rfl
  rw [exec_add_step (S := S + 1) (hS := by omega) d33]
  rw [show S + 1 - 1 = S + 0 from rfl]
  rw [show s3 13 + s3 7 = p + 1 from by rw [e13''', e7'', Nat.add_zero]]
  refine ⟨up s3 2 (p + 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [up_ne (by decide : (0 : Nat) ≠ 2), hs3, up_ne (by decide : (0 : Nat) ≠ 1), hs2]
    exact up_eq s1 0 _
  · rw [up_ne (by decide : (1 : Nat) ≠ 2), hs3]
    exact up_eq s2 1 _
  · exact up_eq s3 2 _
  · rw [up_ne (by decide : (13 : Nat) ≠ 2), hs3, up_ne (by decide : (13 : Nat) ≠ 1),
      hs2, up_ne (by decide : (13 : Nat) ≠ 0)]
    exact e13'''
  · rw [up_ne (by decide : (6 : Nat) ≠ 2), hs3, up_ne (by decide : (6 : Nat) ≠ 1),
      hs2, up_ne (by decide : (6 : Nat) ≠ 0), hs1, up_ne (by decide : (6 : Nat) ≠ 13)]
    exact e6
  · exact cmpAgree_up cmpCell_two ha3
  · exact upFit hf3 hpw
  · simp

/-- **The guard taken** — `p < limit` sends the loop back to `0`. -/
theorem cmpSeg_guard_taken {ρ : Nat → BitVec w} {p limit : Nat} {st : Nat → Nat}
    (h13 : st 13 = p) (h14 : st 14 = limit) (hl : p < limit)
    (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    exec (cmpSegmentProgram cmpHitTail) ρ (S + 1) 34 0 (memOf w st)
      = exec (cmpSegmentProgram cmpHitTail) ρ S 0 0 (memOf w st) := by
  have d34 : (cmpSegmentProgram cmpHitTail).getD 34 Instr.reject = Instr.blt 13 14 0 := by
    rw [show (34 : Nat) = 29 + 5 from rfl, cmpSegment_getD_tail]
    rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d34 hfit (by rw [h13, h14]; exact hl)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  rfl

/-- **The guard not taken** — the loop's exit at `35`, past the tail. -/
theorem cmpSeg_guard_exit {ρ : Nat → BitVec w} {p limit : Nat} {st : Nat → Nat}
    (h13 : st 13 = p) (h14 : st 14 = limit) (hl : ¬ p < limit)
    (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    exec (cmpSegmentProgram cmpHitTail) ρ (S + 1) 34 0 (memOf w st)
      = exec (cmpSegmentProgram cmpHitTail) ρ S 35 0 (memOf w st) := by
  have d34 : (cmpSegmentProgram cmpHitTail).getD 34 Instr.reject = Instr.blt 13 14 0 := by
    rw [show (34 : Nat) = 29 + 5 from rfl, cmpSegment_getD_tail]
    rfl
  rw [exec_blt_ge_step (S := S + 1) (hS := by omega) d34 hfit (by rw [h13, h14]; exact hl)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  rfl

/-! #### One iteration, end to end: the segment, the body, the guard -/

/-- **ONE COUNTING ITERATION.**  From the segment's register precondition at `p`, the
loop frame `g = CmpLoopFrame h p acc`, and the counter, the program runs
`cmpSegCost + 6` steps and returns to `0` with the counter advanced, the accumulator
incremented by the verdict, the precondition re-established, and the frame
re-parametrized at `(p + 1, acc + verdict)`.  This is the transfer (§C10) and the
re-entry (§C9) composed into the one step the induction consumes. -/
theorem cmpSeg_hitIter {ρ : Nat → BitVec w} {h g : Nat → Nat}
    {addrV addrA p acc r limit : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 16 ≤ addrV) (hA : 16 ≤ addrA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h9 : h 9 = 2 ^ r)
    (h11 : h 11 = addrV) (h12 : h 12 = addrA) (h14 : h 14 = limit)
    (k0 : st 0 = addrV + p) (k1 : st 1 = addrA + p) (k2 : st 2 = p) (k13 : st 13 = p)
    (hadA : h (addrA + p) + 2 ^ r < 2 ^ w) (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (hag : ∀ z, ¬ CmpCell z → st z = g z)
    (hgf : ∀ z, g z = CmpLoopFrame h p acc z) (hfit : ∀ z, st z < 2 ^ w)
    (hacc : acc + 1 < 2 ^ w) (hl : p + 1 < limit)
    (hdV : addrV + (p + 1) < 2 ^ w) (hdA : addrA + (p + 1) < 2 ^ w)
    (hpw : p + 1 < 2 ^ w) (S : Nat) :
    ∃ st', (st' 0 = addrV + (p + 1)) ∧ (st' 1 = addrA + (p + 1)) ∧ (st' 2 = p + 1) ∧
        (st' 13 = p + 1) ∧
        (∀ z, ¬ CmpCell z →
          st' z = CmpLoopFrame h (p + 1)
            (acc + (if digHalf h h addrV addrA p r then 1 else 0)) z) ∧
        (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSegmentProgram cmpHitTail) ρ (S + (cmpSegCost h addrV addrA p r + 6)) 0 0 (memOf w st)
        = exec (cmpSegmentProgram cmpHitTail) ρ S 0 0 (memOf w st') := by
  have g13 : g 13 = p := by rw [hgf 13]; exact cmpLoopFrame_13 h p acc
  have g7 : g 7 = 0 := by rw [hgf 7, cmpLoopFrame_7]; exact h7
  have g8 : g 8 = 1 := by rw [hgf 8, cmpLoopFrame_8]; exact h8
  have g9 : g 9 = 2 ^ r := by rw [hgf 9, cmpLoopFrame_9]; exact h9
  have g11 : g 11 = addrV := by rw [hgf 11, cmpLoopFrame_11]; exact h11
  have g12 : g 12 = addrA := by rw [hgf 12, cmpLoopFrame_12]; exact h12
  have g14 : g 14 = limit := by rw [hgf 14, cmpLoopFrame_14]; exact h14
  have gfit : ∀ z, g z < 2 ^ w := by
    intro z; rw [hgf z]
    exact cmpLoopFrame_fit (h := h) (p := p) (acc := acc) hfitH (by omega) (by omega) z
  have gdigV : ∀ i, g (addrV + i) = h (addrV + i) := by
    intro i
    rw [hgf, cmpLoopFrame_digit (by omega) (by omega)]
  have gdigA : ∀ i, g (addrA + i) = h (addrA + i) := by
    intro i
    rw [hgf, cmpLoopFrame_digit (by omega) (by omega)]
  have hadAg : g (addrA + p) + 2 ^ r < 2 ^ w := by rw [gdigA p]; exact hadA
  have hadVg : g (addrV + p) + 2 ^ r < 2 ^ w := by rw [gdigV p]; exact hadV
  have hcost : cmpSegCost g addrV addrA p r = cmpSegCost h addrV addrA p r :=
    cmpSegCost_congr gdigV gdigA
  obtain ⟨s1, h6, hags, hfits, hstep1⟩ :=
    cmpSeg_reaches_program cmpHitTail (ρ := ρ) (h := g) (addrV := addrV)
      (addrA := addrA) (p := p) (r := r) (st := st) (S := S + 6)
      gfit (by omega) (by omega) g7 g8 g9 k0 k1 k2 hadAg hadVg hag hfit
  rw [hcost] at hstep1
  have s13 : s1 13 = p := by rw [hags 13 (not_cmpCell_high (by omega)), g13]
  have s11 : s1 11 = addrV := (hags 11 (not_cmpCell_high (by omega))).trans g11
  have s12 : s1 12 = addrA := (hags 12 (not_cmpCell_high (by omega))).trans g12
  have s14 : s1 14 = limit := (hags 14 (not_cmpCell_high (by omega))).trans g14
  have s7 : s1 7 = 0 := (hags 7 not_cmpCell_seven).trans g7
  have s8 : s1 8 = 1 := (hags 8 not_cmpCell_eight).trans g8
  have s15 : s1 15 = acc := (hags 15 (not_cmpCell_high (by omega))).trans (by rw [hgf 15]; exact cmpLoopFrame_15 h p acc)
  obtain ⟨s2, m0, m1, m2, m13, m6, mframe, mfit, hstep2⟩ :=
    cmpSeg_hitBody (ρ := ρ) (h := g) (addrV := addrV) (addrA := addrA) (p := p)
      (limit := limit) (st := s1) (S := S + 1)
      (h7 := g7) (h8 := g8) (h11 := g11) (h12 := g12) (h14 := g14)
      (hag := hags) (hfit := hfits) (h13 := s13)
      (h6le := by rw [h6]; split <;> omega) (hacc1 := by rw [s15]; exact hacc)
      (hdV := hdV) (hdA := hdA) (hpw := hpw)
  have m14 : s2 14 = limit := by
    rw [mframe 14 (not_cmpCell_high (by omega)), up_ne (by decide : (14 : Nat) ≠ 13),
      up_ne (by decide : (14 : Nat) ≠ 15)]
    exact g14
  have hstep3 : exec (cmpSegmentProgram cmpHitTail) ρ (S + 1) 34 0 (memOf w s2)
      = exec (cmpSegmentProgram cmpHitTail) ρ S 0 0 (memOf w s2) :=
    cmpSeg_guard_taken (ρ := ρ) (p := p + 1) (limit := limit) (st := s2)
      m13 m14 hl mfit (S := S)
  refine ⟨s2, m0, m1, m2, m13, ?_, mfit, ?_⟩
  · -- the frame is the `(p + 1, acc + verdict)` re-parametrization
    have key : ∀ z, ¬ CmpCell z →
        up (up g 15 (g 15 + (if digHalf g g addrV addrA p r then 1 else 0))) 13 (p + 1) z
          = CmpLoopFrame h (p + 1)
              (acc + (if digHalf h h addrV addrA p r then 1 else 0)) z := by
      intro z _
      have hg15 : g 15 = acc := by rw [hgf 15]; exact cmpLoopFrame_15 h p acc
      have dh : (if digHalf g g addrV addrA p r then 1 else 0)
          = (if digHalf h h addrV addrA p r then 1 else 0) := by
        rw [digHalf_congr (f := g) (g := g) (f' := h) (g' := h) (addrV := addrV)
          (addrA := addrA) (p := p) (r := r) gdigV gdigA]
      have gg : g = CmpLoopFrame h p acc := funext hgf
      rw [dh, hg15, gg]
      rw [show CmpLoopFrame h p acc = up (up h 13 p) 15 acc from rfl]
      exact congrFun (up_up_absorb h p acc
        (acc + (if digHalf h h addrV addrA p r then 1 else 0)) (p + 1)) z
    intro z hz
    rw [mframe z hz, h6]
    exact key z hz
  · -- the three pieces are one run
    have eA : exec (cmpSegmentProgram cmpHitTail) ρ (S + (cmpSegCost h addrV addrA p r + 6)) 0 0 (memOf w st)
        = exec (cmpSegmentProgram cmpHitTail) ρ (S + 6) 29 0 (memOf w s1) := by
      rw [show S + (cmpSegCost h addrV addrA p r + 6)
          = S + 6 + cmpSegCost h addrV addrA p r from by omega]
      exact hstep1
    have eB : exec (cmpSegmentProgram cmpHitTail) ρ (S + 6) 29 0 (memOf w s1)
        = exec (cmpSegmentProgram cmpHitTail) ρ (S + 1) 34 0 (memOf w s2) := by
      rw [show S + 6 = S + 1 + 5 from by omega]
      exact hstep2
    exact eA.trans (eB.trans hstep3)

/-! #### The induction on the number of comparisons -/

/-- **THE LOOP.**  `m` comparisons starting at `p0`, all of whose guards are taken
(`p0 + m < limit`), cost exactly `cmpLoopFuel` and accumulate exactly `cmpLoopHits`
verdicts, returning to `0` with the frame re-parametrized at
`(p0 + m, acc + cmpLoopHits …)`.  The shape is `scan_loop`'s — an accumulator threaded
through an induction on the count — with the segment's per-comparison price inside it.

**The charge.**  `cmpLoopFuel` is exact per comparison; the bounded form is
`m * (20 + 9 * (p0 + m))`, which is what residual (iv)'s horizon reads. -/

theorem cmpSeg_loop {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA r limit : Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 16 ≤ addrV) (hA : 16 ≤ addrA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (h9 : h 9 = 2 ^ r)
    (h11 : h 11 = addrV) (h12 : h 12 = addrA) (h14 : h 14 = limit) :
    ∀ (m p0 acc : Nat) (st : Nat → Nat),
      st 0 = addrV + p0 → st 1 = addrA + p0 → st 2 = p0 → st 13 = p0 →
      (∀ z, ¬ CmpCell z → st z = CmpLoopFrame h p0 acc z) →
      (∀ z, st z < 2 ^ w) → acc + m < 2 ^ w →
      p0 + m < limit →
      (∀ i, i ≤ m → h (addrA + p0 + i) + 2 ^ r < 2 ^ w) →
      (∀ i, i ≤ m → h (addrV + p0 + i) + 2 ^ r < 2 ^ w) →
      p0 + m < 2 ^ w → addrV + (p0 + m) < 2 ^ w → addrA + (p0 + m) < 2 ^ w →
      ∀ (S : Nat),
      ∃ st', (st' 0 = addrV + (p0 + m)) ∧ (st' 1 = addrA + (p0 + m)) ∧
          (st' 2 = p0 + m) ∧ (st' 13 = p0 + m) ∧
          (∀ z, ¬ CmpCell z →
            st' z = CmpLoopFrame h (p0 + m) (acc + cmpLoopHits h addrV addrA p0 m r) z) ∧
          (∀ z, st' z < 2 ^ w) ∧
        exec (cmpSegmentProgram cmpHitTail) ρ (S + cmpLoopFuel h addrV addrA p0 m r) 0 0
            (memOf w st)
          = exec (cmpSegmentProgram cmpHitTail) ρ S 0 0 (memOf w st') := by
  intro m
  induction m with
  | zero =>
    intro p0 acc st k0 k1 k2 k13 hag hfit hacc hlim hfitA hfitV hpw hdV hdA S
    exact ⟨st, k0, k1, k2, k13, fun z hz => hag z hz, hfit, rfl⟩
  | succ m ih =>
    intro p0 acc st k0 k1 k2 k13 hag hfit hacc hlim hfitA hfitV hpw hdV hdA S
    have hl : p0 + 1 < limit := by omega
    have hpw1 : p0 + 1 < 2 ^ w := by omega
    have hdV1 : addrV + (p0 + 1) < 2 ^ w := by omega
    have hdA1 : addrA + (p0 + 1) < 2 ^ w := by omega
    obtain ⟨s1, n0, n1, n2, n13, nframe, nfit, hstep⟩ :=
      cmpSeg_hitIter (ρ := ρ) (h := h) (g := CmpLoopFrame h p0 acc) (addrV := addrV)
        (addrA := addrA) (p := p0) (acc := acc) (r := r) (limit := limit) (st := st)
        (S := S + cmpLoopFuel h addrV addrA (p0 + 1) m r)
        hfitH hV hA h7 h8 h9 h11 h12 h14 k0 k1 k2 k13
        (hfitA 0 (by omega)) (hfitV 0 (by omega)) hag (fun _ => rfl) hfit
        (by omega) hl hdV1 hdA1 hpw1
    obtain ⟨s2, q0, q1, q2, q13, qframe, qfit, hstep2⟩ :=
      ih (p0 + 1) (acc + (if digHalf h h addrV addrA p0 r then 1 else 0)) s1
        n0 n1 n2 n13 nframe nfit
        (by have hv : (if digHalf h h addrV addrA p0 r then 1 else 0) ≤ 1 := by
              split <;> omega
            omega)
        (by omega)
        (fun i hi => by
          have hh := hfitA (i + 1) (by omega)
          rwa [show addrA + p0 + (i + 1) = addrA + (p0 + 1) + i from by omega] at hh)
        (fun i hi => by
          have hh := hfitV (i + 1) (by omega)
          rwa [show addrV + p0 + (i + 1) = addrV + (p0 + 1) + i from by omega] at hh)
        (by omega) (by omega) (by omega) S
    refine ⟨s2, by omega, by omega, by omega, by omega, ?_, qfit, ?_⟩
    · intro z hz
      rw [qframe z hz]
      rw [show cmpLoopHits h addrV addrA p0 (m + 1) r
            = (if digHalf h h addrV addrA p0 r then 1 else 0)
              + cmpLoopHits h addrV addrA (p0 + 1) m r from rfl]
      rw [show p0 + (m + 1) = (p0 + 1) + m from by omega]
      rw [show acc + ((if digHalf h h addrV addrA p0 r then 1 else 0)
                + cmpLoopHits h addrV addrA (p0 + 1) m r)
              = (acc + (if digHalf h h addrV addrA p0 r then 1 else 0))
                + cmpLoopHits h addrV addrA (p0 + 1) m r from by omega]
    · rw [show cmpLoopFuel h addrV addrA p0 (m + 1) r
          = cmpSegCost h addrV addrA p0 r + 6
            + cmpLoopFuel h addrV addrA (p0 + 1) m r from rfl]
      rw [show S + (cmpSegCost h addrV addrA p0 r + 6
              + cmpLoopFuel h addrV addrA (p0 + 1) m r)
            = S + cmpLoopFuel h addrV addrA (p0 + 1) m r
              + (cmpSegCost h addrV addrA p0 r + 6) from by omega]
      exact hstep.trans hstep2

end SubsetSumL25.Row
