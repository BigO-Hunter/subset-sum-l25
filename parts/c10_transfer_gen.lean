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
