
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
