/-
`KapilaDigitwise`'s residual (i) — **`cmpSeg`'s segment proof**.

§D5 of `KapilaDigitwise` stated the shape and left the walk unproved, with the
obligation written out: from the register precondition (cells 0/1 = the two digit
addresses at `p`, cell 2 = `p`, cells 7/8/9 = `0`/`1`/`2^r`), the run of `cmpSeg
cont` reaches `cont` within `cmpSegFuel p` steps with cell 6 = `digHalf`'s verdict.
This module discharges it, and it is the last arithmetic-shaped obligation the row
carried: `hitWord_binSumTest` already showed that verdict *is* the bin-sum test, so
nothing in §6/§7 is re-argued here.

## §C1 — the calculus gets a third peeler, `rem`

The exits write the zero verdict with `.rem 6 7 7` (`[6] := [7] % [7]`, and `[7]`
is the constant `0`), which needs a `rem` peeler and its word lemma.  `KapilaLoop`
ported `sub` and `div`; `rem` is the third, and its word lemma holds at `b = 0` as
well (`[j] % 0 = [j]` in `Statement.lean`'s semantics is `Nat.mod_zero`), which is
exactly why the segment can write a zero without a constant `0` cell of its own.

## §C2 — the frame: what the segment is allowed to write

Cells `0…6` and `10` are the segment's own; `7`, `8`, `9` are the caller's
constants and are only ever read.  `CmpCell` names that set, so the frame is one
agreement condition — `∀ z, ¬ CmpCell z → st z = h z` — instead of a bag of
per-cell equalities, and every write preserves it (`cmpAgree_up`).  The digit reads
are therefore reads at addresses `≥ 11`, which is the one separation hypothesis the
segment needs (`hV`, `hA`) — the same separation `KapilaLoop`'s `Layout` discharges
by putting the payload at `14` and above.

## §C3 — the costs are *functions*, not existentials

`walkCost` is the walk's exact step count as a function of the digits it will read,
and `cmpSegCost` is the segment's.  That is what makes the composition work: the
segment's tail cost depends on which prologue branch fires and on where the digit
walk stops, so a `∃ k` would have to be resolved *before* the peeler chain that
produces the state — the wrong order.  As functions, each branch's cost is a closed
term, each lemma's step equation is stated at its exact cost with the ambient
horizon `S` free, and the assembly is `omega` on literals.  `walkCost_le` /
`cmpSegCost_le` recover the headline bound `cmpSegFuel`.

## §C4 — the low walk, by induction on the digit counter

`cmpDigitsFrom`'s recursion is an *equal* digit deferring to the walk below; the
segment's is the same, and the induction is on `n` with the base at `n = 1`, because
the walk is only ever entered with a digit to read (the `p = 0` tie does not
descend — `KapilaDigitwise`'s §D5 defect (1)).  The three leaves are *constant*
(`7` downward miss, `9` upward hit, `8` all-equal exit at `n = 1`); the equal branch
costs `9` per digit plus the terminal digit's extra step.

## §C5 — the composition state

The segment's internal jump targets are absolute (positions `8, 12, 14, 16, 19`,
`27`), so it can only sit at offset `0` of the program containing it — a program of
the shape `cmpSeg cont ++ tail` with `cont = 29`.  That is `cmpSeg_reaches_append`,
and it is free (only `getD` past `28` changes).  What the caller *pays*, stated
rather than hidden: the segment walks cells `0`, `1`, `2` down, so a loop invoking
it once per estimate reloads those three cells before each invocation, and reads
cell `6` afterwards as the verdict.  `cmpSeg_verdict_is_wordTest` writes that
verdict in the row's own vocabulary, so the loop's consumer is
`halfTest_iff_wordDiff` and not a new predicate.

Nothing here touches `Statement.lean` (hash unchanged), `KapilaAlgo.cost`,
`D7.agrees`'s horizon (residual (iv)) or `PayloadCarries` (named, residual (iii)).
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaDigitwise

set_option autoImplicit true
set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §C1 — the `rem` peeler -/

/-- The word of a remainder.  Holds at `b = 0` too: `[j] % 0 = [j]` on both sides
(`Nat.mod_zero` on the `ℕ` side, the same convention in `Statement.lean`). -/
theorem bv_rem {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    BitVec.ofNat w a % BitVec.ofNat w b = BitVec.ofNat w (a % b) := by
  rw [BitVec.toNat_eq, BitVec.umod_def]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

section StepLemmas

variable {w : Nat} {P : List Instr} {ρ : Nat → BitVec w} {S pc r : Nat} {f : Nat → Nat}

theorem exec_rem_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.rem i j k)
    (hfit : ∀ x, f x < 2 ^ w) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i (f j % f k))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;> simp [memOf, up, hxi, bv_rem (hfit j) (hfit k)]

end StepLemmas

/-! ### §C2 — the frame -/

/-- The cells the segment may write: `0…6` (pointers, digits, scratch, verdict) and
`10` (the swap scratch).  Cells `7`, `8`, `9` are the caller's constants and are
read-only. -/
def CmpCell (z : Nat) : Prop := z ≤ 6 ∨ z = 10

theorem not_cmpCell_high {z : Nat} (hz : 11 ≤ z) : ¬ CmpCell z := by
  unfold CmpCell; omega

theorem cmpCell_zero : CmpCell 0 := by unfold CmpCell; omega
theorem cmpCell_one : CmpCell 1 := by unfold CmpCell; omega
theorem cmpCell_two : CmpCell 2 := by unfold CmpCell; omega
theorem cmpCell_three : CmpCell 3 := by unfold CmpCell; omega
theorem cmpCell_four : CmpCell 4 := by unfold CmpCell; omega
theorem cmpCell_five : CmpCell 5 := by unfold CmpCell; omega
theorem cmpCell_six : CmpCell 6 := by unfold CmpCell; omega
theorem cmpCell_ten : CmpCell 10 := by unfold CmpCell; omega
theorem not_cmpCell_seven : ¬ CmpCell 7 := by unfold CmpCell; omega
theorem not_cmpCell_eight : ¬ CmpCell 8 := by unfold CmpCell; omega
theorem not_cmpCell_nine : ¬ CmpCell 9 := by unfold CmpCell; omega

/-- The walk on no digits answers `true` — the `p = 0` tie's verdict. -/
theorem cmpDigitsFrom_zero (f g : Nat → Nat) (addrV addrA : Nat) :
    cmpDigitsFrom f g addrV addrA 0 = true := rfl

/-- A write to a segment cell preserves the frame. -/
theorem cmpAgree_up {h g : Nat → Nat} {c v : Nat} (hc : CmpCell c)
    (hg : ∀ z, ¬ CmpCell z → g z = h z) :
    ∀ z, ¬ CmpCell z → up g c v z = h z := by
  intro z hz
  rw [up]
  by_cases h : z = c
  · exact absurd (h ▸ hc) hz
  · rw [if_neg h]
    exact hg z hz

/-- **The digit plus `2^r` fits when the digit's top bit is clear.**  At `r + 2 ≤ w`
this is free: a scale-fitting payload's digit at `p` is below `2^(r+1)`, so
`d + 2^r < 3·2^r < 2^(r+2) ≤ 2^w`.  Only `r = w − 1` (the half bit in the digit's
top position) is left as the explicit premise `hadA`/`hadV`, and there it is a real
constraint on the digit: the segment's `add 5 4 9` keeps the sum in one word. -/
theorem two_pow_add_fits {w r d : Nat} (hr : r + 2 ≤ w) (hd : d < 2 ^ (r + 1)) :
    d + 2 ^ r < 2 ^ w := by
  have hp : 0 < (2 : Nat) ^ r := Nat.two_pow_pos r
  have hd' : d + 1 ≤ 2 ^ r * 2 := by
    have h := hd
    rw [Nat.pow_succ] at h
    omega
  have h4 : (2 : Nat) ^ r * 4 ≤ 2 ^ w := by
    have h : (2 : Nat) ^ (r + 2) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hr
    calc (2 : Nat) ^ r * 4 = 2 ^ (r + 2) := by rw [Nat.pow_add]
      _ ≤ 2 ^ w := h
  omega

/-! ### §C3 — the walk's exact cost, as a function of the digits -/

/-- **The walk's step count.**  Read the digit pair at offset `n-1`: unequal costs
`7` (downward) or `9` (upward); equal costs `9` and recurses, except that the last
digit (`n = 1`) falls through the terminal test into the hit exit for `12`.  `0` is
unreachable — the walk is entered only with `1 ≤ n` — and its value is a
placeholder, which is why `walkCost_le` is stated on the walk's own domain. -/
def walkCost (h : Nat → Nat) (addrV addrA : Nat) : Nat → Nat
  | 0 => 7
  | n + 1 =>
    if h (addrV + n) = h (addrA + n) then
      (if n = 0 then 12 else 9 + walkCost h addrV addrA n)
    else if h (addrV + n) < h (addrA + n) then 7 else 9

theorem walkCost_zero (h : Nat → Nat) (addrV addrA : Nat) :
    walkCost h addrV addrA 0 = 7 := rfl

theorem walkCost_succ (h : Nat → Nat) (addrV addrA n : Nat) :
    walkCost h addrV addrA (n + 1)
      = (if h (addrV + n) = h (addrA + n) then
          (if n = 0 then 12 else 9 + walkCost h addrV addrA n)
        else if h (addrV + n) < h (addrA + n) then 7 else 9) := rfl

/-- **The walk's bound is `9n + 3` on its own domain.**  That is §D5's linear shape,
and the `+3` is the terminal digit's extra step plus the two exit instructions. -/
theorem walkCost_le (h : Nat → Nat) (addrV addrA : Nat) :
    ∀ n, 1 ≤ n → walkCost h addrV addrA n ≤ 9 * n + 3 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro _
    rw [walkCost_succ]
    by_cases hc : h (addrV + m) = h (addrA + m)
    · rw [if_pos hc]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; rw [if_pos rfl]
      · rw [if_neg (by omega : ¬ m = 0)]; have := ih (by omega); omega
    · rw [if_neg hc]
      by_cases hlt : h (addrV + m) < h (addrA + m)
      · rw [if_pos hlt]; omega
      · rw [if_neg hlt]; omega

/-- **The bound is attained.**  If every digit pair read is equal, the walk costs
exactly `9n + 3` — the all-equal path is the expensive one, so the fuel is not
slack. -/
theorem walkCost_eq_of_all_eq (h : Nat → Nat) (addrV addrA : Nat) :
    ∀ n, 1 ≤ n → (∀ i, i < n → h (addrV + i) = h (addrA + i)) →
      walkCost h addrV addrA n = 9 * n + 3 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro _ hall
    rw [walkCost_succ, if_pos (hall m (by omega))]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; rw [if_pos rfl]
    · rw [if_neg (by omega : ¬ m = 0), ih hm (fun i hi => hall i (by omega))]
      omega

/-! ### §C4 — the low walk: head, three leaves, and the induction

Every lemma is stated at one program position with an exact step count from a free
horizon `S`, so the segment's assembly is arithmetic on literals. -/

/-- The walk's four opening instructions (`pc 19 → pc 23`): both pointers stepped
down, the digit pair read into cells `3`/`4`. -/
theorem cmpSeg_walk_head {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA n : Nat} {st : Nat → Nat}
    (hV : 11 ≤ addrV) (hA : 11 ≤ addrA) (hfitH : ∀ z, h z < 2 ^ w)
    (h2 : st 2 = n) (h8 : h 8 = 1)
    (h0 : st 0 = addrV + n) (h1 : st 1 = addrA + n)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (hn : 1 ≤ n)
    (S : Nat) :
    ∃ st', (st' 0 = addrV + (n - 1) ∧ st' 1 = addrA + (n - 1) ∧ st' 2 = n ∧
        st' 3 = h (addrV + (n - 1)) ∧ st' 4 = h (addrA + (n - 1)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w)) ∧
      exec (cmpSeg cont) ρ (S + 4) 19 0 (memOf w st)
        = exec (cmpSeg cont) ρ S 23 0 (memOf w st') := by
  have hb0 : st 0 < 2 ^ w := hfit 0
  have hb1 : st 1 < 2 ^ w := hfit 1
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d19 : (cmpSeg cont).getD 19 Instr.reject = Instr.sub 0 0 8 := rfl
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
  have d20 : (cmpSeg cont).getD 20 Instr.reject = Instr.sub 1 1 8 := rfl
  rw [exec_sub_step (S := S + 3) (hS := by omega) d20 hf1 (by rw [e1, e1']; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have v20 : s1 1 - s1 8 = addrA + (n - 1) := by rw [e1, e1']; omega
  rw [v20]
  set s2 : Nat → Nat := up s1 1 (addrA + (n - 1)) with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 (by omega)
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_one ha1
  have e0' : s2 0 = addrV + (n - 1) := by
    rw [hs2, up_ne (by decide : (0 : Nat) ≠ 1)]; exact up_eq st 0 _
  have d21 : (cmpSeg cont).getD 21 Instr.reject = Instr.load 3 0 := rfl
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
  have d22 : (cmpSeg cont).getD 22 Instr.reject = Instr.load 4 1 := rfl
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

/-- **The downward miss** (`pc 23 → cont`, 3 steps): the V-side digit is smaller, so
the low block is smaller and the verdict is `0` — no subtraction, no numerator. -/
theorem cmpSeg_walk_lt {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA m : Nat} {st : Nat → Nat}
    (h3 : st 3 = h (addrV + m)) (h4 : st 4 = h (addrA + m))
    (hlt : h (addrV + m) < h (addrA + m)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    ∃ st', (st' 6 = 0) ∧ (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 3) 23 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d23 : (cmpSeg cont).getD 23 Instr.reject = Instr.blt 3 4 14 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d23 hfit (by rw [h3, h4]; exact hlt)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d14 : (cmpSeg cont).getD 14 Instr.reject = Instr.rem 6 7 7 := rfl
  rw [exec_rem_step (S := S + 2) (hS := by omega) d14 hfit]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v14 : st 7 % st 7 = 0 := by rw [s7]
  rw [v14]
  set s1 : Nat → Nat := up st 6 0 with hs1
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_six hag
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (Nat.two_pow_pos w)
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 6)]; exact s7
  have e8 : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d15 : (cmpSeg cont).getD 15 Instr.reject = Instr.blt 7 8 cont := rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d15 hf1 (by rw [e7, e8]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s1, up_eq st 6 0, ha1, hf1, ?_⟩
  simp

/-- **The upward hit** (`pc 23 → cont`, 5 steps): the difference is positive, so the
V-side block is not smaller — one `sub`, one `blt`, then the hit exit. -/
theorem cmpSeg_walk_gt {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA m : Nat} {st : Nat → Nat}
    (h3 : st 3 = h (addrV + m)) (h4 : st 4 = h (addrA + m))
    (hgt : h (addrA + m) < h (addrV + m)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    ∃ st', (st' 6 = 1) ∧ (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 5) 23 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  have hb3 : st 3 < 2 ^ w := hfit 3
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d23 : (cmpSeg cont).getD 23 Instr.reject = Instr.blt 3 4 14 := rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d23 hfit (by rw [h3, h4]; omega)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d24 : (cmpSeg cont).getD 24 Instr.reject = Instr.sub 5 3 4 := rfl
  rw [exec_sub_step (S := S + 4) (hS := by omega) d24 hfit (by rw [h3, h4]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have v24 : st 3 - st 4 = h (addrV + m) - h (addrA + m) := by rw [h3, h4]
  rw [v24]
  set s1 : Nat → Nat := up st 5 (h (addrV + m) - h (addrA + m)) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (by rw [h3] at hb3; omega)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have d25 : (cmpSeg cont).getD 25 Instr.reject = Instr.blt 7 5 12 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d25 hf1
    (by rw [e7, hs1, up_eq]; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : (cmpSeg cont).getD 12 Instr.reject = Instr.one 6 := rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s2 : Nat → Nat := up s1 6 1 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2 z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 h8w
  have e7' : s2 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7
  have e8' : s2 8 = 1 := by rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d13 : (cmpSeg cont).getD 13 Instr.reject = Instr.blt 7 8 cont := rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf2 (by rw [e7', e8']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s2, up_eq s1 6 1, ha2, hf2, ?_⟩
  simp

/-- **Equal digits with more to come** (`pc 23 → pc 19`, 5 steps): the pair matched,
the counter steps down, and the walk continues at the next digit. -/
theorem cmpSeg_walk_eq_step {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA m : Nat} {st : Nat → Nat}
    (h0 : st 0 = addrV + m) (h1 : st 1 = addrA + m) (h2 : st 2 = m + 1)
    (h3 : st 3 = h (addrV + m)) (h4 : st 4 = h (addrA + m))
    (heq : h (addrV + m) = h (addrA + m)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (hm : 1 ≤ m)
    (S : Nat) :
    ∃ st', (st' 0 = addrV + m) ∧ (st' 1 = addrA + m) ∧ (st' 2 = m) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 5) 23 0 (memOf w st)
        = exec (cmpSeg cont) ρ S 19 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d23 : (cmpSeg cont).getD 23 Instr.reject = Instr.blt 3 4 14 := rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d23 hfit (by rw [h3, h4, heq]; omega)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d24 : (cmpSeg cont).getD 24 Instr.reject = Instr.sub 5 3 4 := rfl
  rw [exec_sub_step (S := S + 4) (hS := by omega) d24 hfit (by rw [h3, h4]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have v24 : st 3 - st 4 = 0 := by rw [h3, h4, heq]; omega
  rw [v24]
  set s1 : Nat → Nat := up st 5 0 with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (Nat.two_pow_pos w)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have e5 : s1 5 = 0 := up_eq st 5 0
  have d25 : (cmpSeg cont).getD 25 Instr.reject = Instr.blt 7 5 12 := rfl
  rw [exec_blt_ge_step (S := S + 3) (hS := by omega) d25 hf1 (by rw [e7, e5]; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d26 : (cmpSeg cont).getD 26 Instr.reject = Instr.sub 2 2 8 := rfl
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
  have d27 : (cmpSeg cont).getD 27 Instr.reject = Instr.blt 7 2 19 := rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d27 hf2 (by rw [e7', e2']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s2, ?_, ?_, e2', ha2, hf2, ?_⟩
  · rw [hs2, up_ne (by decide : (0 : Nat) ≠ 2), hs1, up_ne (by decide : (0 : Nat) ≠ 5)]
    exact h0
  · rw [hs2, up_ne (by decide : (1 : Nat) ≠ 2), hs1, up_ne (by decide : (1 : Nat) ≠ 5)]
    exact h1
  · simp

/-- **Equal digits, no digit below** (`pc 23 → cont`, 8 steps): the last pair matched
and the counter reached zero, so every digit was equal and the block comparison is
`true` — the walk's all-equal exit. -/
theorem cmpSeg_walk_eq_term {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA : Nat} {st : Nat → Nat}
    (h2 : st 2 = 1) (h3 : st 3 = h (addrV + 0)) (h4 : st 4 = h (addrA + 0))
    (heq : h (addrV + 0) = h (addrA + 0)) (h7 : h 7 = 0) (h8 : h 8 = 1)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w) (S : Nat) :
    ∃ st', (st' 6 = 1) ∧ (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 8) 23 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d23 : (cmpSeg cont).getD 23 Instr.reject = Instr.blt 3 4 14 := rfl
  rw [exec_blt_ge_step (S := S + 8) (hS := by omega) d23 hfit (by rw [h3, h4, heq]; omega)]
  rw [show S + 8 - 1 = S + 7 from rfl]
  have d24 : (cmpSeg cont).getD 24 Instr.reject = Instr.sub 5 3 4 := rfl
  rw [exec_sub_step (S := S + 7) (hS := by omega) d24 hfit (by rw [h3, h4]; omega)]
  rw [show S + 7 - 1 = S + 6 from rfl]
  have v24 : st 3 - st 4 = 0 := by rw [h3, h4, heq]; omega
  rw [v24]
  set s1 : Nat → Nat := up st 5 0 with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (Nat.two_pow_pos w)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_five hag
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have e5 : s1 5 = 0 := up_eq st 5 0
  have d25 : (cmpSeg cont).getD 25 Instr.reject = Instr.blt 7 5 12 := rfl
  rw [exec_blt_ge_step (S := S + 6) (hS := by omega) d25 hf1 (by rw [e7, e5]; omega)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d26 : (cmpSeg cont).getD 26 Instr.reject = Instr.sub 2 2 8 := rfl
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
  have d27 : (cmpSeg cont).getD 27 Instr.reject = Instr.blt 7 2 19 := rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d27 hf2 (by rw [e7', e2']; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have e8' : s2 8 = 1 := by
    rw [hs2, up_ne (by decide : (8 : Nat) ≠ 2), hs1, up_ne (by decide : (8 : Nat) ≠ 5)]
    exact s8
  have d28 : (cmpSeg cont).getD 28 Instr.reject = Instr.blt 7 8 12 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d28 hf2 (by rw [e7', e8']; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : (cmpSeg cont).getD 12 Instr.reject = Instr.one 6 := rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s3 : Nat → Nat := up s2 6 1 with hs3
  have ha3 : ∀ z, ¬ CmpCell z → s3 z = h z := cmpAgree_up cmpCell_six ha2
  have hf3 : ∀ z, s3 z < 2 ^ w := upFit hf2 h8w
  have e7'' : s3 7 = 0 := by rw [hs3, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7'
  have e8'' : s3 8 = 1 := by rw [hs3, up_ne (by decide : (8 : Nat) ≠ 6)]; exact e8'
  have d13 : (cmpSeg cont).getD 13 Instr.reject = Instr.blt 7 8 cont := rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf3 (by rw [e7'', e8'']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s3, up_eq s2 6 1, ha3, hf3, ?_⟩
  simp

/-- **THE LOW WALK** (`pc 19 → cont`, exactly `walkCost` steps): from the three
pointer cells, the run reaches `cont` with cell 6 = `cmpDigitsFrom`'s answer as a
word.  The induction's base is `n = 1` — the walk is never entered with a zero
counter, which is what the `p = 0` guard in the tie prologue buys. -/
theorem cmpSeg_walk {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA : Nat}
    (hfit : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (h7 : h 7 = 0) (h8 : h 8 = 1) :
    ∀ (n : Nat) (st : Nat → Nat) (S : Nat), 1 ≤ n →
      st 0 = addrV + n → st 1 = addrA + n → st 2 = n →
      (∀ z, ¬ CmpCell z → st z = h z) → (∀ z, st z < 2 ^ w) →
      ∃ st', (st' 6 = (if cmpDigitsFrom h h addrV addrA n then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
        exec (cmpSeg cont) ρ (S + walkCost h addrV addrA n) 19 0 (memOf w st)
          = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
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
        cmpSeg_walk_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
          (n := m + 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega) (S := S + 3)
      have hv : s4 3 = h (addrV + m) := by simpa using e3
      have ha : s4 4 = h (addrA + m) := by simpa using e4
      obtain ⟨st', h6, hag', hf', hstep⟩ :=
        cmpSeg_walk_lt (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
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
          cmpSeg_walk_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
            (n := m + 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega) (S := S + 5)
        have hv : s4 3 = h (addrV + m) := by simpa using e3
        have ha : s4 4 = h (addrA + m) := by simpa using e4
        obtain ⟨st', h6, hag', hf', hstep⟩ :=
          cmpSeg_walk_gt (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
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
            cmpSeg_walk_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
              (n := 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega) (S := S + 8)
          have hv : s4 3 = h (addrV + 0) := by simpa using e3
          have ha : s4 4 = h (addrA + 0) := by simpa using e4
          have e2' : s4 2 = 1 := e2
          obtain ⟨st', h6, hag', hf', hstep⟩ :=
            cmpSeg_walk_eq_term (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
              e2' hv ha heq h7 h8 hag4 hf4 S
          refine ⟨st', ?_, hag', hf', ?_⟩
          · rw [hcd]; rw [cmpDigitsFrom]; exact h6
          · rw [show S + 12 = S + 8 + 4 from by omega, hstep4, hstep]
        · -- a digit matched and more remain: 5 steps back to the walk head
          rw [if_neg (by omega : ¬ m = 0)]
          obtain ⟨s4, ⟨e0, e1, e2, e3, e4, hag4, hf4⟩, hstep4⟩ :=
            cmpSeg_walk_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
              (n := m + 1) hV hA hfit h2 h8 h0 h1 hag hf (by omega)
              (S := S + 5 + walkCost h addrV addrA m)
          have hv : s4 3 = h (addrV + m) := by simpa using e3
          have ha : s4 4 = h (addrA + m) := by simpa using e4
          have e2' : s4 2 = m + 1 := e2
          obtain ⟨s5, f0, f1, f2, hag5, hf5, hstep5⟩ :=
            cmpSeg_walk_eq_step (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
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

/-! ### §C5 — the prologue: three reads, then five ways out

`CmpHead` bundles the state at the prologue's first branch (`pc 3`): the two digits
read at `p`, and the A-side digit's `+ 2^r`.  The five leaves are then each one
peeler chain with a literal cost. -/

/-- The state at `pc 3`. -/
def CmpHead (w : Nat) (h : Nat → Nat) (st : Nat → Nat) (addrV addrA p r : Nat) : Prop :=
  st 0 = addrV + p ∧ st 1 = addrA + p ∧ st 2 = p
    ∧ st 3 = h (addrV + p) ∧ st 4 = h (addrA + p) ∧ st 5 = h (addrA + p) + 2 ^ r
    ∧ (∀ z, ¬ CmpCell z → st z = h z) ∧ (∀ z, st z < 2 ^ w)

/-- **The prologue's three reads** (`pc 0 → pc 3`, 3 steps): the two digits at `p`
and the A-side digit plus the half bit. -/
theorem cmpSeg_head {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hV : 11 ≤ addrV) (hA : 11 ≤ addrA) (hfitH : ∀ z, h z < 2 ^ w) (h9 : h 9 = 2 ^ r)
    (h0 : st 0 = addrV + p) (h1 : st 1 = addrA + p) (h2 : st 2 = p)
    (hag : ∀ z, ¬ CmpCell z → st z = h z) (hfit : ∀ z, st z < 2 ^ w)
    (hadA : h (addrA + p) + 2 ^ r < 2 ^ w) (S : Nat) :
    ∃ st', CmpHead w h st' addrV addrA p r ∧
      exec (cmpSeg cont) ρ (S + 3) 0 0 (memOf w st)
        = exec (cmpSeg cont) ρ S 3 0 (memOf w st') := by
  have d0 : (cmpSeg cont).getD 0 Instr.reject = Instr.load 3 0 := rfl
  rw [exec_load_step (S := S + 3) (hS := by omega) d0 hfit]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have v0 : st (st 0) = h (addrV + p) := by
    rw [h0]; exact hag _ (not_cmpCell_high (by omega))
  rw [v0]
  set s1 : Nat → Nat := up st 3 (h (addrV + p)) with hs1
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (hfitH _)
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_three hag
  have e1 : s1 1 = addrA + p := by rw [hs1, up_ne (by decide : (1 : Nat) ≠ 3)]; exact h1
  have d1 : (cmpSeg cont).getD 1 Instr.reject = Instr.load 4 1 := rfl
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
  have d2 : (cmpSeg cont).getD 2 Instr.reject = Instr.add 5 4 9 := rfl
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

/-- **The decided hit, A's digit far above** (`pc 3 → cont`, 4 steps). -/
theorem cmpSeg_above {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA p r)
    (hnlt : ¬ h (addrV + p) < h (addrA + p) + 2 ^ r)
    (habove : h (addrA + p) + 2 ^ r < h (addrV + p))
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 4) 3 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : (cmpSeg cont).getD 3 Instr.reject = Instr.blt 3 5 8 := rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hnlt)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have d4 : (cmpSeg cont).getD 4 Instr.reject = Instr.blt 5 3 12 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d4 hfit (by rw [k3, k5]; exact habove)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : (cmpSeg cont).getD 12 Instr.reject = Instr.one 6 := rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s1 : Nat → Nat := up st 6 1 with hs1
  have ha1 : ∀ z, ¬ CmpCell z → s1 z = h z := cmpAgree_up cmpCell_six hag
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit h8w
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 6)]; exact s7
  have e8 : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d13 : (cmpSeg cont).getD 13 Instr.reject = Instr.blt 7 8 cont := rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf1 (by rw [e7, e8]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have hdh : digHalf h h addrV addrA p r = true := by
    rw [digHalf, if_pos habove]
  refine ⟨s1, ?_, ha1, hf1, ?_⟩
  · rw [hdh]; exact up_eq st 6 1
  · simp

/-- **The decided miss** (`pc 3 → cont`, 5 steps): neither digit is `2^r` above the
other, so the whole difference is below the threshold. -/
theorem cmpSeg_miss {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA p r) (h9 : h 9 = 2 ^ r)
    (hvlt : h (addrV + p) < h (addrA + p) + 2 ^ r)
    (halt : h (addrA + p) < h (addrV + p) + 2 ^ r)
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 5) 3 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d3 : (cmpSeg cont).getD 3 Instr.reject = Instr.blt 3 5 8 := rfl
  rw [exec_blt_lt_step (S := S + 5) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d8 : (cmpSeg cont).getD 8 Instr.reject = Instr.add 5 3 9 := rfl
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
  have d9 : (cmpSeg cont).getD 9 Instr.reject = Instr.blt 4 5 14 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact halt)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d14 : (cmpSeg cont).getD 14 Instr.reject = Instr.rem 6 7 7 := rfl
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
  have d15 : (cmpSeg cont).getD 15 Instr.reject = Instr.blt 7 8 cont := rfl
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

/-- **The decided hit, A's digit still below `v + 2^r` but above `a + 2^r`** — the
mirror of `cmpSeg_above` through the second add (`pc 3 → cont`, 6 steps). -/
theorem cmpSeg_below {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA p r) (h9 : h 9 = 2 ^ r)
    (hvlt : h (addrV + p) < h (addrA + p) + 2 ^ r)
    (hnat : ¬ h (addrA + p) < h (addrV + p) + 2 ^ r)
    (hbelow : h (addrV + p) + 2 ^ r < h (addrA + p))
    (hadV : h (addrV + p) + 2 ^ r < 2 ^ w)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA p r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 6) 3 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : (cmpSeg cont).getD 3 Instr.reject = Instr.blt 3 5 8 := rfl
  rw [exec_blt_lt_step (S := S + 6) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d8 : (cmpSeg cont).getD 8 Instr.reject = Instr.add 5 3 9 := rfl
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
  have d9 : (cmpSeg cont).getD 9 Instr.reject = Instr.blt 4 5 14 := rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact hnat)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have d10 : (cmpSeg cont).getD 10 Instr.reject = Instr.blt 5 4 12 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d10 hf1 (by rw [e4, e5]; exact hbelow)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : (cmpSeg cont).getD 12 Instr.reject = Instr.one 6 := rfl
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
  have d13 : (cmpSeg cont).getD 13 Instr.reject = Instr.blt 7 8 cont := rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d13 hf2 (by rw [e7, e8']; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have hdh : digHalf h h addrV addrA p r = true := by
    rw [digHalf, if_neg (by omega : ¬ h (addrA + p) + 2 ^ r < h (addrV + p)),
      if_pos hbelow]
  refine ⟨s2, ?_, ha2, hf2, ?_⟩
  · rw [hdh]; exact up_eq s1 6 1
  · simp

/-- **The V-side tie, with digits below** (`pc 3 → pc 19`, 4 steps): `v = a + 2^r`,
so the threshold is met exactly and the low walk decides. -/
theorem cmpSeg_tieV {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA p r : Nat} {st : Nat → Nat}
    (hfitH : ∀ z, h z < 2 ^ w) (hV : 11 ≤ addrV) (hA : 11 ≤ addrA)
    (hH : CmpHead w h st addrV addrA p r)
    (hnlt : ¬ h (addrV + p) < h (addrA + p) + 2 ^ r)
    (hnab : ¬ h (addrA + p) + 2 ^ r < h (addrV + p))
    (h7 : h 7 = 0) (h8 : h 8 = 1) (hp : 1 ≤ p) (S : Nat) :
    ∃ st', (st' 0 = addrV + p) ∧ (st' 1 = addrA + p) ∧ (st' 2 = p) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 4) 3 0 (memOf w st)
        = exec (cmpSeg cont) ρ S 19 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s2 : st 2 = p := k2
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : (cmpSeg cont).getD 3 Instr.reject = Instr.blt 3 5 8 := rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hnlt)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have d4 : (cmpSeg cont).getD 4 Instr.reject = Instr.blt 5 3 12 := rfl
  rw [exec_blt_ge_step (S := S + 3) (hS := by omega) d4 hfit (by rw [k3, k5]; exact hnab)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d5 : (cmpSeg cont).getD 5 Instr.reject = Instr.add 6 7 8 := rfl
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
  have d6 : (cmpSeg cont).getD 6 Instr.reject = Instr.blt 7 2 19 := rfl
  rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d6 hf1 (by rw [e7', e2]; omega)]
  rw [show S + 1 - 1 = S + 0 from rfl]
  refine ⟨s1, ?_, ?_, ?_, ha1, hf1, ?_⟩
  · rw [hs1, up_ne (by decide : (0 : Nat) ≠ 6)]; exact k0
  · rw [hs1, up_ne (by decide : (1 : Nat) ≠ 6)]; exact k1
  · exact e2
  · simp

/-- **The A-side tie, with digits below** (`pc 3 → pc 19`, 8 steps): `a = v + 2^r`,
so the sides are exchanged (cells `0`/`1`) and the walk runs on the mirror. -/
theorem cmpSeg_tieA {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
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
      exec (cmpSeg cont) ρ (S + 8) 3 0 (memOf w st)
        = exec (cmpSeg cont) ρ S 19 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have d3 : (cmpSeg cont).getD 3 Instr.reject = Instr.blt 3 5 8 := rfl
  rw [exec_blt_lt_step (S := S + 8) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 8 - 1 = S + 7 from rfl]
  have d8 : (cmpSeg cont).getD 8 Instr.reject = Instr.add 5 3 9 := rfl
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
  have d9 : (cmpSeg cont).getD 9 Instr.reject = Instr.blt 4 5 14 := rfl
  rw [exec_blt_ge_step (S := S + 6) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact hnat)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d10 : (cmpSeg cont).getD 10 Instr.reject = Instr.blt 5 4 12 := rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d10 hf1 (by rw [e4, e5]; exact hnbe)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have e2 : s1 2 = p := by
    rw [hs1, up_ne (by decide : (2 : Nat) ≠ 5)]; exact k2
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have d11 : (cmpSeg cont).getD 11 Instr.reject = Instr.blt 7 2 16 := rfl
  rw [exec_blt_lt_step (S := S + 4) (hS := by omega) d11 hf1 (by rw [e7, e2]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  -- 16, 17, 18: exchange cells 0 and 1 through cell 10
  have d16 : (cmpSeg cont).getD 16 Instr.reject = Instr.add 10 0 7 := rfl
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
  have d17 : (cmpSeg cont).getD 17 Instr.reject = Instr.add 0 1 7 := rfl
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
  have d18 : (cmpSeg cont).getD 18 Instr.reject = Instr.add 1 10 7 := rfl
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

/-- **The V-side tie at `p = 0`** (`pc 3 → cont`, 7 steps): with no digit below, the
tie is a hit outright and the walk is not entered. -/
theorem cmpSeg_tieV_zero {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA 0 r)
    (hnlt : ¬ h (addrV + 0) < h (addrA + 0) + 2 ^ r)
    (hnab : ¬ h (addrA + 0) + 2 ^ r < h (addrV + 0))
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA 0 r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 7) 3 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s2 : st 2 = 0 := k2
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : (cmpSeg cont).getD 3 Instr.reject = Instr.blt 3 5 8 := rfl
  rw [exec_blt_ge_step (S := S + 7) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hnlt)]
  rw [show S + 7 - 1 = S + 6 from rfl]
  have d4 : (cmpSeg cont).getD 4 Instr.reject = Instr.blt 5 3 12 := rfl
  rw [exec_blt_ge_step (S := S + 6) (hS := by omega) d4 hfit (by rw [k3, k5]; exact hnab)]
  rw [show S + 6 - 1 = S + 5 from rfl]
  have d5 : (cmpSeg cont).getD 5 Instr.reject = Instr.add 6 7 8 := rfl
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
  have d6 : (cmpSeg cont).getD 6 Instr.reject = Instr.blt 7 2 19 := rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d6 hf1 (by rw [e7', e2]; omega)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have e8' : s1 8 = 1 := by rw [hs1, up_ne (by decide : (8 : Nat) ≠ 6)]; exact s8
  have d7 : (cmpSeg cont).getD 7 Instr.reject = Instr.blt 7 8 12 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d7 hf1 (by rw [e7', e8']; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : (cmpSeg cont).getD 12 Instr.reject = Instr.one 6 := rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s2' : Nat → Nat := up s1 6 1 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2' z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2' z < 2 ^ w := upFit hf1 h8w
  have e72 : s2' 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7'
  have e82 : s2' 8 = 1 := by rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6)]; exact e8'
  have d13 : (cmpSeg cont).getD 13 Instr.reject = Instr.blt 7 8 cont := rfl
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

/-- **The A-side tie at `p = 0`** (`pc 3 → cont`, 7 steps): mirror of
`cmpSeg_tieV_zero`; the swap is skipped because there is nothing to walk. -/
theorem cmpSeg_tieA_zero {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
    {addrV addrA r : Nat} {st : Nat → Nat}
    (hH : CmpHead w h st addrV addrA 0 r) (h9 : h 9 = 2 ^ r)
    (hvlt : h (addrV + 0) < h (addrA + 0) + 2 ^ r)
    (hnat : ¬ h (addrA + 0) < h (addrV + 0) + 2 ^ r)
    (hnbe : ¬ h (addrV + 0) + 2 ^ r < h (addrA + 0))
    (hadV : h (addrV + 0) + 2 ^ r < 2 ^ w)
    (h7 : h 7 = 0) (h8 : h 8 = 1) (S : Nat) :
    ∃ st', (st' 6 = (if digHalf h h addrV addrA 0 r then 1 else 0)) ∧
        (∀ z, ¬ CmpCell z → st' z = h z) ∧ (∀ z, st' z < 2 ^ w) ∧
      exec (cmpSeg cont) ρ (S + 7) 3 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  obtain ⟨k0, k1, k2, k3, k4, k5, hag, hfit⟩ := hH
  have s2 : st 2 = 0 := k2
  have s7 : st 7 = 0 := by rw [hag 7 not_cmpCell_seven]; exact h7
  have s8 : st 8 = 1 := by rw [hag 8 not_cmpCell_eight]; exact h8
  have h8w : (1 : Nat) < 2 ^ w := by rw [← s8]; exact hfit 8
  have d3 : (cmpSeg cont).getD 3 Instr.reject = Instr.blt 3 5 8 := rfl
  rw [exec_blt_lt_step (S := S + 7) (hS := by omega) d3 hfit (by rw [k3, k5]; exact hvlt)]
  rw [show S + 7 - 1 = S + 6 from rfl]
  have d8 : (cmpSeg cont).getD 8 Instr.reject = Instr.add 5 3 9 := rfl
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
  have d9 : (cmpSeg cont).getD 9 Instr.reject = Instr.blt 4 5 14 := rfl
  rw [exec_blt_ge_step (S := S + 5) (hS := by omega) d9 hf1 (by rw [e4, e5]; exact hnat)]
  rw [show S + 5 - 1 = S + 4 from rfl]
  have d10 : (cmpSeg cont).getD 10 Instr.reject = Instr.blt 5 4 12 := rfl
  rw [exec_blt_ge_step (S := S + 4) (hS := by omega) d10 hf1 (by rw [e4, e5]; exact hnbe)]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have e2 : s1 2 = 0 := by rw [hs1, up_ne (by decide : (2 : Nat) ≠ 5)]; exact s2
  have e7 : s1 7 = 0 := by rw [hs1, up_ne (by decide : (7 : Nat) ≠ 5)]; exact s7
  have d11 : (cmpSeg cont).getD 11 Instr.reject = Instr.blt 7 2 16 := rfl
  rw [exec_blt_ge_step (S := S + 3) (hS := by omega) d11 hf1 (by rw [e7, e2]; omega)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d12 : (cmpSeg cont).getD 12 Instr.reject = Instr.one 6 := rfl
  rw [exec_one_step (S := S + 2) (hS := by omega) d12]
  rw [show S + 2 - 1 = S + 1 from rfl]
  set s2' : Nat → Nat := up s1 6 1 with hs2
  have ha2 : ∀ z, ¬ CmpCell z → s2' z = h z := cmpAgree_up cmpCell_six ha1
  have hf2 : ∀ z, s2' z < 2 ^ w := upFit hf1 h8w
  have e72 : s2' 7 = 0 := by rw [hs2, up_ne (by decide : (7 : Nat) ≠ 6)]; exact e7
  have e82 : s2' 8 = 1 := by
    rw [hs2, up_ne (by decide : (8 : Nat) ≠ 6), hs1, up_ne (by decide : (8 : Nat) ≠ 5)]
    exact s8
  have d13 : (cmpSeg cont).getD 13 Instr.reject = Instr.blt 7 8 cont := rfl
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

/-! ### §C6 — the segment theorem, and the fuel's exactness

`cmpSegCost` is the segment's step count as a function of the digits at `p` — one
closed term per prologue branch, so the theorem below assembles by `omega` on
literals rather than by resolving an existential. -/

/-- **The segment's step count.**  Prologue (`3`) plus the branch taken: `4` the
A-side decided hit, `5` the decided miss, `6` the V-side decided hit, `7` a `p = 0`
tie (hit outright), and the two ties that descend cost `4`/`8` into the walk plus
`walkCost`.  Mirrors the *program's* branch order (`v < a + 2^r` first), not
`digHalf`'s, because the cost is a property of the code. -/
def cmpSegCost (h : Nat → Nat) (addrV addrA p r : Nat) : Nat :=
  if h (addrV + p) < h (addrA + p) + 2 ^ r then
    (if h (addrA + p) < h (addrV + p) + 2 ^ r then 8
     else if h (addrV + p) + 2 ^ r < h (addrA + p) then 9
     else if p = 0 then 10 else 11 + walkCost h addrA addrV p)
  else
    (if h (addrA + p) + 2 ^ r < h (addrV + p) then 7
     else if p = 0 then 10 else 7 + walkCost h addrV addrA p)

/-- **The segment costs at most `cmpSegFuel p = 14 + 9p`.**  With `cmpSegCost_le`
the exact costs stay visible to a caller that knows its branch, and the bound is the
one residual (iv) can charge without knowing them. -/
theorem cmpSegCost_le (h : Nat → Nat) (addrV addrA p r : Nat) :
    cmpSegCost h addrV addrA p r ≤ cmpSegFuel p := by
  unfold cmpSegCost cmpSegFuel
  by_cases b1 : h (addrV + p) < h (addrA + p) + 2 ^ r
  · rw [if_pos b1]
    by_cases b2 : h (addrA + p) < h (addrV + p) + 2 ^ r
    · rw [if_pos b2]; omega
    · rw [if_neg b2]
      by_cases b3 : h (addrV + p) + 2 ^ r < h (addrA + p)
      · rw [if_pos b3]; omega
      · rw [if_neg b3]
        by_cases hp0 : p = 0
        · rw [if_pos hp0]; omega
        · rw [if_neg hp0]
          have hw := walkCost_le h addrA addrV p (by omega)
          omega
  · rw [if_neg b1]
    by_cases b4 : h (addrA + p) + 2 ^ r < h (addrV + p)
    · rw [if_pos b4]; omega
    · rw [if_neg b4]
      by_cases hp0 : p = 0
      · rw [if_pos hp0]; omega
      · rw [if_neg hp0]
        have hw := walkCost_le h addrV addrA p (by omega)
        omega

/-- **THE SEGMENT.**  From §D5's register precondition — cells `0`/`1` the two digit
addresses at `p`, cell `2 = p`, cells `7`/`8`/`9` the constants `0`/`1`/`2^r`, and
the frame (`CmpCell`) with the word fit — the run of `cmpSeg cont` reaches `cont` in
exactly `cmpSegCost` steps with cell `6` = `digHalf`'s verdict as a word, touching no
cell outside `CmpCell`.  The one pair of premises beyond the frame is the
single-word fit of `d + 2^r` (`hadA`, `hadV`), free at `r + 2 ≤ w`
(`two_pow_add_fits`). -/
theorem cmpSeg_reaches {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
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
      exec (cmpSeg cont) ρ (S + cmpSegCost h addrV addrA p r) 0 0 (memOf w st)
        = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  unfold cmpSegCost
  by_cases b1 : h (addrV + p) < h (addrA + p) + 2 ^ r
  · rw [if_pos b1]
    by_cases b2 : h (addrA + p) < h (addrV + p) + 2 ^ r
    · -- the decided miss: 8 = 3 + 5
      rw [if_pos b2]
      obtain ⟨s3, hH, hstep1⟩ :=
        cmpSeg_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 5)
      obtain ⟨st', h6, hag', hf', hstep2⟩ :=
        cmpSeg_miss (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hH h9 b1 b2 hadV h7 h8 S
      exact ⟨st', h6, hag', hf', by rw [show S + 8 = S + 5 + 3 from by omega, hstep1, hstep2]⟩
    · rw [if_neg b2]
      by_cases b3 : h (addrV + p) + 2 ^ r < h (addrA + p)
      · -- the V-side decided hit: 9 = 3 + 6
        rw [if_pos b3]
        obtain ⟨s3, hH, hstep1⟩ :=
          cmpSeg_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 6)
        obtain ⟨st', h6, hag', hf', hstep2⟩ :=
          cmpSeg_below (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hH h9 b1 b2 b3 hadV h7 h8 S
        exact ⟨st', h6, hag', hf',
          by rw [show S + 9 = S + 6 + 3 from by omega, hstep1, hstep2]⟩
      · rw [if_neg b3]
        by_cases hp0 : p = 0
        · -- the A-side tie at `p = 0`: hit outright, 10 = 3 + 7
          rw [if_pos hp0]
          subst hp0
          obtain ⟨s3, hH, hstep1⟩ :=
            cmpSeg_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
              (p := 0) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 7)
          obtain ⟨st', h6, hag', hf', hstep2⟩ :=
            cmpSeg_tieA_zero (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
              (r := r) hH h9 b1 b2 b3 hadV h7 h8 S
          exact ⟨st', h6, hag', hf',
            by rw [show S + 10 = S + 7 + 3 from by omega, hstep1, hstep2]⟩
        · -- the A-side tie: swap, then the walk
          rw [if_neg hp0]
          have hp1 : 1 ≤ p := by omega
          obtain ⟨s3, hH, hstep1⟩ :=
            cmpSeg_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
              (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA
              (S := S + 8 + walkCost h addrA addrV p)
          obtain ⟨s4, g0, g1, g2, hag4, hf4, hstep2⟩ :=
            cmpSeg_tieA (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
              (p := p) (r := r) hfitH hV hA hH h9 b1 b2 b3 hadV h7 h8 hp1
              (S := S + walkCost h addrA addrV p)
          obtain ⟨st', h6, hag', hf', hstep3⟩ :=
            cmpSeg_walk (cont := cont) (h := h) (addrV := addrA) (addrA := addrV)
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
        cmpSeg_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 4)
      obtain ⟨st', h6, hag', hf', hstep2⟩ :=
        cmpSeg_above (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
          (p := p) (r := r) hH b1 b4 h7 h8 S
      exact ⟨st', h6, hag', hf', by rw [show S + 7 = S + 4 + 3 from by omega, hstep1, hstep2]⟩
    · rw [if_neg b4]
      by_cases hp0 : p = 0
      · -- the V-side tie at `p = 0`: hit outright, 10 = 3 + 7
        rw [if_pos hp0]
        subst hp0
        obtain ⟨s3, hH, hstep1⟩ :=
          cmpSeg_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
            (p := 0) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA (S := S + 7)
        obtain ⟨st', h6, hag', hf', hstep2⟩ :=
          cmpSeg_tieV_zero (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
            (r := r) hH b1 b4 h7 h8 S
        exact ⟨st', h6, hag', hf',
          by rw [show S + 10 = S + 7 + 3 from by omega, hstep1, hstep2]⟩
      · -- the V-side tie: the walk without the swap
        rw [if_neg hp0]
        have hp1 : 1 ≤ p := by omega
        obtain ⟨s3, hH, hstep1⟩ :=
          cmpSeg_head (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hV hA hfitH h9 k0 k1 k2 hag hfit hadA
            (S := S + 4 + walkCost h addrV addrA p)
        obtain ⟨s4, g0, g1, g2, hag4, hf4, hstep2⟩ :=
          cmpSeg_tieV (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
            (p := p) (r := r) hfitH hV hA hH b1 b4 h7 h8 hp1
            (S := S + walkCost h addrV addrA p)
        obtain ⟨st', h6, hag', hf', hstep3⟩ :=
          cmpSeg_walk (cont := cont) (h := h) (addrV := addrV) (addrA := addrA)
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

/-- **The headline bound.**  The segment reaches `cont` *within* `cmpSegFuel p` steps
— §D5's stated obligation, with the exact cost still available through
`cmpSeg_reaches` / `cmpSegCost`. -/
theorem cmpSeg_reaches_bound {cont : Nat} {ρ : Nat → BitVec w} {h : Nat → Nat}
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
        exec (cmpSeg cont) ρ (S + k) 0 0 (memOf w st)
          = exec (cmpSeg cont) ρ S cont 0 (memOf w st') := by
  obtain ⟨st', h6, hag', hf', hstep⟩ := cmpSeg_reaches hfitH hV hA h7 h8 h9 k0 k1 k2
    hadA hadV hag hfit S
  exact ⟨_, cmpSegCost_le h addrV addrA p r, st', h6, hag', hf', hstep⟩

/-- **The fuel is attained, not slack.**  On the A-side tie with every low digit
equal — the walk's expensive path — the segment costs exactly `cmpSegFuel p`.  So
`cmpSegFuel` is the segment's worst case and not an estimate of it. -/
theorem cmpSegCost_tight {h : Nat → Nat} {addrV addrA p r : Nat}
    (hp : 1 ≤ p) (htie : h (addrA + p) = h (addrV + p) + 2 ^ r)
    (hall : ∀ i, i < p → h (addrA + i) = h (addrV + i)) :
    cmpSegCost h addrV addrA p r = cmpSegFuel p := by
  have ht : 0 < 2 ^ r := Nat.two_pow_pos r
  have hvlt : h (addrV + p) < h (addrA + p) + 2 ^ r := by omega
  have hnat : ¬ h (addrA + p) < h (addrV + p) + 2 ^ r := by omega
  have hnbe : ¬ h (addrV + p) + 2 ^ r < h (addrA + p) := by omega
  have hp0 : ¬ p = 0 := by omega
  rw [cmpSegCost, if_pos hvlt, if_neg hnat, if_neg hnbe, if_neg hp0,
    walkCost_eq_of_all_eq h addrA addrV p hp hall]
  unfold cmpSegFuel
  omega

/-! ### §C7 — the composition state

The segment's internal jump targets are absolute, so it can sit only at offset `0` of
the program that contains it.  `cmpSegmentProgram` is that program, and
`cmpSegment_getD` proves the segment's `getD` facts transfer to it; the state
interface (`cell 6 = verdict`, `CmpCell` untouched) is what a loop reads. -/

/-- The program shape the segment requires: `cmpSeg 29 ++ tail`, i.e. the compare
segment at offset `0` and the caller's continuation from `29`. -/
def cmpSegmentProgram (tail : List Instr) : List Instr := cmpSeg (cmpSeg 29).length ++ tail

/-- **The segment's `getD` facts transfer to the composed program.**  Positions
`0…28` are `cmpSeg`'s own; the tail starts at `29`.  This is the whole of the
"composition is free" claim — and it is the *only* part of it that is free. -/
theorem cmpSegment_getD (tail : List Instr) {i : Nat} (hi : i ≤ 28) :
    (cmpSegmentProgram tail).getD i Instr.reject = (cmpSeg 29).getD i Instr.reject := by
  unfold cmpSegmentProgram
  rw [cmpSeg_length]
  have hlen : i < (cmpSeg 29).length := by rw [cmpSeg_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]

/-- **The verdict in the row's own vocabulary.**  Cell 6 is `1` exactly when §7 step
7's integer test fires — the bridge `halfTest_iff_wordDiff` and `hitWord_binSumTest`
already own, so the loop's consumer needs no new predicate. -/
theorem cmpSeg_cell6_iff_wordTest {w F stride : Nat} {h : Nat → Nat} {addrV addrA v : Nat}
    (hw : 1 ≤ w) (hF : 1 ≤ F) (hfit : ∀ z, h z < 2 ^ w)
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w h addrV stride < 2 ^ F) (hAb : numAt w h addrA stride < 2 ^ F)
    (h6 : v = (if digHalf h h addrV addrA ((F - 1) / w) ((F - 1) % w) then 1 else 0)) :
    (v = 1) ↔ 2 ^ (F - 1) ≤ wordDiff (numAt w h addrV stride) (numAt w h addrA stride) := by
  have hkey := digHalf_eq_threshold hw hF h h hfit hfit hp hVb hAb
  rw [h6]
  by_cases hd : digHalf h h addrV addrA ((F - 1) / w) ((F - 1) % w) = true
  · rw [if_pos hd]; exact ⟨fun _ => hkey.mp hd, fun _ => rfl⟩
  · rw [if_neg hd]
    exact ⟨fun hc => absurd hc (by decide), fun hc => absurd (hkey.mpr hc) hd⟩


/-! ### §C8 — end-to-end spot checks, kernel-checked

The real test of a segment proof is that the *program* does what the theorem says, so
these run `exec` on the actual `Instr` list with the segment at offset `0` and a
three-instruction tail that turns cell 6 into the verdict (`blt 7 6 31`, `reject`,
`accept`).  Fuel is chosen one step above and one step below each branch's cost, so
each pair pins both the verdict *and* the cost — the tie case's `24 → none` is the
tightness of `cmpSegFuel` measured on the program rather than argued.  `decide`, not
`native_decide`: the house banner admits no `Lean.ofReduceBool`. -/

/-- The three-instruction tail: `hit ⇔ cell 6 ≠ 0`, as a verdict. -/
def cmpSegSpotTail : List Instr := [ .blt 7 6 31, .reject, .accept ]

/-- A concrete state at `p = 1`, `r = 1` (`2^r = 2`): V's block at `11`, A's at `21`,
the two digits at `p` given by `d1`, `d2`, and equal low digits (`3`, `3`). -/
def cmpSegSpotState (d1 d2 : Nat) : Nat → Nat :=
  fun z => if z = 0 then 12 else if z = 1 then 22 else if z = 2 then 1
    else if z = 7 then 0 else if z = 8 then 1 else if z = 9 then 2
    else if z = 11 then 3 else if z = 12 then d1
    else if z = 21 then 3 else if z = 22 then d2 else 0

/-- A concrete state at `p = 0` with `r = 2` (`2^r = 4`): no digit below `p`, so a
tie is decided by the prologue alone. -/
def cmpSegSpotZero (dv da : Nat) : Nat → Nat :=
  fun z => if z = 0 then 11 else if z = 1 then 21 else if z = 2 then 0
    else if z = 7 then 0 else if z = 8 then 1 else if z = 9 then 4
    else if z = 11 then dv else if z = 21 then da else 0

/-- The A-side tie with all low digits equal — the expensive path: hit, and it takes
the full `cmpSegFuel 1 = 23` segment steps (`25 = 23 + 2`). -/
theorem cmpSeg_spot_tieA :
    exec (cmpSeg 29 ++ cmpSegSpotTail) (fun _ => 0) 25 0 0
      (memOf 6 (cmpSegSpotState 0 2)) = some true := by decide

/-- One step short of that tie does not halt: the bound is exact. -/
theorem cmpSeg_spot_tieA_short :
    exec (cmpSeg 29 ++ cmpSegSpotTail) (fun _ => 0) 24 0 0
      (memOf 6 (cmpSegSpotState 0 2)) = none := by decide

/-- Equal digits at `p`, neither `2^r` apart: the decided miss. -/
theorem cmpSeg_spot_miss :
    exec (cmpSeg 29 ++ cmpSegSpotTail) (fun _ => 0) 11 0 0
      (memOf 6 (cmpSegSpotState 3 3)) = some false := by decide

/-- A's digit `2^r` *below* V's: the decided hit, `7 + 2 = 9`. -/
theorem cmpSeg_spot_above :
    exec (cmpSeg 29 ++ cmpSegSpotTail) (fun _ => 0) 9 0 0
      (memOf 6 (cmpSegSpotState 8 2)) = some true := by decide

/-- One step short does not halt there either. -/
theorem cmpSeg_spot_above_short :
    exec (cmpSeg 29 ++ cmpSegSpotTail) (fun _ => 0) 8 0 0
      (memOf 6 (cmpSegSpotState 8 2)) = none := by decide

/-- **The `p = 0` tie**: `v = a + 2^r` with no digit below, so the verdict is a hit
and the walk is never entered (`10 + 2 = 12`).  This is the case the segment's first
draft got wrong by descending to address `−1` — `KapilaDigitwise` §D5's defect (1) —
pinned here on the program rather than only in prose. -/
theorem cmpSeg_spot_tieV_zero :
    exec (cmpSeg 29 ++ cmpSegSpotTail) (fun _ => 0) 12 0 0
      (memOf 6 (cmpSegSpotZero 4 0)) = some true := by decide

/-- One step short of the `p = 0` tie does not halt. -/
theorem cmpSeg_spot_tieV_zero_short :
    exec (cmpSeg 29 ++ cmpSegSpotTail) (fun _ => 0) 11 0 0
      (memOf 6 (cmpSegSpotZero 4 0)) = none := by decide

end SubsetSumL25.Row
