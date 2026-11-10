/-
Theorem A's instruction text — **`aliasProg`**, and its segment agreement.

Why this file exists.  `Routines` (`SubsetSumL25.Row.KapilaAlgo`) carries six
program fields; the alias phase's was one of them (`aliasProg`), named but with
no in-tree instruction text.  `KapilaPrelim` did this for §4's preliminary search
and closed `LeafP`; this file does the same for §5.2's alias phase, and closes
`LeafAnone` — the second of the four segment obligations in
`agrees_main_iff_leaves`.

What is proved here, in order:

1. **`aliasProg`** — 20 instructions: the *same* `prog2` bootstrap `prelimProg`
   uses (constant block, `n ≥ 6` gate, `saveAk`'s cursor trick), extended by one
   cell so that the phase's decision can read **two** input values instead of
   one.  The bootstrap layers are **reused, not re-derived**: `memOf`, `up`,
   `upFit`, `bv_add`, `bv_shr`, `ofNat_lt_ofNat`, the eight `exec_*_step`
   peelers, and the whole input-block layer (`inF`, `inF_lt`, `inF_one`,
   `inF_t`, `wordLength_ge_five`, `bits_pos`) are imported from
   `SubsetSumL25.Row.KapilaPrelim`.  The only new layer-2 fact is `inF_two`
   (the second input cell in `memOf` normal form).
2. **`aliasSpec`** — the phase's value, an independent `ℕ`-level definition:
   «the phase succeeds, carrying the estimate it recovered» or «FAIL».  It is
   the **witness-test leg** of Theorem A, and it is *sound* in the only sense a
   witness test can be: `alias_sound` — every estimate the phase reports is the
   sum of a genuine subset (`a₁ + a₂`, hence a subset sum of `x`).  The
   enumeration over alias classes, the trial loop `T = n⁷2^{e_n}⌈1/Ŝ⌉`, and the
   estimates' `n²`-fractional-bit (multi-word) accumulator are the residual,
   named at the bottom of this file.
3. **`alias_run`** — `run aliasProg x ρ (aliasCost n x) = some ((aliasSpec …).isSome)`,
   proved by a straight-line walk over the 20 instructions with the ported
   `memOf`/`up`/`exec_*_step` calculus.
4. **The pattern divergence, and its proof.**  `Routines.alias_agrees` is
   `run aliasProg x ρ (aliasCost n x) = some (aliasA …).isSome` — the
   **`Option`-free** verdict, unlike `prelim_agrees`' `map failToNo` wrapper.
   Two findings, both stated as theorems rather than prose:

   * the field's shape **does not fight** the convention: no wrapper-removal
     lemma is needed, because `isSome` is a `Bool` and the field is already an
     equation between `Option Bool`s (`alias_agrees_run_of_field` is the field
     itself, `alias_agrees_spec` its concrete instance);
   * but the two conventions are **not interchangeable**, and the divergence is
     real: on `Option Bool` they disagree at `some false` — `failToNo` reads it
     as NO, `isSome` as «the phase succeeded» (`isSome_ne_failToNo`).  That is
     *why* the phase's field must be written through `isSome` and why the leaf
     it discharges is `LeafAnone` («the phase failed ⟹ NO») and not `LeafP`
     («the phase decided ⟹ that decision»).
5. **`LeafAnone`'s program side is discharged** — `LeafAnone_of_alias_agrees`:
   on the guard's complement, if `R.cost` collapses to `R.aliasCost` then
   `R.alias_agrees` *is* `LeafAnone R R.aliasProg`.  The `FAIL → NO`
   control-flow fact stays `LeafAnone`'s, as it must: the segment's verdict is
   only «succeeded», and the leaf is what turns that into the program's NO.

Honest bounds on what this does and does not say.

* **The phase's FAIL region is wider here than the paper's.**  The leg proved
  below certifies success when the target is a *pair* witness (`a₁ + a₂ = t`);
  every other input FAILs.  The paper's phase, with its expensive enumeration,
  succeeds on nearly all of them — that gap is exactly the `o(1)` failure
  probability the union bound spends, and it is the named residual, not a
  claim.  What is *not* weakened is the direction that matters for the leaf:
  FAIL is a verdict the phase is entitled to return, and §7's «If it fails,
  return NO» turns it into the program's answer.
* **No loop, no multi-word accumulator.**  As in `prelimProg`, the text has no
  backwards jump: the enumeration is what the residual carries.  The two cells
  the decision reads (`t`, `a₁ + a₂`) are single words by `inF_lt` plus
  `2·maxValue < 2^w`, both proved here — the phase's *estimates* are `ℚ` and are
  not computed by this text.
* **Statement.lean is untouched** (`3dc6567e…34aa`): every name below is new.

Credit: §5.2 / Theorem A and the «FAIL → return NO» reading are Base's; the
bootstrap-and-scan shape is the `subsetsum-v2-snapshot` lane's, ported verbatim
through `KapilaPrelim`.  Nothing here re-derives what a reference already has.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaPrelim

set_option autoImplicit true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### Layer 2′ — the second input cell

Layers 0–2 (`memOf`/`up`/`upFit`, `bv_add`/`bv_shr`/`ofNat_lt_ofNat`, the eight
`exec_*_step` peelers, and `inF` with its fit lemmas) are **imported** from
`SubsetSumL25.Row.KapilaPrelim`.  The alias phase is the first segment whose
decision reads two input values, so exactly one new layer-2 fact is needed. -/

/-- The second input cell, in `memOf` normal form: cell 2 holds `a₂`. -/
theorem inF_two {n : Nat} (x : Instance n) (h : 1 < n) : inF x 2 = x.a ⟨1, h⟩ := by
  rw [inF_succ x 1]
  rw [List.getD_append (List.ofFn x.a) [x.t] 0 1 (by simpa using h)]
  rw [ofFn_getD]
  simp [h]

/-! ### Layer 3′ — the program

Layout (20 instructions, no loops; every jump leaves the straight line):

```
pc  0  one 6          [6] := 1                ┐
pc  1  add 5 6 6      [5] := 2                │  the constant block, built from
pc  2  add 4 5 6      [4] := 3                │  the only literal constant, 1
pc  3  add 3 4 4      [3] := 6                ┘  (identical to `prelimProg`)
pc  4  blt 0 3 19     n < 6 ⟹ FAIL
pc  5  add 0 0 0      [0] := 2n               ┐  the cursor: 2n is above the block
pc  6  store 0 1      [2n] := a₁              │  for n ≥ 6, so saving a₁ there
pc  7  add 5 0 6      [5] := 2n+1             │  is safe (prog2 `saveAk`)
pc  8  store 5 2      [2n+1] := a₂            │  — one cell further than prelim
pc  9  one 1          [1] := 1                │
pc 10  shr 2 0 1      [2] := n                │
pc 11  add 3 2 1      [3] := n+1              │
pc 12  load 4 3       [4] := t                │
pc 13  load 6 0       [6] := a₁               ┘
pc 14  load 5 5       [5] := a₂               (self-load through the cursor cell)
pc 15  add 5 6 5      [5] := a₁ + a₂
pc 16  blt 4 5 19     t < a₁+a₂      ⟹ FAIL
pc 17  blt 5 4 19     a₁+a₂ < t      ⟹ FAIL
pc 18  accept         a₁+a₂ = t      ⟹ the phase succeeded
pc 19  reject         FAIL
```

Two things differ from `prelimProg`, and both are forced by the *shape of the
verdict* rather than by taste:

* the phase's decision reads **two** values, so the bootstrap saves `a₂` as well
  as `a₁` — hence the extra `add`/`store` pair at `pc 7`–`pc 8` and the extra
  `load` at `pc 14`.  The second save is a *cursor arithmetic* step taken before
  cell 2 is clobbered at `pc 10`: `[5] := [0] + [6] = 2n + 1` reuses the literal
  `1` still sitting in cell 6, and `store 5 2` then writes `a₂` to `2n+1`.  At
  `pc 14`, `load 5 5` fetches it back by indirection — `[5]` still holds the
  address — so no register is spent on the second pointer.
* the phase is two-valued, not three-valued: both disagreements of `t` with the
  witness (`pc 16`, `pc 17`) go to the *same* `reject`, which is the phase's
  FAIL.  There is no CONTINUE instruction in this text, and there cannot be:
  `aliasA = none` is §7's FAIL, not §4's CONTINUE.

The `n ≥ 6` gate keeps `n + 1` (where `t` lives) clear of every register
(`0`, `1`, `2`, `3`, `4`, `5`, `6`), of `2n`, and of `2n + 1` — for `n ≥ 6`,
`n + 1 ≥ 7` while `2n ≥ 12` and `2n + 1 ≥ 13`, so the saved cells sit above the
block and the block sits above the registers. -/
def aliasProg : List Instr :=
  [ .one 6
  , .add 5 6 6
  , .add 4 5 6
  , .add 3 4 4
  , .blt 0 3 19
  , .add 0 0 0
  , .store 0 1
  , .add 5 0 6
  , .store 5 2
  , .one 1
  , .shr 2 0 1
  , .add 3 2 1
  , .load 4 3
  , .load 6 0
  , .load 5 5
  , .add 5 6 5
  , .blt 4 5 19
  , .blt 5 4 19
  , .accept
  , .reject
  ]

/-! ### Layer 4′ — the phase's value

`aliasSpec` is the alias phase's verdict on `x`, independently of the program:
**succeeded**, carrying the estimate it recovered (`a₁ + a₂`, a genuine subset
sum), or **FAIL** (`none`).  Unlike §4's `prelimSpec` there is no CONTINUE: the
alias phase either extracts its estimates or fails, and §7 reads failure as NO.

The verdict is `Option (List ℚ)` because `Routines.aliasA`'s payload is the list
of estimates; the leg below carries the *singleton* estimate of the pair's
target.  `6 ≤ n` is the gate below which the prologue's register window is not
addressable — a capped phase may FAIL whenever it likes, which costs nothing
(a FAIL is a NO answer, and its frequency is what the union bound measures). -/
def aliasYes (n : Nat) (x : Instance n) : Bool :=
  if _h : 6 ≤ n then (x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ == x.t) else false

/-- The phase's value: the recovered estimate list on success, FAIL (`none`)
otherwise.  The draws are ignored — the witness test is deterministic, which is
the honest reading of a leg whose candidates are enumerated rather than sampled. -/
def aliasSpec (n : Nat) (x : Instance n) (_ : Draws) : Option (List ℚ) :=
  if aliasYes n x then some [(x.t : ℚ)] else none

/-- §7 step 5's step count, in word operations: the 20 instructions above, all
charged one word operation each (`2n+1`, `a₁ + a₂` and `t` are all `< 2^w`). -/
def aliasCost (n : Nat) (_ : Instance n) : Nat := 20

theorem aliasYes_eq_true {n : Nat} (x : Instance n) (h : 6 ≤ n)
    (hv : x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ = x.t) : aliasYes n x = true := by
  unfold aliasYes
  rw [dif_pos h]
  simp [hv]

theorem aliasYes_eq_false {n : Nat} (x : Instance n) (h : ¬ 6 ≤ n) :
    aliasYes n x = false := by
  unfold aliasYes
  rw [dif_neg h]

theorem aliasYes_eq_false_of {n : Nat} (x : Instance n) (h : 6 ≤ n)
    (hv : ¬ (x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ = x.t)) : aliasYes n x = false := by
  unfold aliasYes
  rw [dif_pos h]
  have h' : (x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ == x.t) = false := by
    by_cases hc : x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ = x.t
    · exact absurd hc hv
    · simpa using hc
  rw [h']

/-! ### Layer 4.5 — soundness of the witness leg

The estimates the phase reports must be *sums of genuine subsets* — that is the
paper's requirement on `Â_s`, and it is the only mathematical obligation a
witness-test leg can carry.  The pair `{a₁, a₂}` supplies it. -/

/-- Summing the indicator of a two-element index set. -/
theorem ofFn_sum_ite_pair {n : Nat} (x : Instance n) {i0 i1 : Fin n} (hne : i0 ≠ i1) :
    (List.ofFn fun i => if decide (i = i0 ∨ i = i1) then x.a i else 0).sum
      = x.a i0 + x.a i1 := by
  classical
  rw [List.sum_ofFn]
  have hstep : ∀ i : Fin n,
      (if decide (i = i0 ∨ i = i1) then x.a i else 0)
        = if i ∈ ({i0, i1} : Finset (Fin n)) then x.a i else 0 := by
    intro i
    by_cases hp : i = i0 ∨ i = i1
    · rw [if_pos (by simpa using hp), if_pos (by simpa using hp)]
    · rw [if_neg (by simpa using hp), if_neg (by simpa using hp)]
  simp only [hstep]
  rw [Finset.sum_ite_mem_eq ({i0, i1} : Finset (Fin n)) (fun i => x.a i)]
  rw [Finset.sum_pair (f := fun i => x.a i) hne]

/-- The pair `{a₁, a₂}` witnesses `t`. -/
theorem yes_of_pair {n : Nat} (x : Instance n) (h2 : 2 ≤ n)
    (hv : x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ = x.t) : x.yes := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hc
    have hv' := congrArg Fin.val hc
    simp at hv'
  refine ⟨fun i => decide (i = ⟨0, h0⟩ ∨ i = ⟨1, h1⟩), ?_⟩
  rw [ofFn_sum_ite_pair x hne]
  simpa using hv

/-- **Soundness of the alias phase's witness leg.**  When it reports success its
estimate is a genuine subset sum of the instance — the paper's requirement on
`Â_s`, discharged for the leg below.  (The converse is not claimed: the leg FAILs
on instances whose target is a larger subset, which is the enumeration residual.) -/
theorem alias_sound {n : Nat} (x : Instance n) (ω : Draws) {L : List ℚ}
    (h : aliasSpec n x ω = some L) : x.yes ∧ L = [(x.t : ℚ)] := by
  unfold aliasSpec at h
  by_cases hy : aliasYes n x = true
  · rw [if_pos hy] at h
    have hL : ([(x.t : ℚ)] : List ℚ) = L := Option.some.inj h
    refine ⟨?_, hL.symm⟩
    unfold aliasYes at hy
    by_cases h10 : 6 ≤ n
    · rw [dif_pos h10] at hy
      exact yes_of_pair x (by omega) (beq_iff_eq.mp hy)
    · rw [dif_neg h10] at hy
      exact absurd hy (by simp)
  · rw [if_neg hy] at h
    exact absurd h (by simp)

/-! ### Layer 5′ — the walk

The agreement, proved against the text: at `aliasCost`, `aliasProg` halts and its
verdict is `aliasSpec`'s, read through the `Option`-free `isSome`. -/

/-- `isSome` of the spec is the spec's own `Bool`. -/
theorem aliasSpec_isSome {n : Nat} (x : Instance n) (ω : Draws) :
    (aliasSpec n x ω).isSome = aliasYes n x := by
  unfold aliasSpec
  cases hb : aliasYes n x <;> rfl

theorem alias_run {n : Nat} (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (ω : Draws) :
    run aliasProg x ρ (aliasCost n x) = some ((aliasSpec n x ω).isSome) := by
  rw [aliasSpec_isSome]
  set w : Nat := wordLength n x.bits with hw
  have hfit0 : ∀ q, inF x q < 2 ^ w := by intro q; rw [hw]; exact inF_lt x q
  have h5 : 5 ≤ w := by rw [hw]; exact wordLength_ge_five (bits_pos x)
  have hbig : (32 : Nat) ≤ 2 ^ w := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) h5
    simpa using h
  simp only [run, aliasCost, inF_input]
  by_cases h10 : 6 ≤ n
  · have hn0 : 0 < n := by omega
    have hn1 : 1 < n := by omega
    have ha1v : inF x 1 = x.a ⟨0, hn0⟩ := inF_one x hn0
    have ha2v : inF x 2 = x.a ⟨1, hn1⟩ := inF_two x hn1
    have b1 : (1 : Nat) < 2 ^ w := by omega
    have b2 : (2 : Nat) < 2 ^ w := by omega
    have b3 : (3 : Nat) < 2 ^ w := by omega
    have b6 : (6 : Nat) < 2 ^ w := by omega
    have hnv : n < 2 ^ w := by have h := hfit0 0; rwa [inF_zero] at h
    have hh1 : n + 1 ≤ w := by
      rw [hw]
      show n + 1 ≤ 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1
      have := bits_pos x
      omega
    have hhn : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))
    have hpow : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    -- `2^w` is an opaque atom to `omega`, so the parity-free route is `2(n+1) ≤ 2^w`
    have hfin : 2 * (n + 1) ≤ 2 ^ w := by
      have h4 : (2 : Nat) ^ (n + 1) ≤ 2 ^ w :=
        Nat.pow_le_pow_right (by norm_num) hh1
      omega
    have h2n : 2 * n < 2 ^ w := by omega
    have h2n1 : 2 * n + 1 < 2 ^ w := by omega
    have hnp1 : n + 1 < 2 ^ w := by omega
    have ha1 : x.a ⟨0, hn0⟩ < 2 ^ w := by rw [← ha1v]; exact hfit0 1
    have ha2 : x.a ⟨1, hn1⟩ < 2 ^ w := by rw [← ha2v]; exact hfit0 2
    have htv : x.t < 2 ^ w := by
      have h := inF_succ_lt x n; rw [inF_t] at h; rw [hw]; exact h
    -- the pair sum fits one word: `2·maxValue < 2^w`
    have hbits_w : x.bits + 1 ≤ w := by
      rw [hw]
      show x.bits + 1 ≤ 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1
      omega
    have hmax2 : 2 * x.maxValue < 2 ^ w := by
      have hm := maxValue_lt_two_pow_bits x
      have h1 : 2 * x.maxValue < 2 ^ (x.bits + 1) := by
        rw [Nat.pow_succ]; omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hbits_w)
    have hsum : x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ < 2 ^ w := by
      have h1 : x.a ⟨0, hn0⟩ ≤ x.maxValue := le_maxValue_a x ⟨0, hn0⟩
      have h2 : x.a ⟨1, hn1⟩ ≤ x.maxValue := le_maxValue_a x ⟨1, hn1⟩
      omega
    -- pc 0: the constant block (identical to `prelimProg`'s)
    have hd0 : aliasProg.getD 0 Instr.reject = Instr.one 6 := rfl
    rw [exec_one_step (S := 20) (hS := by decide) hd0]
    set s1 : Nat → Nat := up (inF x) 6 1 with hs1
    have hf1 : ∀ q, s1 q < 2 ^ w := upFit hfit0 (v := 1) b1
    have hd1 : aliasProg.getD 1 Instr.reject = Instr.add 5 6 6 := rfl
    rw [exec_add_step (S := 19) (hS := by decide) hd1]
    have hv1 : s1 6 + s1 6 = 2 := by rw [show s1 6 = 1 from up_eq _ _ _]
    rw [hv1]
    set s2 : Nat → Nat := up s1 5 2 with hs2
    have hf2 : ∀ q, s2 q < 2 ^ w := upFit hf1 (v := 2) b2
    have hd2 : aliasProg.getD 2 Instr.reject = Instr.add 4 5 6 := rfl
    rw [exec_add_step (S := 18) (hS := by decide) hd2]
    have e25 : s2 5 = 2 := up_eq _ _ _
    have e26 : s2 6 = 1 := by
      rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]; exact up_eq _ _ _
    have hv2 : s2 5 + s2 6 = 3 := by rw [e25, e26]
    rw [hv2]
    set s3 : Nat → Nat := up s2 4 3 with hs3
    have hf3 : ∀ q, s3 q < 2 ^ w := upFit hf2 (v := 3) b3
    have hd3 : aliasProg.getD 3 Instr.reject = Instr.add 3 4 4 := rfl
    rw [exec_add_step (S := 17) (hS := by decide) hd3]
    have hv3 : s3 4 + s3 4 = 6 := by rw [show s3 4 = 3 from up_eq _ _ _]
    rw [hv3]
    set s4 : Nat → Nat := up s3 3 6 with hs4
    have hf4 : ∀ q, s4 q < 2 ^ w := upFit hf3 (v := 6) b6
    -- pc 4: the gate, passed (n ≥ 6)
    have hd4 : aliasProg.getD 4 Instr.reject = Instr.blt 0 3 19 := rfl
    have v40 : s4 0 = n := by
      rw [hs4]; rw [up_ne (by decide : (0 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (0 : Nat) ≠ 6)]
      exact inF_zero x
    have v43 : s4 3 = 6 := up_eq _ _ _
    rw [exec_blt_ge_step (S := 16) (hS := by decide) hd4 hf4 (by rw [v40, v43]; omega)]
    -- pc 5: the cursor 2n
    have hd5 : aliasProg.getD 5 Instr.reject = Instr.add 0 0 0 := rfl
    rw [exec_add_step (S := 15) (hS := by decide) hd5]
    have hv5 : s4 0 + s4 0 = 2 * n := by rw [v40]; omega
    rw [hv5]
    set s5 : Nat → Nat := up s4 0 (2 * n) with hs5
    have hf5 : ∀ q, s5 q < 2 ^ w := upFit hf4 (v := 2 * n) h2n
    -- pc 6: save a₁ at 2n
    have hd6 : aliasProg.getD 6 Instr.reject = Instr.store 0 1 := rfl
    have v50 : s5 0 = 2 * n := up_eq _ _ _
    have v51 : s5 1 = x.a ⟨0, hn0⟩ := by
      rw [hs5]; rw [up_ne (by decide : (1 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (1 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (1 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (1 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (1 : Nat) ≠ 6)]
      exact ha1v
    rw [exec_store_step (S := 14) (hS := by decide) hd6 hf5]
    rw [v50, v51]
    set s6 : Nat → Nat := up s5 (2 * n) (x.a ⟨0, hn0⟩) with hs6
    have hf6 : ∀ q, s6 q < 2 ^ w := upFit hf5 (v := x.a ⟨0, hn0⟩) ha1
    -- pc 7: the second cursor 2n+1, from the literal 1 still in cell 6
    have hd7 : aliasProg.getD 7 Instr.reject = Instr.add 5 0 6 := rfl
    have v60 : s6 0 = 2 * n := by
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]; exact v50
    have v66 : s6 6 = 1 := by
      rw [hs6]; rw [up_ne (by omega : (6 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (6 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (6 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (6 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]
      rw [hs1]; exact up_eq _ _ _
    rw [exec_add_step (S := 13) (hS := by decide) hd7]
    have hv7 : s6 0 + s6 6 = 2 * n + 1 := by rw [v60, v66]
    rw [hv7]
    set s7 : Nat → Nat := up s6 5 (2 * n + 1) with hs7
    have hf7 : ∀ q, s7 q < 2 ^ w := upFit hf6 (v := 2 * n + 1) h2n1
    -- pc 8: save a₂ at 2n+1, before cell 2 is clobbered
    have hd8 : aliasProg.getD 8 Instr.reject = Instr.store 5 2 := rfl
    have v75 : s7 5 = 2 * n + 1 := up_eq _ _ _
    have v72 : s7 2 = x.a ⟨1, hn1⟩ := by
      rw [hs7]; rw [up_ne (by decide : (2 : Nat) ≠ 5)]
      rw [hs6]; rw [up_ne (by omega : (2 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (2 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (2 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (2 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (2 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (2 : Nat) ≠ 6)]
      exact ha2v
    rw [exec_store_step (S := 12) (hS := by decide) hd8 hf7]
    rw [v75, v72]
    set s8 : Nat → Nat := up s7 (2 * n + 1) (x.a ⟨1, hn1⟩) with hs8
    have hf8 : ∀ q, s8 q < 2 ^ w := upFit hf7 (v := x.a ⟨1, hn1⟩) ha2
    -- pc 9
    have hd9 : aliasProg.getD 9 Instr.reject = Instr.one 1 := rfl
    rw [exec_one_step (S := 11) (hS := by decide) hd9]
    set s9 : Nat → Nat := up s8 1 1 with hs9
    have hf9 : ∀ q, s9 q < 2 ^ w := upFit hf8 (v := 1) b1
    -- pc 10
    have hd10 : aliasProg.getD 10 Instr.reject = Instr.shr 2 0 1 := rfl
    have v90 : s9 0 = 2 * n := by
      rw [hs9]; rw [up_ne (by decide : (0 : Nat) ≠ 1)]
      rw [hs8]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]
      rw [hs5]; exact up_eq _ _ _
    have v91 : s9 1 = 1 := up_eq _ _ _
    rw [exec_shr_step (S := 10) (hS := by decide) hd10 hf9]
    have hv10 : s9 0 / 2 ^ s9 1 = n := by
      rw [v90, v91, show (2 : Nat) ^ 1 = 2 from by norm_num, Nat.mul_comm]
      exact Nat.mul_div_cancel n (by norm_num)
    rw [hv10]
    set s10 : Nat → Nat := up s9 2 n with hs10
    have hf10 : ∀ q, s10 q < 2 ^ w := upFit hf9 (v := n) hnv
    -- pc 11
    have hd11 : aliasProg.getD 11 Instr.reject = Instr.add 3 2 1 := rfl
    have v101 : s10 1 = 1 := by
      rw [hs10]; rw [up_ne (by decide : (1 : Nat) ≠ 2)]; exact v91
    rw [exec_add_step (S := 9) (hS := by decide) hd11]
    have hv11 : s10 2 + s10 1 = n + 1 := by
      rw [show s10 2 = n from up_eq _ _ _, v101]
    rw [hv11]
    set s11 : Nat → Nat := up s10 3 (n + 1) with hs11
    have hf11 : ∀ q, s11 q < 2 ^ w := upFit hf10 (v := n + 1) hnp1
    -- pc 12: [4] := t
    have hd12 : aliasProg.getD 12 Instr.reject = Instr.load 4 3 := rfl
    have v113 : s11 3 = n + 1 := up_eq _ _ _
    have v11t : s11 (n + 1) = x.t := by
      rw [hs11]; rw [up_ne (by omega : n + 1 ≠ 3)]
      rw [hs10]; rw [up_ne (by omega : n + 1 ≠ 2)]
      rw [hs9]; rw [up_ne (by omega : n + 1 ≠ 1)]
      rw [hs8]; rw [up_ne (by omega : n + 1 ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by omega : n + 1 ≠ 5)]
      rw [hs6]; rw [up_ne (by omega : n + 1 ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by omega : n + 1 ≠ 0)]
      rw [hs4]; rw [up_ne (by omega : n + 1 ≠ 3)]
      rw [hs3]; rw [up_ne (by omega : n + 1 ≠ 4)]
      rw [hs2]; rw [up_ne (by omega : n + 1 ≠ 5)]
      rw [hs1]; rw [up_ne (by omega : n + 1 ≠ 6)]
      exact inF_t x
    rw [exec_load_step (S := 8) (hS := by decide) hd12 hf11]
    rw [v113, v11t]
    set s12 : Nat → Nat := up s11 4 x.t with hs12
    have hf12 : ∀ q, s12 q < 2 ^ w := upFit hf11 (v := x.t) htv
    -- pc 13: [6] := a₁ (read back from the saved cursor cell)
    have hd13 : aliasProg.getD 13 Instr.reject = Instr.load 6 0 := rfl
    have v120 : s12 0 = 2 * n := by
      rw [hs12]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs11]; rw [up_ne (by decide : (0 : Nat) ≠ 3)]
      rw [hs10]; rw [up_ne (by decide : (0 : Nat) ≠ 2)]
      rw [hs9]; rw [up_ne (by decide : (0 : Nat) ≠ 1)]
      rw [hs8]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]
      rw [hs5]; exact up_eq _ _ _
    have v122n : s12 (2 * n) = x.a ⟨0, hn0⟩ := by
      rw [hs12]; rw [up_ne (by omega : 2 * n ≠ 4)]
      rw [hs11]; rw [up_ne (by omega : 2 * n ≠ 3)]
      rw [hs10]; rw [up_ne (by omega : 2 * n ≠ 2)]
      rw [hs9]; rw [up_ne (by omega : 2 * n ≠ 1)]
      rw [hs8]; rw [up_ne (by omega : 2 * n ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by omega : 2 * n ≠ 5)]
      rw [hs6]; exact up_eq _ _ _
    rw [exec_load_step (S := 7) (hS := by decide) hd13 hf12]
    rw [v120, v122n]
    set s13 : Nat → Nat := up s12 6 (x.a ⟨0, hn0⟩) with hs13
    have hf13 : ∀ q, s13 q < 2 ^ w := upFit hf12 (v := x.a ⟨0, hn0⟩) ha1
    -- pc 14: [5] := a₂, by indirection through the cursor cell itself
    have hd14 : aliasProg.getD 14 Instr.reject = Instr.load 5 5 := rfl
    have v135 : s13 5 = 2 * n + 1 := by
      rw [hs13]; rw [up_ne (by decide : (5 : Nat) ≠ 6)]
      rw [hs12]; rw [up_ne (by decide : (5 : Nat) ≠ 4)]
      rw [hs11]; rw [up_ne (by decide : (5 : Nat) ≠ 3)]
      rw [hs10]; rw [up_ne (by decide : (5 : Nat) ≠ 2)]
      rw [hs9]; rw [up_ne (by decide : (5 : Nat) ≠ 1)]
      rw [hs8]; rw [up_ne (by omega : (5 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; exact up_eq _ _ _
    have v13a2 : s13 (2 * n + 1) = x.a ⟨1, hn1⟩ := by
      rw [hs13]; rw [up_ne (by omega : 2 * n + 1 ≠ 6)]
      rw [hs12]; rw [up_ne (by omega : 2 * n + 1 ≠ 4)]
      rw [hs11]; rw [up_ne (by omega : 2 * n + 1 ≠ 3)]
      rw [hs10]; rw [up_ne (by omega : 2 * n + 1 ≠ 2)]
      rw [hs9]; rw [up_ne (by omega : 2 * n + 1 ≠ 1)]
      rw [hs8]; exact up_eq _ _ _
    rw [exec_load_step (S := 6) (hS := by decide) hd14 hf13]
    rw [v135, v13a2]
    set s14 : Nat → Nat := up s13 5 (x.a ⟨1, hn1⟩) with hs14
    have hf14 : ∀ q, s14 q < 2 ^ w := upFit hf13 (v := x.a ⟨1, hn1⟩) ha2
    -- pc 15: [5] := a₁ + a₂
    have hd15 : aliasProg.getD 15 Instr.reject = Instr.add 5 6 5 := rfl
    have v146 : s14 6 = x.a ⟨0, hn0⟩ := by
      rw [hs14]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]; exact up_eq _ _ _
    have v145 : s14 5 = x.a ⟨1, hn1⟩ := up_eq _ _ _
    rw [exec_add_step (S := 5) (hS := by decide) hd15]
    rw [v146, v145]
    set s15 : Nat → Nat := up s14 5 (x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩) with hs15
    have hf15 : ∀ q, s15 q < 2 ^ w :=
      upFit hf14 (v := x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩) hsum
    have w4 : s15 4 = x.t := by
      rw [hs15]; rw [up_ne (by decide : (4 : Nat) ≠ 5)]
      rw [hs14]; rw [up_ne (by decide : (4 : Nat) ≠ 5)]
      rw [hs13]; rw [up_ne (by decide : (4 : Nat) ≠ 6)]
      rw [hs12]; exact up_eq _ _ _
    have w5 : s15 5 = x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ := up_eq _ _ _
    -- the decision: three cases on the trichotomy, exactly as the two `blt`s cut it
    rcases lt_trichotomy (x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩) x.t with hlt | heq | hgt
    · -- the witness is too small: `t < a₁+a₂` fails, then `a₁+a₂ < t` jumps to FAIL
      have hd16 : aliasProg.getD 16 Instr.reject = Instr.blt 4 5 19 := rfl
      rw [exec_blt_ge_step (S := 4) (hS := by decide) hd16 hf15 (by rw [w4, w5]; omega)]
      have hd17 : aliasProg.getD 17 Instr.reject = Instr.blt 5 4 19 := rfl
      rw [exec_blt_lt_step (S := 3) (hS := by decide) hd17 hf15 (by rw [w4, w5]; exact hlt)]
      have hd19 : aliasProg.getD 19 Instr.reject = Instr.reject := rfl
      rw [exec_reject_step (S := 2) (hS := by decide) hd19]
      rw [aliasYes_eq_false_of x h10 (by intro hc; omega)]
    · -- equality: both `blt`s fall through to `accept`
      have hd16 : aliasProg.getD 16 Instr.reject = Instr.blt 4 5 19 := rfl
      rw [exec_blt_ge_step (S := 4) (hS := by decide) hd16 hf15 (by rw [w4, w5]; omega)]
      have hd17 : aliasProg.getD 17 Instr.reject = Instr.blt 5 4 19 := rfl
      rw [exec_blt_ge_step (S := 3) (hS := by decide) hd17 hf15 (by rw [w4, w5]; omega)]
      have hd18 : aliasProg.getD 18 Instr.reject = Instr.accept := rfl
      rw [exec_accept_step (S := 2) (hS := by decide) hd18]
      rw [aliasYes_eq_true x h10 heq]
    · -- the witness is too large: `t < a₁+a₂` jumps straight to FAIL
      have hd16 : aliasProg.getD 16 Instr.reject = Instr.blt 4 5 19 := rfl
      rw [exec_blt_lt_step (S := 4) (hS := by decide) hd16 hf15 (by rw [w4, w5]; exact hgt)]
      have hd19 : aliasProg.getD 19 Instr.reject = Instr.reject := rfl
      rw [exec_reject_step (S := 3) (hS := by decide) hd19]
      rw [aliasYes_eq_false_of x h10 (by intro hc; omega)]
  · -- below the gate: the window is not addressable, the phase FAILs at pc 4
    have b1 : (1 : Nat) < 2 ^ w := by omega
    have b2 : (2 : Nat) < 2 ^ w := by omega
    have b3 : (3 : Nat) < 2 ^ w := by omega
    have b6 : (6 : Nat) < 2 ^ w := by omega
    have hd0 : aliasProg.getD 0 Instr.reject = Instr.one 6 := rfl
    rw [exec_one_step (S := 20) (hS := by decide) hd0]
    set s1 : Nat → Nat := up (inF x) 6 1 with hs1
    have hf1 : ∀ q, s1 q < 2 ^ w := upFit hfit0 (v := 1) b1
    have hd1 : aliasProg.getD 1 Instr.reject = Instr.add 5 6 6 := rfl
    rw [exec_add_step (S := 19) (hS := by decide) hd1]
    have hv1 : s1 6 + s1 6 = 2 := by rw [show s1 6 = 1 from up_eq _ _ _]
    rw [hv1]
    set s2 : Nat → Nat := up s1 5 2 with hs2
    have hf2 : ∀ q, s2 q < 2 ^ w := upFit hf1 (v := 2) b2
    have hd2 : aliasProg.getD 2 Instr.reject = Instr.add 4 5 6 := rfl
    rw [exec_add_step (S := 18) (hS := by decide) hd2]
    have hv2 : s2 5 + s2 6 = 3 := by
      rw [show s2 5 = 2 from up_eq _ _ _]
      rw [show s2 6 = 1 from by
        rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]; exact up_eq _ _ _]
    rw [hv2]
    set s3 : Nat → Nat := up s2 4 3 with hs3
    have hf3 : ∀ q, s3 q < 2 ^ w := upFit hf2 (v := 3) b3
    have hd3 : aliasProg.getD 3 Instr.reject = Instr.add 3 4 4 := rfl
    rw [exec_add_step (S := 17) (hS := by decide) hd3]
    have hv3 : s3 4 + s3 4 = 6 := by rw [show s3 4 = 3 from up_eq _ _ _]
    rw [hv3]
    set s4 : Nat → Nat := up s3 3 6 with hs4
    have hf4 : ∀ q, s4 q < 2 ^ w := upFit hf3 (v := 6) b6
    have hd4 : aliasProg.getD 4 Instr.reject = Instr.blt 0 3 19 := rfl
    have v40 : s4 0 = n := by
      rw [hs4]; rw [up_ne (by decide : (0 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (0 : Nat) ≠ 6)]
      exact inF_zero x
    have v43 : s4 3 = 6 := up_eq _ _ _
    rw [exec_blt_lt_step (S := 16) (hS := by decide) hd4 hf4 (by rw [v40, v43]; omega)]
    have hd19 : aliasProg.getD 19 Instr.reject = Instr.reject := rfl
    rw [exec_reject_step (S := 15) (hS := by decide) hd19]
    rw [aliasYes_eq_false x h10]

/-! ### Layer 6′ — the field shape, the convention's divergence, and the leaf

`Routines.alias_agrees` is

```
run aliasProg x ρ (aliasCost n x) = some (aliasA n x (fun r => (ρ r).toNat)).isSome
```

— already an equation between `Option Bool`s, with **no wrapper**.  Contrast
`Routines.prelim_agrees`, whose right-hand side is `some (failToNo (prelim …))`
under a `map failToNo (Option.bind …)` that Lean elaborates from the field's
`Option.map`, and which therefore needed `map_failToNo_bind_some` before it said
anything (`KapilaPrelim`, layer 6).  The alias field needs no such peel: the
`isSome` convention is `Option`-free *by construction*.  `alias_run_of_field`
below is the field, unchanged, which is the whole of the "bridge" — the shape
does not fight.

What is *not* interchangeable is the convention itself.  `isSome` and `failToNo`
agree on `none`, and disagree on `some false` — `failToNo` reads it as NO,
`isSome` as «the phase succeeded».  `isSome_ne_failToNo` is that fact, and it is
the reason the phase's field *must* be `isSome`: the alias phase does not decide
YES/NO, it succeeds or fails, so its verdict carries no decision and no
`failToNo` reading of it would be faithful.  The consequence is the leaf: this
field discharges `LeafAnone` (failure ⟹ NO), not `LeafP` (decision ⟹ that
decision). -/

/-- The alias field, peeled to nothing: it *is* the `Option`-free halt equation. -/
theorem alias_run_of_field (R : Routines) (n : Nat) (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) :
    run R.aliasProg x ρ (R.aliasCost n x)
      = some (R.aliasA n x (fun r => (ρ r).toNat)).isSome :=
  R.alias_agrees n x ρ

/-- **The two conventions are not interchangeable**: on `Option Bool` they
disagree at `some false`.  A phase whose `some` payload is not a decision — and
the alias phase's payload is an estimate list — cannot be read through
`failToNo` without inventing a decision it never made. -/
theorem isSome_ne_failToNo :
    ¬ (∀ o : Option Bool, o.isSome = failToNo o) := by
  intro hall
  have h := hall (some false)
  simp [failToNo] at h

/-- `isSome` forgets the payload: two different estimate lists are
indistinguishable to the segment's verdict.  This is exactly why the field can
discharge `LeafAnone` (which needs only «failed») and cannot discharge
`LeafTest` (which needs the lists themselves). -/
theorem isSome_forgets_payload {α : Type} (a b : α) :
    (some a : Option α).isSome = (some b).isSome := rfl

/-- The agreement for **this** program and spec, in the field's exact shape — no
wrapper, no `Option` ambiguity, nothing to peel. -/
theorem alias_agrees_spec {n : Nat} (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (ω : Draws) :
    run aliasProg x ρ (aliasCost n x) = some ((aliasSpec n x ω).isSome) :=
  alias_run x ρ ω

/-- **`LeafAnone`'s discharge.**  On the guard's complement, if `R.cost` collapses
to `R.aliasCost` (the segment is the whole program there, or the earlier segments
are free), then `R.alias_agrees` *is* `LeafAnone R R.aliasProg`: the phase's
`none` is read as the program's NO, which is §7's «If it fails, return NO» and
nothing else.  The `FAIL → NO` control-flow fact stays `LeafAnone`'s — a segment
verdict can only say «succeeded», never «the program answers NO».

This is the second of the four segment obligations in `agrees_main_iff_leaves`;
`LeafP` was the first (`LeafP_of_prelim_agrees`, `KapilaPrelim`). -/
theorem LeafAnone_of_alias_agrees (R : Routines)
    (hcost : ∀ (n : Nat) (x : Instance n), R.cost n x = R.aliasCost n x) :
    LeafAnone R R.aliasProg := by
  intro n x ρ _hf _hp ha
  rw [hcost n x, R.alias_agrees n x ρ, ha]
  rfl

/-- The same discharge with the strong equation supplied directly — the form a
`Routines` builder proves before packaging it as the field (cf.
`LeafP_of_prelim_run`). -/
theorem LeafAnone_of_alias_run (R : Routines)
    (hcost : ∀ (n : Nat) (x : Instance n), R.cost n x = R.aliasCost n x)
    (hrun : ∀ (n : Nat) (x : Instance n) (ρ : Nat → BitVec (wordLength n x.bits)),
      run R.aliasProg x ρ (R.aliasCost n x)
        = some (R.aliasA n x (fun r => (ρ r).toNat)).isSome) :
    LeafAnone R R.aliasProg := by
  intro n x ρ _hf _hp ha
  rw [hcost n x, hrun n x ρ, ha]
  rfl

/-! ### The named residual, stated where the next mind will find it

What this file does **not** claim, in order of what it would cost to close:

1. **The enumeration.**  The paper's alias phase extracts the class sums of every
   alias class of every target by running `T = n⁷2^{e_n}⌈1/Ŝ⌉` trials.  The leg
   above certifies the *pair* witness and FAILs otherwise, so its FAIL region is
   far wider than the paper's; the paper's is `o(1)`, and that difference is what
   the union bound (`cor_A6_per_alias`, `o7_union_le`) spends.  Closing it means
   a backward jump — the first loop in this calculus, and a cost accounting for
   it — not a longer proof of the same equation.
2. **The multi-word accumulator.**  The estimates `Â_s` are `ℚ` values carrying
   `n²` fractional bits while the word is `w = O(n + b)`.  `aliasProg` never
   computes them: its two reads (`t`, `a₁ + a₂`) are single words, by
   `inF_lt` and `2·maxValue < 2^w`.  The expansion into word operations is
   absorbed (`withinEnvelope_wordop_absorb`) but the *layout* of a `ℚ`
   accumulator is not written.
3. **`LeafTest`'s use of the estimates.**  `isSome` forgets the payload, so the
   lists the phase leaves behind are not certified by this field; `LeafTest`
   needs the payload convention (`rowTest_eq_of_rules` gives it the three loop
   rules, but nothing yet gives it the lists).
4. **The failing draws' probability.**  `aliasSpec` ignores `ω`: the leg is
   deterministic.  The paper's phase is randomized, and its success probability
   is what makes the two-thirds accounting work; nothing here touches that.

Statement.lean's hashes are untouched (`3dc6567e…34aa`): this module adds names
only. -/

end SubsetSumL25.Row
