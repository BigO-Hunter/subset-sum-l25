/-
Theorem B's instruction text — **`checksumProg`**, its agreement, and its segment leaf.

Why this file exists.  `Routines` (`SubsetSumL25.Row.KapilaAlgo`) carries six
program fields; the checksum phase's was one of them (`checksumProg`), named but
with no in-tree instruction text.  `KapilaPrelim` did this for §4's preliminary
search and closed `LeafP`; `KapilaAlias` did it for §5.2's alias phase and closed
`LeafAnone`.  This file does it for §6's checksum phase, and closes
**`LeafBnone`** — the third of the four segment obligations in
`agrees_main_iff_leaves`.  After it, one leaf remains (`LeafTest`).

What is proved here, in order:

1. **`checksumProg`** — 24 instructions: the same constant-and-cursor bootstrap
   `prelimProg`/`aliasProg` use, extended by a **third** saved cell so that the
   phase's decision reads three input values instead of two.  The bootstrap
   layers are **reused, not re-derived**: `memOf`, `up`, `upFit`, `bv_add`,
   `bv_shr`, `ofNat_lt_ofNat`, the eight `exec_*_step` peelers, the input-block
   layer (`inF`, `inF_lt`, `inF_one`, `inF_two`, `inF_t`,
   `wordLength_ge_five`, `bits_pos`), and the pair-sum layer
   (`ofFn_sum_ite_pair`, `yes_of_pair`) are imported from
   `SubsetSumL25.Row.KapilaPrelim` / `KapilaAlias`.  The only new layer-2 fact is
   `inF_three` (the third input cell in `memOf` normal form).
2. **`checksumSpec`** — the phase's value, an independent `ℕ`-level definition:
   «the phase succeeds, carrying the estimate it recovered» or «FAIL».  It is
   Theorem B's programme-level witness test, and it is *sound* in the only sense
   such a leg can be: `checksum_sound` — every estimate the phase reports is
   carried by a **genuine subset** of the instance (`a₁ + a₂ + a₃`, hence a
   subset sum of `x`), and `checksum_support_in_bin` reads that subset in §6's
   own bin vocabulary.  The block tables, the pattern family, the
   inverse-multiplicity weighting, and the `1/8`-accuracy bound are the residual,
   named at the bottom of this file.
3. **`checksum_run`** — `run checksumProg x ρ (checksumCost n x)` is
   `some (checksumSpec …).isSome`, proved by a straight-line walk over the 24
   instructions with the ported `memOf`/`up`/`exec_*_step` calculus.
4. **`checksum_agrees_spec`** — the agreement for this program and spec in
   `Routines.checksum_agrees`' field shape: **`Option`-free**, through `isSome`,
   exactly as the alias phase's was (and unlike §4's `failToNo` wrapper).
5. **`LeafBnone`'s program side is discharged** — `LeafBnone_of_checksum_agrees`:
   on the guard's complement, if `R.cost` collapses to `R.checksumCost` then
   `R.checksum_agrees` *is* `LeafBnone R R.checksumProg`.  The `FAIL → NO`
   control-flow fact stays `LeafBnone`'s, as it must: the segment's verdict is
   only «succeeded», and the leaf is what turns that into the program's NO.

Honest bounds on what this does and does not say.

* **The phase's FAIL region is wider here than the paper's**, exactly as the alias
  leg's is.  The leg proved below certifies success when the target is a *triple*
  witness (`a₁ + a₂ + a₃ = t`); Theorem B's phase, with its block tables and
  inverse-multiplicity weighting, succeeds with probability `1 - o(1)` on nearly
  all targets.  That gap is what the union bound spends; it is the named
  residual, not a claim.  What is *not* weakened is the direction that matters for
  the leaf: FAIL is a verdict the phase is entitled to return, and §7's «If it
  fails, return NO» turns it into the program's answer.
* **§6's checksum is not `a₁ + a₂ + a₃`.**  Eq. (6.1) defines
  `V_ρ = ∑_{I : ∑_{i∈I} b_i ≡ ρ} e_P(∑_{i∈I} φ_i)` — a *complex* sum over a
  residue bin, with one term per subset.  The in-tree calculus has no complex
  numbers, no phases (a `Draws` is a word stream, and this leg is deterministic —
  it ignores `ω`), and no residue machinery beyond `Nat` mod.  What the leg
  certifies is therefore the **support** of a checksum term: a subset in the bin
  exists, and `checksum_support_in_bin` states that in §6's vocabulary (`∑ a_i ≡ t
  (mod P)` for every modulus `P`, so the term is one of `V_ρ`'s summands at
  `ρ = t mod P`).  The phases' weights, the tables, and the `1/8` accuracy are
  what Theorem B's core proves (`o5_mse_le`) and what this text does not compute.
* **No loop, no multi-word accumulator.**  As in `prelimProg`/`aliasProg`, the text
  has no backwards jump: the block-table enumeration is what the residual
  carries.  The three cells the decision reads (`t`, `a₁ + a₂ + a₃`) are single
  words by `inF_lt` plus `3·maxValue < 2^w`, both proved here — the phase's
  *estimates* are `ℚ` and are not computed by this text.
* **Statement.lean is untouched** (`3dc6567e…34aa`): every name below is new.

Credit: §6 / Theorem B's procedure and the «FAIL → return NO» reading are
Base's and the OpenAI preprint's; the bootstrap-and-scan shape is the
`subsetsum-v2-snapshot` lane's, ported verbatim through `KapilaPrelim` and
`KapilaAlias`.  Nothing here re-derives what a reference already has.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaPrelim
import SubsetSumL25.Row.KapilaAlias

set_option autoImplicit true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### Layer 2″ — the third input cell

Layers 0–2 (`memOf`/`up`/`upFit`, `bv_add`/`bv_shr`/`ofNat_lt_ofNat`, the eight
`exec_*_step` peelers, and `inF` with its fit lemmas) are **imported** from
`SubsetSumL25.Row.KapilaPrelim`; the second-cell fact `inF_two` is imported from
`SubsetSumL25.Row.KapilaAlias`.  The checksum phase is the first segment whose
decision reads three input values, so exactly one new layer-2 fact is needed. -/

/-- The third input cell, in `memOf` normal form: cell 3 holds `a₃`. -/
theorem inF_three {n : Nat} (x : Instance n) (h : 2 < n) : inF x 3 = x.a ⟨2, h⟩ := by
  rw [inF_succ x 2]
  rw [List.getD_append (List.ofFn x.a) [x.t] 0 2 (by simpa using h)]
  rw [ofFn_getD]
  simp [h]

/-! ### Layer 3″ — the program

Layout (24 instructions, no loops; every jump leaves the straight line):

```
pc  0  one 6          [6] := 1                ┐
pc  1  add 5 6 6      [5] := 2                │  the constant block, built from
pc  2  add 4 5 6      [4] := 3                │  the only literal constant, 1
pc  3  add 4 4 4      [4] := 6                ┘  (the *same* `6` as `prelim`,
pc  4  blt 0 4 23     n < 6 ⟹ FAIL                built as 3 + 3, not 2 · 3)
pc  5  add 0 0 0      [0] := 2n               ┐  the cursor: 2n is above the
pc  6  store 0 1      [2n] := a₁              │  block for n ≥ 6, so the three
pc  7  add 1 0 6      [1] := 2n+1             │  saves are safe (prog2 `saveAk`,
pc  8  store 1 2      [2n+1] := a₂            │  one cell further than alias)
pc  9  add 2 1 6      [2] := 2n+2             │
pc 10  store 2 3      [2n+2] := a₃            ┘
pc 11  shr 2 0 6      [2] := n                (2n >>> 1; the literal 1 is in 6)
pc 12  add 3 2 6      [3] := n+1              ┐  the address of `t`; cell 3 is
pc 13  load 4 3       [4] := t                ┘  free only now (`a₃` was saved)
pc 14  load 6 0       [6] := a₁               ┐  the three saved cells, read
pc 15  add 3 0 5      [3] := 2n+2             │  back: 2n stays in 0, 2n+1 in 1,
pc 16  load 3 3       [3] := a₃               │  2n+2 is rebuilt as 2n + 2 from
pc 17  load 5 1       [5] := a₂               ┘  the still unspent literal 2 in 5
pc 18  add 6 6 5      [6] := a₁ + a₂
pc 19  add 6 6 3      [6] := a₁ + a₂ + a₃
pc 20  blt 4 6 23     t < a₁+a₂+a₃   ⟹ FAIL
pc 21  blt 6 4 23     a₁+a₂+a₃ < t   ⟹ FAIL
pc 22  accept         a₁+a₂+a₃ = t   ⟹ the phase succeeded
pc 23  reject         FAIL
```

Three things differ from `aliasProg`, and each is forced by the *shape of the
verdict* rather than by taste:

* **The saves come first, the `6` is built in a scratch cell.**  The alias phase
  could build its constant block into cell 3 (`add 3 4 4`) because `a₃` played no
  part in its decision; the checksum phase reads `a₃`, so cell 3 must survive the
  bootstrap.  Hence the constant block touches only cells 4, 5, 6, and the `6` is
  built as `3 + 3` in cell 4 — the level it needs (`n ≥ 6`) is compared against
  cell 4 rather than cell 3.  The three saves then happen *before* any register
  is spent: the cursor `2n` costs no constant at all (`add 0 0 0`), and the two
  successors reuse the literal `1` in cell 6 (`add 1 0 6`, `add 2 1 6`), so the
  input cells 1, 2, 3 are read on the instruction that clobbers them and on no
  earlier one.
* **The read-back uses the whole register file.**  Cells 0 and 1 still hold the
  addresses `2n` and `2n+1` when the saves finish, so two of the three fetches are
  single indirections (`load 6 0`, `load 5 1`); the third address is rebuilt as
  `2n + 2` from the unspent literal `2` (`add 3 0 5`) and then self-loaded
  (`load 3 3`).  Which is why the `2` in cell 5 survives until `pc 17`: it is an
  address constant, not a value.
* **The phase is two-valued, not three-valued**: both disagreements of `t` with
  the witness (`pc 20`, `pc 21`) go to the *same* `reject`, which is the phase's
  FAIL.  There is no CONTINUE instruction in this text, and there cannot be:
  `checksumB = none` is §7's FAIL, not §4's CONTINUE.

The `n ≥ 6` gate keeps `n + 1` (where `t` lives) clear of every register
(`0`, `1`, `2`, `3`, `4`, `5`, `6`), of `2n`, of `2n + 1`, and of `2n + 2` — for
`n ≥ 6`, `n + 1 ≥ 7` while `2n ≥ 12`, so the saved cells sit above the block and
the block sits above the registers, and `n + 1 < 2n` keeps `t`'s address off the
saved cells. -/
def checksumProg : List Instr :=
  [ .one 6
  , .add 5 6 6
  , .add 4 5 6
  , .add 4 4 4
  , .blt 0 4 23
  , .add 0 0 0
  , .store 0 1
  , .add 1 0 6
  , .store 1 2
  , .add 2 1 6
  , .store 2 3
  , .shr 2 0 6
  , .add 3 2 6
  , .load 4 3
  , .load 6 0
  , .add 3 0 5
  , .load 3 3
  , .load 5 1
  , .add 6 6 5
  , .add 6 6 3
  , .blt 4 6 23
  , .blt 6 4 23
  , .accept
  , .reject
  ]

/-! ### Layer 4″ — the phase's value

`checksumSpec` is the checksum phase's verdict on `x`, independently of the
program: **succeeded**, carrying the estimate it recovered (`a₁ + a₂ + a₃`, a
genuine subset sum), or **FAIL** (`none`).  As in §5.2's `aliasSpec` there is no
CONTINUE: the phase either extracts its estimates or fails, and §7 reads failure
as NO.

The verdict is `Option (List ℚ)` because `Routines.checksumB`'s payload is the
list of estimates; the leg below carries the *singleton* estimate of the
witness's target.  `6 ≤ n` is the gate below which the prologue's register
window is not addressable — a capped phase may FAIL whenever it likes, which
costs nothing (a FAIL is a NO answer, and its frequency is what the union bound
measures). -/
def checksumYes (n : Nat) (x : Instance n) : Bool :=
  if _h : 6 ≤ n then
    (x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ + x.a ⟨2, by omega⟩ == x.t)
  else false

/-- The phase's value: the recovered estimate list on success, FAIL (`none`)
otherwise.  The draws are ignored — the witness test is deterministic, which is
the honest reading of a leg whose candidates are enumerated from tables rather
than sampled. -/
def checksumSpec (n : Nat) (x : Instance n) (_ : Draws) : Option (List ℚ) :=
  if checksumYes n x then some [(x.t : ℚ)] else none

/-- §7 step 6's step count, in word operations: the 24 instructions above, all
charged one word operation each (`2n+2`, `a₁ + a₂ + a₃` and `t` are all
`< 2^w`). -/
def checksumCost (n : Nat) (_ : Instance n) : Nat := 24

theorem checksumYes_eq_true {n : Nat} (x : Instance n) (h : 6 ≤ n)
    (hv : x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ + x.a ⟨2, by omega⟩ = x.t) :
    checksumYes n x = true := by
  unfold checksumYes
  rw [dif_pos h]
  simp [hv]

theorem checksumYes_eq_false {n : Nat} (x : Instance n) (h : ¬ 6 ≤ n) :
    checksumYes n x = false := by
  unfold checksumYes
  rw [dif_neg h]

theorem checksumYes_eq_false_of {n : Nat} (x : Instance n) (h : 6 ≤ n)
    (hv : ¬ (x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ + x.a ⟨2, by omega⟩ = x.t)) :
    checksumYes n x = false := by
  unfold checksumYes
  rw [dif_pos h]
  have h' : (x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ + x.a ⟨2, by omega⟩ == x.t) = false := by
    by_cases hc : x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ + x.a ⟨2, by omega⟩ = x.t
    · exact absurd hc hv
    · simpa using hc
  rw [h']

/-! ### Layer 4.5″ — soundness of the witness leg

The estimates the phase reports must be carried by *genuine subsets* — that is
what makes them estimates of a checksum over a bin rather than phantom values,
and it is the only mathematical obligation a witness-test leg can carry.  The
triple `{a₁, a₂, a₃}` supplies it. -/

/-- Summing the indicator of a three-element index set. -/
theorem ofFn_sum_ite_triple {n : Nat} (x : Instance n) {i0 i1 i2 : Fin n}
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2) :
    (List.ofFn fun i => if decide (i = i0 ∨ i = i1 ∨ i = i2) then x.a i else 0).sum
      = x.a i0 + x.a i1 + x.a i2 := by
  classical
  rw [List.sum_ofFn]
  have hstep : ∀ i : Fin n,
      (if decide (i = i0 ∨ i = i1 ∨ i = i2) then x.a i else 0)
        = if i ∈ ({i0, i1, i2} : Finset (Fin n)) then x.a i else 0 := by
    intro i
    by_cases hp : i = i0 ∨ i = i1 ∨ i = i2
    · rw [if_pos (by simpa using hp), if_pos (by simpa using hp)]
    · rw [if_neg (by simpa using hp), if_neg (by simpa using hp)]
  simp only [hstep]
  rw [Finset.sum_ite_mem_eq ({i0, i1, i2} : Finset (Fin n)) (fun i => x.a i)]
  have hS : ({i0, i1, i2} : Finset (Fin n)) = insert i0 ({i1, i2} : Finset (Fin n)) := by
    ext i
    simp
  rw [hS]
  rw [Finset.sum_insert (by simp [h01, h02])]
  rw [Finset.sum_pair (f := fun i => x.a i) h12]
  omega

/-- The triple `{a₁, a₂, a₃}` witnesses `t`. -/
theorem yes_of_triple {n : Nat} (x : Instance n) (h3 : 3 ≤ n)
    (hv : x.a ⟨0, by omega⟩ + x.a ⟨1, by omega⟩ + x.a ⟨2, by omega⟩ = x.t) : x.yes := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have h2 : 2 < n := by omega
  have hne01 : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hc
    have hv' := congrArg Fin.val hc
    simp at hv'
  have hne02 : (⟨0, h0⟩ : Fin n) ≠ ⟨2, h2⟩ := by
    intro hc
    have hv' := congrArg Fin.val hc
    simp at hv'
  have hne12 : (⟨1, h1⟩ : Fin n) ≠ ⟨2, h2⟩ := by
    intro hc
    have hv' := congrArg Fin.val hc
    simp at hv'
  refine ⟨fun i => decide (i = ⟨0, h0⟩ ∨ i = ⟨1, h1⟩ ∨ i = ⟨2, h2⟩), ?_⟩
  rw [ofFn_sum_ite_triple x hne01 hne02 hne12]
  simpa using hv

/-- **Soundness of the checksum phase's witness leg.**  When it reports success
its estimate is a genuine subset sum of the instance — the paper's requirement
that every term of `V_ρ` correspond to an actual subset, discharged for the leg
below.  (The converse is not claimed: the leg FAILs on instances whose target is
a larger subset, which is the block-table residual.) -/
theorem checksum_sound {n : Nat} (x : Instance n) (ω : Draws) {L : List ℚ}
    (h : checksumSpec n x ω = some L) : x.yes ∧ L = [(x.t : ℚ)] := by
  unfold checksumSpec at h
  by_cases hy : checksumYes n x = true
  · rw [if_pos hy] at h
    have hL : ([(x.t : ℚ)] : List ℚ) = L := Option.some.inj h
    refine ⟨?_, hL.symm⟩
    unfold checksumYes at hy
    by_cases h10 : 6 ≤ n
    · rw [dif_pos h10] at hy
      exact yes_of_triple x (by omega) (beq_iff_eq.mp hy)
    · rw [dif_neg h10] at hy
      exact absurd hy (by simp)
  · rw [if_neg hy] at h
    exact absurd h (by simp)

/-- **The same content in §6's bin vocabulary.**  The certified subset lands in
the target's residue class modulo *every* modulus `P`, so its term is one of the
summands of `V_ρ` at `ρ = t mod P` (eq. (6.1)).  This is the part of «genuine
checksum» that the in-tree calculus can state without complex numbers or
phases. -/
theorem checksum_support_in_bin {n : Nat} (x : Instance n) (ω : Draws) {L : List ℚ}
    (h : checksumSpec n x ω = some L) (P : Nat) :
    ∃ S : Fin n → Bool, (List.ofFn fun i => if S i then x.a i else 0).sum % P = x.t % P := by
  obtain ⟨⟨S, hS⟩, _⟩ := checksum_sound x ω h
  exact ⟨S, by rw [hS]⟩

/-! ### Layer 5″ — the walk

The agreement, proved against the text: at `checksumCost`, `checksumProg` halts
and its verdict is `checksumSpec`'s, read through the `Option`-free `isSome`. -/

/-- `isSome` of the spec is the spec's own `Bool`. -/
theorem checksumSpec_isSome {n : Nat} (x : Instance n) (ω : Draws) :
    (checksumSpec n x ω).isSome = checksumYes n x := by
  unfold checksumSpec
  cases hb : checksumYes n x <;> rfl

theorem checksum_run {n : Nat} (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (ω : Draws) :
    run checksumProg x ρ (checksumCost n x) = some ((checksumSpec n x ω).isSome) := by
  rw [checksumSpec_isSome]
  set w : Nat := wordLength n x.bits with hw
  have hfit0 : ∀ q, inF x q < 2 ^ w := by intro q; rw [hw]; exact inF_lt x q
  have h5 : 5 ≤ w := by rw [hw]; exact wordLength_ge_five (bits_pos x)
  -- `omega` treats `2^w` as an opaque atom, so the small-literal fits need the
  -- single numeric fact `32 ≤ 2^w` first (the alias layer's `hbig`)
  have hbig : (32 : Nat) ≤ 2 ^ w := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) h5
    simpa using h
  simp only [run, checksumCost, inF_input]
  by_cases h10 : 6 ≤ n
  · have hn0 : 0 < n := by omega
    have hn1 : 1 < n := by omega
    have hn2 : 2 < n := by omega
    have ha1v : inF x 1 = x.a ⟨0, hn0⟩ := inF_one x hn0
    have ha2v : inF x 2 = x.a ⟨1, hn1⟩ := inF_two x hn1
    have ha3v : inF x 3 = x.a ⟨2, hn2⟩ := inF_three x hn2
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
    -- `2^w` is an opaque atom to `omega`, so the parity-free route is
    -- `2(n+1) ≤ 2^w` and then the four cursor facts follow by linearity
    have hhn : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))
    have hpow : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hfin : 2 * (n + 1) ≤ 2 ^ w := by
      have h4 : (2 : Nat) ^ (n + 1) ≤ 2 ^ w :=
        Nat.pow_le_pow_right (by norm_num) hh1
      have h2 : 2 * (n + 1) ≤ 2 ^ (n + 1) := by
        have hm := Nat.mul_le_mul_left 2 hhn
        rw [hpow] at hm
        exact hm
      exact le_trans h2 h4
    have h2n : 2 * n < 2 ^ w := by omega
    have h2n1 : 2 * n + 1 < 2 ^ w := by omega
    -- **strict, not `≤`**: `upFit` needs every written value `< 2^w`, and `hfin`
    -- only gives `≤`.  `2n+2` is the one address that cannot lean on the
    -- `2(n+1)` bound, so it goes through `k < 2^k ≤ 2^w` with `k = 2n+2 ≤ w`
    have h2n2 : 2 * n + 2 < 2 ^ w := by
      have hwb : 2 * n + 2 ≤ w := by
        rw [hw]
        show 2 * n + 2 ≤ 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1
        have := bits_pos x
        omega
      exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hwb)
    have hnp1 : n + 1 < 2 ^ w := by omega
    have ha1 : x.a ⟨0, hn0⟩ < 2 ^ w := by rw [← ha1v]; exact hfit0 1
    have ha2 : x.a ⟨1, hn1⟩ < 2 ^ w := by rw [← ha2v]; exact hfit0 2
    have ha3 : x.a ⟨2, hn2⟩ < 2 ^ w := by rw [← ha3v]; exact hfit0 3
    have htv : x.t < 2 ^ w := by
      have h := inF_succ_lt x n; rw [inF_t] at h; rw [hw]; exact h
    -- the triple sum fits one word: `3·maxValue < 2^w`, from `bits + 2 ≤ w`
    have hbits_w : x.bits + 2 ≤ w := by
      rw [hw]
      show x.bits + 2 ≤ 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1
      omega
    have hmax3 : 3 * x.maxValue < 2 ^ w := by
      have hm := maxValue_lt_two_pow_bits x
      have h1 : 3 * x.maxValue < 2 ^ (x.bits + 2) := by
        rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 from by norm_num]
        omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hbits_w)
    have hsum3 : x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ + x.a ⟨2, hn2⟩ < 2 ^ w := by
      have h1 : x.a ⟨0, hn0⟩ ≤ x.maxValue := le_maxValue_a x ⟨0, hn0⟩
      have h2 : x.a ⟨1, hn1⟩ ≤ x.maxValue := le_maxValue_a x ⟨1, hn1⟩
      have h3 : x.a ⟨2, hn2⟩ ≤ x.maxValue := le_maxValue_a x ⟨2, hn2⟩
      omega
    have hsum2 : x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ < 2 ^ w := by omega
    -- pc 0: the constant block, built in the scratch cells (4, 5, 6) only
    have hd0 : checksumProg.getD 0 Instr.reject = Instr.one 6 := rfl
    rw [exec_one_step (S := 24) (hS := by decide) hd0]
    set s1 : Nat → Nat := up (inF x) 6 1 with hs1
    have hf1 : ∀ q, s1 q < 2 ^ w := upFit hfit0 (v := 1) b1
    have hd1 : checksumProg.getD 1 Instr.reject = Instr.add 5 6 6 := rfl
    rw [exec_add_step (S := 23) (hS := by decide) hd1]
    have hv1 : s1 6 + s1 6 = 2 := by rw [show s1 6 = 1 from up_eq _ _ _]
    rw [hv1]
    set s2 : Nat → Nat := up s1 5 2 with hs2
    have hf2 : ∀ q, s2 q < 2 ^ w := upFit hf1 (v := 2) b2
    have hd2 : checksumProg.getD 2 Instr.reject = Instr.add 4 5 6 := rfl
    rw [exec_add_step (S := 22) (hS := by decide) hd2]
    have e25 : s2 5 = 2 := up_eq _ _ _
    have e26 : s2 6 = 1 := by
      rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]; exact up_eq _ _ _
    have hv2 : s2 5 + s2 6 = 3 := by rw [e25, e26]
    rw [hv2]
    set s3 : Nat → Nat := up s2 4 3 with hs3
    have hf3 : ∀ q, s3 q < 2 ^ w := upFit hf2 (v := 3) b3
    have hd3 : checksumProg.getD 3 Instr.reject = Instr.add 4 4 4 := rfl
    rw [exec_add_step (S := 21) (hS := by decide) hd3]
    have hv3 : s3 4 + s3 4 = 6 := by rw [show s3 4 = 3 from up_eq _ _ _]
    rw [hv3]
    set s4 : Nat → Nat := up s3 4 6 with hs4
    have hf4 : ∀ q, s4 q < 2 ^ w := upFit hf3 (v := 6) b6
    -- pc 4: the gate, passed (n ≥ 6), compared against the 6 in cell 4
    have hd4 : checksumProg.getD 4 Instr.reject = Instr.blt 0 4 23 := rfl
    have v40 : s4 0 = n := by
      rw [hs4]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (0 : Nat) ≠ 6)]
      exact inF_zero x
    have v44 : s4 4 = 6 := up_eq _ _ _
    rw [exec_blt_ge_step (S := 20) (hS := by decide) hd4 hf4 (by rw [v40, v44]; omega)]
    -- pc 5: the cursor 2n (no constant needed: n + n)
    have hd5 : checksumProg.getD 5 Instr.reject = Instr.add 0 0 0 := rfl
    rw [exec_add_step (S := 19) (hS := by decide) hd5]
    have hv5 : s4 0 + s4 0 = 2 * n := by rw [v40]; omega
    rw [hv5]
    set s5 : Nat → Nat := up s4 0 (2 * n) with hs5
    have hf5 : ∀ q, s5 q < 2 ^ w := upFit hf4 (v := 2 * n) h2n
    -- pc 6: save a₁ at 2n
    have hd6 : checksumProg.getD 6 Instr.reject = Instr.store 0 1 := rfl
    have v50 : s5 0 = 2 * n := up_eq _ _ _
    have v51 : s5 1 = x.a ⟨0, hn0⟩ := by
      rw [hs5]; rw [up_ne (by decide : (1 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (1 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (1 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (1 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (1 : Nat) ≠ 6)]
      exact ha1v
    rw [exec_store_step (S := 18) (hS := by decide) hd6 hf5]
    rw [v50, v51]
    set s6 : Nat → Nat := up s5 (2 * n) (x.a ⟨0, hn0⟩) with hs6
    have hf6 : ∀ q, s6 q < 2 ^ w := upFit hf5 (v := x.a ⟨0, hn0⟩) ha1
    -- pc 7: the second cursor 2n+1, from the literal 1 still in cell 6
    have hd7 : checksumProg.getD 7 Instr.reject = Instr.add 1 0 6 := rfl
    have v60 : s6 0 = 2 * n := by
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]; exact v50
    have v66 : s6 6 = 1 := by
      rw [hs6]; rw [up_ne (by omega : (6 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (6 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (6 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (6 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]
      rw [hs1]; exact up_eq _ _ _
    rw [exec_add_step (S := 17) (hS := by decide) hd7]
    have hv7 : s6 0 + s6 6 = 2 * n + 1 := by rw [v60, v66]
    rw [hv7]
    set s7 : Nat → Nat := up s6 1 (2 * n + 1) with hs7
    have hf7 : ∀ q, s7 q < 2 ^ w := upFit hf6 (v := 2 * n + 1) h2n1
    -- pc 8: save a₂ at 2n+1
    have hd8 : checksumProg.getD 8 Instr.reject = Instr.store 1 2 := rfl
    have v71 : s7 1 = 2 * n + 1 := up_eq _ _ _
    have v72 : s7 2 = x.a ⟨1, hn1⟩ := by
      rw [hs7]; rw [up_ne (by decide : (2 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (2 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (2 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (2 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (2 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (2 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (2 : Nat) ≠ 6)]
      exact ha2v
    rw [exec_store_step (S := 16) (hS := by decide) hd8 hf7]
    rw [v71, v72]
    set s8 : Nat → Nat := up s7 (2 * n + 1) (x.a ⟨1, hn1⟩) with hs8
    have hf8 : ∀ q, s8 q < 2 ^ w := upFit hf7 (v := x.a ⟨1, hn1⟩) ha2
    -- pc 9: the third cursor 2n+2, again from the literal 1
    have hd9 : checksumProg.getD 9 Instr.reject = Instr.add 2 1 6 := rfl
    have v81 : s8 1 = 2 * n + 1 := by
      rw [hs8]; rw [up_ne (by omega : (1 : Nat) ≠ 2 * n + 1)]; exact v71
    have v86 : s8 6 = 1 := by
      rw [hs8]; rw [up_ne (by omega : (6 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (6 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (6 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (6 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (6 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (6 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]
      rw [hs1]; exact up_eq _ _ _
    rw [exec_add_step (S := 15) (hS := by decide) hd9]
    have hv9 : s8 1 + s8 6 = 2 * n + 2 := by rw [v81, v86]
    rw [hv9]
    set s9 : Nat → Nat := up s8 2 (2 * n + 2) with hs9
    have hf9 : ∀ q, s9 q < 2 ^ w := upFit hf8 (v := 2 * n + 2) h2n2
    -- pc 10: save a₃ at 2n+2 — the last instruction that reads cell 3
    have hd10 : checksumProg.getD 10 Instr.reject = Instr.store 2 3 := rfl
    have v92 : s9 2 = 2 * n + 2 := up_eq _ _ _
    have v93 : s9 3 = x.a ⟨2, hn2⟩ := by
      rw [hs9]; rw [up_ne (by decide : (3 : Nat) ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : (3 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (3 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (3 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (3 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (3 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (3 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (3 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (3 : Nat) ≠ 6)]
      exact ha3v
    rw [exec_store_step (S := 14) (hS := by decide) hd10 hf9]
    rw [v92, v93]
    set s10 : Nat → Nat := up s9 (2 * n + 2) (x.a ⟨2, hn2⟩) with hs10
    have hf10 : ∀ q, s10 q < 2 ^ w := upFit hf9 (v := x.a ⟨2, hn2⟩) ha3
    -- pc 11: [2] := 2n >>> 1 = n
    have hd11 : checksumProg.getD 11 Instr.reject = Instr.shr 2 0 6 := rfl
    have v100 : s10 0 = 2 * n := by
      rw [hs10]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by decide : (0 : Nat) ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (0 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]
      rw [hs5]; exact up_eq _ _ _
    have v106 : s10 6 = 1 := by
      rw [hs10]; rw [up_ne (by omega : (6 : Nat) ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by decide : (6 : Nat) ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : (6 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (6 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (6 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (6 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (6 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (6 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]
      rw [hs1]; exact up_eq _ _ _
    rw [exec_shr_step (S := 13) (hS := by decide) hd11 hf10]
    have hv11 : s10 0 / 2 ^ s10 6 = n := by
      rw [v100, v106, show (2 : Nat) ^ 1 = 2 from by norm_num, Nat.mul_comm]
      exact Nat.mul_div_cancel n (by norm_num)
    rw [hv11]
    set s11 : Nat → Nat := up s10 2 n with hs11
    have hf11 : ∀ q, s11 q < 2 ^ w := upFit hf10 (v := n) hnv
    -- pc 12: [3] := n+1 (cell 3 is free: a₃ was saved at pc 10)
    have hd12 : checksumProg.getD 12 Instr.reject = Instr.add 3 2 6 := rfl
    have v116 : s11 6 = 1 := by
      rw [hs11]; rw [up_ne (by decide : (6 : Nat) ≠ 2)]; exact v106
    rw [exec_add_step (S := 12) (hS := by decide) hd12]
    have hv12 : s11 2 + s11 6 = n + 1 := by
      rw [show s11 2 = n from up_eq _ _ _, v116]
    rw [hv12]
    set s12 : Nat → Nat := up s11 3 (n + 1) with hs12
    have hf12 : ∀ q, s12 q < 2 ^ w := upFit hf11 (v := n + 1) hnp1
    -- pc 13: [4] := t
    have hd13 : checksumProg.getD 13 Instr.reject = Instr.load 4 3 := rfl
    have v123 : s12 3 = n + 1 := up_eq _ _ _
    have v12t : s12 (n + 1) = x.t := by
      rw [hs12]; rw [up_ne (by omega : n + 1 ≠ 3)]
      rw [hs11]; rw [up_ne (by omega : n + 1 ≠ 2)]
      rw [hs10]; rw [up_ne (by omega : n + 1 ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by omega : n + 1 ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : n + 1 ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by omega : n + 1 ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : n + 1 ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by omega : n + 1 ≠ 0)]
      rw [hs4]; rw [up_ne (by omega : n + 1 ≠ 4)]
      rw [hs3]; rw [up_ne (by omega : n + 1 ≠ 4)]
      rw [hs2]; rw [up_ne (by omega : n + 1 ≠ 5)]
      rw [hs1]; rw [up_ne (by omega : n + 1 ≠ 6)]
      exact inF_t x
    rw [exec_load_step (S := 11) (hS := by decide) hd13 hf12]
    rw [v123, v12t]
    set s13 : Nat → Nat := up s12 4 x.t with hs13
    have hf13 : ∀ q, s13 q < 2 ^ w := upFit hf12 (v := x.t) htv
    -- pc 14: [6] := a₁ (cell 0 still holds 2n)
    have hd14 : checksumProg.getD 14 Instr.reject = Instr.load 6 0 := rfl
    have v130 : s13 0 = 2 * n := by
      rw [hs13]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs12]; rw [up_ne (by omega : (0 : Nat) ≠ 3)]
      rw [hs11]; rw [up_ne (by decide : (0 : Nat) ≠ 2)]
      rw [hs10]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by decide : (0 : Nat) ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (0 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]
      rw [hs5]; exact up_eq _ _ _
    have v132n : s13 (2 * n) = x.a ⟨0, hn0⟩ := by
      rw [hs13]; rw [up_ne (by omega : 2 * n ≠ 4)]
      rw [hs12]; rw [up_ne (by omega : 2 * n ≠ 3)]
      rw [hs11]; rw [up_ne (by omega : 2 * n ≠ 2)]
      rw [hs10]; rw [up_ne (by omega : 2 * n ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by omega : 2 * n ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : 2 * n ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by omega : 2 * n ≠ 1)]
      rw [hs6]; exact up_eq _ _ _
    rw [exec_load_step (S := 10) (hS := by decide) hd14 hf13]
    rw [v130, v132n]
    set s14 : Nat → Nat := up s13 6 (x.a ⟨0, hn0⟩) with hs14
    have hf14 : ∀ q, s14 q < 2 ^ w := upFit hf13 (v := x.a ⟨0, hn0⟩) ha1
    -- pc 15: [3] := 2n + 2, rebuilt from the unspent literal 2 in cell 5
    have hd15 : checksumProg.getD 15 Instr.reject = Instr.add 3 0 5 := rfl
    have v140 : s14 0 = 2 * n := by
      rw [hs14]; rw [up_ne (by decide : (0 : Nat) ≠ 6)]; exact v130
    have v145 : s14 5 = 2 := by
      rw [hs14]; rw [up_ne (by decide : (5 : Nat) ≠ 6)]
      rw [hs13]; rw [up_ne (by decide : (5 : Nat) ≠ 4)]
      rw [hs12]; rw [up_ne (by omega : (5 : Nat) ≠ 3)]
      rw [hs11]; rw [up_ne (by decide : (5 : Nat) ≠ 2)]
      rw [hs10]; rw [up_ne (by omega : (5 : Nat) ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by decide : (5 : Nat) ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : (5 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; rw [up_ne (by decide : (5 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (5 : Nat) ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by decide : (5 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (5 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (5 : Nat) ≠ 4)]
      rw [hs2]; exact up_eq _ _ _
    rw [exec_add_step (S := 9) (hS := by decide) hd15]
    have hv15 : s14 0 + s14 5 = 2 * n + 2 := by rw [v140, v145]
    rw [hv15]
    set s15 : Nat → Nat := up s14 3 (2 * n + 2) with hs15
    have hf15 : ∀ q, s15 q < 2 ^ w := upFit hf14 (v := 2 * n + 2) h2n2
    -- pc 16: [3] := a₃, by indirection through the rebuilt address
    have hd16 : checksumProg.getD 16 Instr.reject = Instr.load 3 3 := rfl
    have v153 : s15 3 = 2 * n + 2 := up_eq _ _ _
    have v152 : s15 (2 * n + 2) = x.a ⟨2, hn2⟩ := by
      rw [hs15]; rw [up_ne (by omega : 2 * n + 2 ≠ 3)]
      rw [hs14]; rw [up_ne (by omega : 2 * n + 2 ≠ 6)]
      rw [hs13]; rw [up_ne (by omega : 2 * n + 2 ≠ 4)]
      rw [hs12]; rw [up_ne (by omega : 2 * n + 2 ≠ 3)]
      rw [hs11]; rw [up_ne (by omega : 2 * n + 2 ≠ 2)]
      rw [hs10]; exact up_eq _ _ _
    rw [exec_load_step (S := 8) (hS := by decide) hd16 hf15]
    rw [v153, v152]
    set s16 : Nat → Nat := up s15 3 (x.a ⟨2, hn2⟩) with hs16
    have hf16 : ∀ q, s16 q < 2 ^ w := upFit hf15 (v := x.a ⟨2, hn2⟩) ha3
    -- pc 17: [5] := a₂ (cell 1 still holds 2n+1)
    have hd17 : checksumProg.getD 17 Instr.reject = Instr.load 5 1 := rfl
    have v161 : s16 1 = 2 * n + 1 := by
      rw [hs16]; rw [up_ne (by decide : (1 : Nat) ≠ 3)]
      rw [hs15]; rw [up_ne (by decide : (1 : Nat) ≠ 3)]
      rw [hs14]; rw [up_ne (by decide : (1 : Nat) ≠ 6)]
      rw [hs13]; rw [up_ne (by decide : (1 : Nat) ≠ 4)]
      rw [hs12]; rw [up_ne (by omega : (1 : Nat) ≠ 3)]
      rw [hs11]; rw [up_ne (by decide : (1 : Nat) ≠ 2)]
      rw [hs10]; rw [up_ne (by omega : (1 : Nat) ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by decide : (1 : Nat) ≠ 2)]
      rw [hs8]; rw [up_ne (by omega : (1 : Nat) ≠ 2 * n + 1)]
      rw [hs7]; exact up_eq _ _ _
    have v162n1 : s16 (2 * n + 1) = x.a ⟨1, hn1⟩ := by
      rw [hs16]; rw [up_ne (by omega : 2 * n + 1 ≠ 3)]
      rw [hs15]; rw [up_ne (by omega : 2 * n + 1 ≠ 3)]
      rw [hs14]; rw [up_ne (by omega : 2 * n + 1 ≠ 6)]
      rw [hs13]; rw [up_ne (by omega : 2 * n + 1 ≠ 4)]
      rw [hs12]; rw [up_ne (by omega : 2 * n + 1 ≠ 3)]
      rw [hs11]; rw [up_ne (by omega : 2 * n + 1 ≠ 2)]
      rw [hs10]; rw [up_ne (by omega : 2 * n + 1 ≠ 2 * n + 2)]
      rw [hs9]; rw [up_ne (by omega : 2 * n + 1 ≠ 2)]
      rw [hs8]; exact up_eq _ _ _
    rw [exec_load_step (S := 7) (hS := by decide) hd17 hf16]
    rw [v161, v162n1]
    set s17 : Nat → Nat := up s16 5 (x.a ⟨1, hn1⟩) with hs17
    have hf17 : ∀ q, s17 q < 2 ^ w := upFit hf16 (v := x.a ⟨1, hn1⟩) ha2
    -- pc 18: [6] := a₁ + a₂
    have hd18 : checksumProg.getD 18 Instr.reject = Instr.add 6 6 5 := rfl
    have v176 : s17 6 = x.a ⟨0, hn0⟩ := by
      rw [hs17]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]
      rw [hs16]; rw [up_ne (by decide : (6 : Nat) ≠ 3)]
      rw [hs15]; rw [up_ne (by decide : (6 : Nat) ≠ 3)]
      rw [hs14]; exact up_eq _ _ _
    have v175 : s17 5 = x.a ⟨1, hn1⟩ := up_eq _ _ _
    rw [exec_add_step (S := 6) (hS := by decide) hd18]
    rw [v176, v175]
    set s18 : Nat → Nat := up s17 6 (x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩) with hs18
    have hf18 : ∀ q, s18 q < 2 ^ w :=
      upFit hf17 (v := x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩) hsum2
    -- pc 19: [6] := a₁ + a₂ + a₃
    have hd19 : checksumProg.getD 19 Instr.reject = Instr.add 6 6 3 := rfl
    have v183 : s18 3 = x.a ⟨2, hn2⟩ := by
      rw [hs18]; rw [up_ne (by decide : (3 : Nat) ≠ 6)]
      rw [hs17]; rw [up_ne (by decide : (3 : Nat) ≠ 5)]
      rw [hs16]; exact up_eq _ _ _
    rw [exec_add_step (S := 5) (hS := by decide) hd19]
    rw [show s18 6 = x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ from up_eq _ _ _, v183]
    set s19 : Nat → Nat :=
      up s18 6 (x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ + x.a ⟨2, hn2⟩) with hs19
    have hf19 : ∀ q, s19 q < 2 ^ w :=
      upFit hf18 (v := x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ + x.a ⟨2, hn2⟩) hsum3
    have w4 : s19 4 = x.t := by
      rw [hs19]; rw [up_ne (by decide : (4 : Nat) ≠ 6)]
      rw [hs18]; rw [up_ne (by decide : (4 : Nat) ≠ 6)]
      rw [hs17]; rw [up_ne (by decide : (4 : Nat) ≠ 5)]
      rw [hs16]; rw [up_ne (by decide : (4 : Nat) ≠ 3)]
      rw [hs15]; rw [up_ne (by decide : (4 : Nat) ≠ 3)]
      rw [hs14]; rw [up_ne (by decide : (4 : Nat) ≠ 6)]
      rw [hs13]; exact up_eq _ _ _
    have w6 : s19 6 = x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ + x.a ⟨2, hn2⟩ := up_eq _ _ _
    -- the decision: three cases on the trichotomy, exactly as the two `blt`s cut it
    rcases lt_trichotomy (x.a ⟨0, hn0⟩ + x.a ⟨1, hn1⟩ + x.a ⟨2, hn2⟩) x.t with hlt | heq | hgt
    · -- the witness is too small: `t < sum` fails, then `sum < t` jumps to FAIL
      have hd20 : checksumProg.getD 20 Instr.reject = Instr.blt 4 6 23 := rfl
      rw [exec_blt_ge_step (S := 4) (hS := by decide) hd20 hf19 (by rw [w4, w6]; omega)]
      have hd21 : checksumProg.getD 21 Instr.reject = Instr.blt 6 4 23 := rfl
      rw [exec_blt_lt_step (S := 3) (hS := by decide) hd21 hf19 (by rw [w4, w6]; exact hlt)]
      have hd23 : checksumProg.getD 23 Instr.reject = Instr.reject := rfl
      rw [exec_reject_step (S := 2) (hS := by decide) hd23]
      rw [checksumYes_eq_false_of x h10 (by intro hc; omega)]
    · -- equality: both `blt`s fall through to `accept`
      have hd20 : checksumProg.getD 20 Instr.reject = Instr.blt 4 6 23 := rfl
      rw [exec_blt_ge_step (S := 4) (hS := by decide) hd20 hf19 (by rw [w4, w6]; omega)]
      have hd21 : checksumProg.getD 21 Instr.reject = Instr.blt 6 4 23 := rfl
      rw [exec_blt_ge_step (S := 3) (hS := by decide) hd21 hf19 (by rw [w4, w6]; omega)]
      have hd22 : checksumProg.getD 22 Instr.reject = Instr.accept := rfl
      rw [exec_accept_step (S := 2) (hS := by decide) hd22]
      rw [checksumYes_eq_true x h10 heq]
    · -- the witness is too large: `t < sum` jumps straight to FAIL
      have hd20 : checksumProg.getD 20 Instr.reject = Instr.blt 4 6 23 := rfl
      rw [exec_blt_lt_step (S := 4) (hS := by decide) hd20 hf19 (by rw [w4, w6]; exact hgt)]
      have hd23 : checksumProg.getD 23 Instr.reject = Instr.reject := rfl
      rw [exec_reject_step (S := 3) (hS := by decide) hd23]
      rw [checksumYes_eq_false_of x h10 (by intro hc; omega)]
  · -- below the gate: the window is not addressable, the phase FAILs at pc 4
    have b1 : (1 : Nat) < 2 ^ w := by omega
    have b2 : (2 : Nat) < 2 ^ w := by omega
    have b3 : (3 : Nat) < 2 ^ w := by omega
    have b6 : (6 : Nat) < 2 ^ w := by omega
    have hd0 : checksumProg.getD 0 Instr.reject = Instr.one 6 := rfl
    rw [exec_one_step (S := 24) (hS := by decide) hd0]
    set s1 : Nat → Nat := up (inF x) 6 1 with hs1
    have hf1 : ∀ q, s1 q < 2 ^ w := upFit hfit0 (v := 1) b1
    have hd1 : checksumProg.getD 1 Instr.reject = Instr.add 5 6 6 := rfl
    rw [exec_add_step (S := 23) (hS := by decide) hd1]
    have hv1 : s1 6 + s1 6 = 2 := by rw [show s1 6 = 1 from up_eq _ _ _]
    rw [hv1]
    set s2 : Nat → Nat := up s1 5 2 with hs2
    have hf2 : ∀ q, s2 q < 2 ^ w := upFit hf1 (v := 2) b2
    have hd2 : checksumProg.getD 2 Instr.reject = Instr.add 4 5 6 := rfl
    rw [exec_add_step (S := 22) (hS := by decide) hd2]
    have hv2 : s2 5 + s2 6 = 3 := by
      rw [show s2 5 = 2 from up_eq _ _ _]
      rw [show s2 6 = 1 from by
        rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]; exact up_eq _ _ _]
    rw [hv2]
    set s3 : Nat → Nat := up s2 4 3 with hs3
    have hf3 : ∀ q, s3 q < 2 ^ w := upFit hf2 (v := 3) b3
    have hd3 : checksumProg.getD 3 Instr.reject = Instr.add 4 4 4 := rfl
    rw [exec_add_step (S := 21) (hS := by decide) hd3]
    have hv3 : s3 4 + s3 4 = 6 := by rw [show s3 4 = 3 from up_eq _ _ _]
    rw [hv3]
    set s4 : Nat → Nat := up s3 4 6 with hs4
    have hf4 : ∀ q, s4 q < 2 ^ w := upFit hf3 (v := 6) b6
    have hd4 : checksumProg.getD 4 Instr.reject = Instr.blt 0 4 23 := rfl
    have v40 : s4 0 = n := by
      rw [hs4]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs3]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (0 : Nat) ≠ 6)]
      exact inF_zero x
    have v44 : s4 4 = 6 := up_eq _ _ _
    rw [exec_blt_lt_step (S := 20) (hS := by decide) hd4 hf4 (by rw [v40, v44]; omega)]
    have hd23 : checksumProg.getD 23 Instr.reject = Instr.reject := rfl
    rw [exec_reject_step (S := 19) (hS := by decide) hd23]
    rw [checksumYes_eq_false x h10]

/-! ### Layer 6″ — the field shape and the leaf

`Routines.checksum_agrees` is

```
run checksumProg x ρ (checksumCost n x) = some (checksumB n x (fun r => (ρ r).toNat)).isSome
```

— an equation between `Option Bool`s with **no wrapper**, the same `isSome`
convention the alias field uses (and, as `KapilaAlias`'s `isSome_ne_failToNo`
records, the only faithful reading of a payload that is an estimate list rather
than a decision).  So the field needs no peel: `checksum_run_of_field` below is
the field, unchanged, which is the whole of the "bridge". -/

/-- The checksum field, peeled to nothing: it *is* the `Option`-free halt equation. -/
theorem checksum_run_of_field (R : Routines) (n : Nat) (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) :
    run R.checksumProg x ρ (R.checksumCost n x)
      = some (R.checksumB n x (fun r => (ρ r).toNat)).isSome :=
  R.checksum_agrees n x ρ

/-- The agreement for **this** program and spec, in the field's exact shape — no
wrapper, no `Option` ambiguity, nothing to peel. -/
theorem checksum_agrees_spec {n : Nat} (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (ω : Draws) :
    run checksumProg x ρ (checksumCost n x) = some ((checksumSpec n x ω).isSome) :=
  checksum_run x ρ ω

/-- **`LeafBnone`'s discharge.**  On the guard's complement, if `R.cost` collapses
to `R.checksumCost` (the segment is the whole program there, or the earlier
segments are free), then `R.checksum_agrees` *is* `LeafBnone R R.checksumProg`:
the phase's `none` is read as the program's NO, which is §7's «If it fails,
return NO» and nothing else.  The `FAIL → NO` control-flow fact stays
`LeafBnone`'s — a segment verdict can only say «succeeded», never «the program
answers NO».

This is the third of the four segment obligations in `agrees_main_iff_leaves`;
`LeafP` was the first (`LeafP_of_prelim_agrees`, `KapilaPrelim`) and `LeafAnone`
the second (`LeafAnone_of_alias_agrees`, `KapilaAlias`).  Only `LeafTest`
remains. -/
theorem LeafBnone_of_checksum_agrees (R : Routines)
    (hcost : ∀ (n : Nat) (x : Instance n), R.cost n x = R.checksumCost n x) :
    LeafBnone R R.checksumProg := by
  intro n x ρ _hf _hp _Ahat _ha ha
  rw [hcost n x, R.checksum_agrees n x ρ, ha]
  rfl

/-- The same discharge with the strong equation supplied directly — the form a
`Routines` builder proves before packaging it as the field (cf.
`LeafAnone_of_alias_run`). -/
theorem LeafBnone_of_checksum_run (R : Routines)
    (hcost : ∀ (n : Nat) (x : Instance n), R.cost n x = R.checksumCost n x)
    (hrun : ∀ (n : Nat) (x : Instance n) (ρ : Nat → BitVec (wordLength n x.bits)),
      run R.checksumProg x ρ (R.checksumCost n x)
        = some (R.checksumB n x (fun r => (ρ r).toNat)).isSome) :
    LeafBnone R R.checksumProg := by
  intro n x ρ _hf _hp _Ahat _ha ha
  rw [hcost n x, hrun n x ρ, ha]
  rfl

/-! ### The named residual, stated where the next mind will find it

What this file does **not** claim, in order of what it would cost to close:

1. **The block tables, the pattern family, and the weighting.**  Theorem B's
   procedure estimates `V_ρ` by sampling frequency tables, grouping frequencies by
   blockwise patterns, counting and sampling the resulting matches, and weighting
   by inverse multiplicity.  The text above is a *witness test*: it certifies a
   triple and FAILs otherwise, so its FAIL region is far wider than the paper's
   (`1 - o(1)` success).  Closing it means loops — the density and count steps
   iterate — plus the phase stream that `Draws` currently flattens into words.
2. **The complex estimate and the `1/8` accuracy.**  §6's estimates are sums of
   `e_P(·)` terms; this calculus has no `ℂ` arithmetic and no residue-bin
   density.  `checksum_support_in_bin` certifies the *support* of a term (the
   subset lands in `ρ`'s class mod every `P`) and nothing about its magnitude;
   the magnitude is `o5_mse_le`'s, named there.
3. **The multi-word accumulator.**  The estimates `V̂_ρ` are `ℚ` values carrying
   `n²` fractional bits while the word is `w = O(n + b)`.  `checksumProg` never
   computes them: its three reads (`t`, `a₁ + a₂ + a₃`) are single words, by
   `inF_lt` and `3·maxValue < 2^w`, both proved above.  The expansion into word
   operations is absorbed (`withinEnvelope_wordop_absorb`) but the *layout* of a
   `ℚ` accumulator is not written.
4. **`LeafTest`'s use of the estimates.**  `isSome` forgets the payload, so the
   lists this phase leaves behind are not certified by this field; `LeafTest`
   needs the payload convention (`rowTest_eq_of_rules` gives it the three loop
   rules, but nothing yet gives it the lists) — and, in this lane, the two
   estimates must additionally satisfy «their difference is the bin sum», which
   is where `LeafTest`'s remaining seam actually is.
5. **The failing draws' probability.**  `checksumSpec` ignores `ω`: the leg is
   deterministic.  Theorem B's phase is randomized, and its failure probability is
   what the union bound spends; nothing here touches that.

Statement.lean's hashes are untouched (`3dc6567e…34aa`): this module adds names
only. -/

end SubsetSumL25.Row
