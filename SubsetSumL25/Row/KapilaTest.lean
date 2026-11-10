/-
`LeafTest`'s **first obligation** — the payload convention for §7 step 7's segment.

Why this file exists.  `agrees_main_iff_leaves` cuts the main branch into four
segment obligations; three are discharged (`LeafP`, `LeafAnone`, `LeafBnone`).
The fourth, `LeafTest`, must produce the verdict `Routines.rowTest Ahat Vhat` from
the *stored estimate lists*, and the three landed legs deliberately leave two
gaps in front of it:

1. `alias_agrees` / `checksum_agrees` are stated through `Option.isSome`, and
   `isSome_forgets_payload` records the price: the payload — the estimate lists
   themselves — is gone.  A field that says «the phase succeeded» cannot say
   «the phase left *these* lists behind».
2. `rowTest_eq_of_rules` records the other half: `rowTest` is *determined* by
   three equations (nil/left, nil/right, cons/cons), so no instruction-level
   proof of the segment has to reason about `rowTest` at all — it has to
   establish exactly those three equations at the segment's exit.

This file lands the bridge between the two: **the exit convention**.  It is
statement-and-definition work only.  It does *not* walk the segment, does not
write the loop, and does not touch the estimates' arithmetic relation; those are
`LeafTest`'s remaining obligations and are named at the bottom, where the next
mind will find them rather than rediscover them.

What the convention says, in one sentence: **the segment's exit memory holds the
two estimate lists in a declared fixed-point layout, and the segment's verdict
function obeys the three `rowTest` rules with respect to those lists.**  The
payload lists are *defined from the memory* (`PayloadConvention.Ahat`,
`PayloadConvention.Vhat`), so they cannot lie: there is no field asserting the
lists are what the memory says, because the lists simply *are* that read.  This
is the sharp form of «the payload survives to the exit», and it is where the
`ℚ` accumulator layout obligation lands: one equation per block, saying the exit
memory holds those words at that scale.

Statement.lean's hashes are untouched (`3dc6567e…34aa`); this module adds names
only, and it is a leaf of the import DAG, so no built module's hash moves.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaPrelim
import SubsetSumL25.Row.KapilaAlias
import SubsetSumL25.Row.KapilaChecksum

set_option maxHeartbeats 800000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### Layer 7.0 — the payload layout

Two lists of `ℚ` values must live in a word memory.  The layout is fixed point:
`len` words starting at `base`, each read as `⌊x⌋/2^{fracBits}`.  §6.2's estimates
carry `n²` fractional bits, so `fracBits = n²` and `len = ⌈n²/w⌉ + 1` per estimate
— the two fields the multi-word accumulator obligation fills in; nothing here
fixes them, and nothing here needs them to be fixed. -/

/-- A payload block: `len` words starting at `base`, read as fixed point with
`fracBits` fractional bits.  The block is the *only* place a phase's estimate
lists can live at the exit, and `mem` is the exit memory itself — so a payload
read through this def is what the segment actually left behind, not a value
threaded beside it. -/
def payloadBlock {w : Nat} (fracBits base len : Nat) (m : Nat → BitVec w) : List ℚ :=
  (List.range len).map fun i => ((m (base + i)).toNat : ℚ) / (2 : ℚ) ^ fracBits

@[simp] theorem payloadBlock_zero {w : Nat} (fracBits base : Nat) (m : Nat → BitVec w) :
    payloadBlock fracBits base 0 m = [] := rfl

theorem payloadBlock_length {w : Nat} (fracBits base len : Nat) (m : Nat → BitVec w) :
    (payloadBlock fracBits base len m).length = len := by
  simp [payloadBlock]

/-- The block's `i`-th entry, read at the address the layout declares — the form
the accumulator obligation's per-word equation will take. -/
theorem payloadBlock_getElem? {w : Nat} (fracBits base len : Nat) (m : Nat → BitVec w)
    (i : Nat) :
    (payloadBlock fracBits base len m)[i]?
      = if i < len then some (((m (base + i)).toNat : ℚ) / (2 : ℚ) ^ fracBits) else none := by
  unfold payloadBlock
  by_cases h : i < len
  · rw [List.getElem?_map, List.getElem?_range h]
    simp [h]
  · have h' : len ≤ i := by omega
    rw [List.getElem?_map, List.getElem?_eq_none (by simp [h'])]
    simp [h]

/-! ### Layer 7.1 — the exit convention

The structure is the segment's *contract*: two payload exits, the verdict
function computed from them, and the three rules that — by
`rowTest_eq_of_rules` — determine that function.  Every field is either data the
exit memory supplies or one of the three equations, so a program that reaches
this exit discharges the conventions' fields and nothing else. -/

/-- **§7 step 7's exit convention.**  At the test segment's exit:

* the two estimate lists sit in the exit memory `mem` as fixed-point blocks at
  `baseA` / `baseV` with `fracBits` fractional bits and `blockLen` words each
  (`PayloadConvention.Ahat`, `PayloadConvention.Vhat`);
* the segment's verdict function `verdict` obeys `rowTest`'s three rules *on
  those lists*.

By `rowTest_eq_of_rules` the last three fields are not a weakening: they
determine `verdict` outright, so the segment cannot obey them and still compute
something other than `rowTest` (`PayloadConvention.verdict_eq_rowTest`).  What
remains for `LeafTest` is then exactly the control flow — reach this exit with
this memory — which is the loop and the walk, deliberately not this file's. -/
structure PayloadConvention (n : Nat) (x : Instance n) where
  /-- Fractional bits of the payload words: §6.2's `n²`. -/
  fracBits : Nat
  /-- Words per payload block: `⌈n²/w⌉ + 1` at the paper's parameters. -/
  blockLen : Nat
  /-- Address of the alias phase's payload block. -/
  baseA : Nat
  /-- Address of the checksum phase's payload block. -/
  baseV : Nat
  /-- The segment's exit memory. -/
  mem : Nat → BitVec (wordLength n x.bits)
  /-- The verdict function the segment computes from the two lists. -/
  verdict : List ℚ → List ℚ → Bool
  /-- Rule 1 (the loop's entry): an empty alias list never fires. -/
  rule_nil_left : ∀ V : List ℚ, verdict [] V = false
  /-- Rule 2 (the loop's exit): an empty checksum list never fires. -/
  rule_nil_right : ∀ A : List ℚ, verdict A [] = false
  /-- Rule 3 (the loop's step): one pair's difference against `1/2`, then the
  rest — §7 step 7's «the sum of the squares … exceeds 1/4» in `ℚ` form
  (`abs_ge_half_iff` is the identification). -/
  rule_cons_cons : ∀ (a : ℚ) (A : List ℚ) (v : ℚ) (V : List ℚ),
    verdict (a :: A) (v :: V) = (decide ((1 / 2 : ℚ) ≤ |v - a|) || verdict A V)

namespace PayloadConvention

variable {n : Nat} {x : Instance n}

/-- The alias phase's estimate list, as the exit memory holds it. -/
def Ahat (C : PayloadConvention n x) : List ℚ :=
  payloadBlock C.fracBits C.baseA C.blockLen C.mem

/-- The checksum phase's estimate list, as the exit memory holds it. -/
def Vhat (C : PayloadConvention n x) : List ℚ :=
  payloadBlock C.fracBits C.baseV C.blockLen C.mem

/-- The `i`-th alias estimate, read word-by-word — the form the accumulator
layout obligation states its per-word equations in. -/
def aAt (C : PayloadConvention n x) (i : Nat) : ℚ :=
  ((C.mem (C.baseA + i)).toNat : ℚ) / (2 : ℚ) ^ C.fracBits

/-- The `i`-th checksum estimate. -/
def vAt (C : PayloadConvention n x) (i : Nat) : ℚ :=
  ((C.mem (C.baseV + i)).toNat : ℚ) / (2 : ℚ) ^ C.fracBits

/-- **The estimate §7 step 7 compares**: `d_i = V̂_i − Â_i`, read straight off
the exit memory (`dAt_eq`).  The cross-estimate obligation states «`d` is the
bin sum» about *this* def, which is the point of the convention: before it, the
quantity the test consumes did not exist anywhere in the tree. -/
def dAt (C : PayloadConvention n x) (i : Nat) : ℚ := C.vAt i - C.aAt i

/-! #### The well-formedness lemmas -/

theorem Ahat_eq_map (C : PayloadConvention n x) :
    C.Ahat = (List.range C.blockLen).map C.aAt := rfl

theorem Vhat_eq_map (C : PayloadConvention n x) :
    C.Vhat = (List.range C.blockLen).map C.vAt := rfl

theorem Ahat_length (C : PayloadConvention n x) : C.Ahat.length = C.blockLen :=
  payloadBlock_length C.fracBits C.baseA C.blockLen C.mem

theorem Vhat_length (C : PayloadConvention n x) : C.Vhat.length = C.blockLen :=
  payloadBlock_length C.fracBits C.baseV C.blockLen C.mem

/-- **The payload survives to the exit.**  `d_i` is a function of two words and
the scale alone — so the list `isSome` forgets is recovered exactly, and the
accumulator layout obligation has precisely one equation per estimate to prove:
that the exit memory holds these words at this scale. -/
theorem dAt_eq (C : PayloadConvention n x) (i : Nat) :
    C.dAt i
      = ((C.mem (C.baseV + i)).toNat : ℚ) / (2 : ℚ) ^ C.fracBits
        - ((C.mem (C.baseA + i)).toNat : ℚ) / (2 : ℚ) ^ C.fracBits := rfl

theorem dAt_def (C : PayloadConvention n x) (i : Nat) : C.dAt i = C.vAt i - C.aAt i := rfl

/-! #### The rules determine the verdict -/

/-- **The convention computes `rowTest`.**  The three exit equations are not
merely true of the segment's verdict — they characterise it
(`rowTest_eq_of_rules`), so a program that satisfies them has proved §7 step 7's
test and not an approximation of it. -/
theorem verdict_eq_rowTest (C : PayloadConvention n x) :
    ∀ A V : List ℚ, C.verdict A V = Routines.rowTest A V :=
  rowTest_eq_of_rules C.verdict C.rule_nil_left C.rule_nil_right C.rule_cons_cons

/-- The same, at the carrier: the segment's verdict on the payloads it *left* is
§7 step 7's test on those payloads.  This is the equation `LeafTest` needs, with
the payload supplied instead of forgotten. -/
theorem verdict_Ahat_Vhat (C : PayloadConvention n x) :
    C.verdict C.Ahat C.Vhat = Routines.rowTest C.Ahat C.Vhat :=
  C.verdict_eq_rowTest C.Ahat C.Vhat

end PayloadConvention

/-! ### Layer 7.2 — the rules *are* `rowTest`, and `isSome` is not enough

Two statements about the convention's exact strength, both stated so the next
mind inherits a measured boundary rather than a hope. -/

/-- **`rowTest`'s rules, iff.**  A `Bool`-valued function of two estimate lists
obeys the three exit equations **iff** it is `rowTest` pointwise.  The forward
direction is `rowTest_eq_of_rules`; the backward direction instantiates
`rowTest`'s own three lemmas, so the rule set is neither too weak to pin the
test nor stronger than it. -/
theorem payload_rules_iff (f : List ℚ → List ℚ → Bool) :
    ((∀ V : List ℚ, f [] V = false) ∧ (∀ A : List ℚ, f A [] = false) ∧
      (∀ (a : ℚ) (A : List ℚ) (v : ℚ) (V : List ℚ),
        f (a :: A) (v :: V) = (decide ((1 / 2 : ℚ) ≤ |v - a|) || f A V)))
      ↔ ∀ A V : List ℚ, f A V = Routines.rowTest A V := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact rowTest_eq_of_rules f h0 h1 h2
  · intro h
    refine ⟨fun V => ?_, fun A => ?_, fun a A v V => ?_⟩
    · rw [h, rowTest_nil_left]
    · rw [h, rowTest_nil_right]
    · rw [h (a :: A) (v :: V), rowTest_cons_cons, h A V]

/-- §7 step 7's test genuinely consumes its payload: two estimate lists with the
same length and verdict difference can still be separated.  (Concretely `[0]`
against `[1]` fires and `[0]` against `[0]` does not.) -/
theorem rowTest_separates_payloads :
    ∃ (A V A' V' : List ℚ), Routines.rowTest A V ≠ Routines.rowTest A' V' := by
  have h1 : Routines.rowTest [(0 : ℚ)] [(1 : ℚ)] = true := by
    rw [rowTest_cons_cons, rowTest_nil_left]
    norm_num
  have h0 : Routines.rowTest [(0 : ℚ)] [(0 : ℚ)] = false := by
    rw [rowTest_cons_cons, rowTest_nil_left]
    norm_num
  exact ⟨[0], [1], [0], [0], by rw [h1, h0]; decide⟩

/-- **Why the convention is needed at all.**  `isSome_forgets_payload` shows the
two landed fields cannot tell payloads apart; the test *does* tell them apart.
So a field stated through `isSome` is strictly less information than `LeafTest`
consumes, and no amount of reasoning about the field recovers the lists — the
segment must carry the convention. -/
theorem isSome_not_enough :
    ∃ (A V A' V' : List ℚ),
      (some A : Option (List ℚ)).isSome = (some A').isSome
        ∧ Routines.rowTest A V ≠ Routines.rowTest A' V' := by
  obtain ⟨A, V, A', V', h⟩ := rowTest_separates_payloads
  exact ⟨A, V, A', V', rfl, h⟩

/-! ### Layer 7.3 — the convention is sufficient for `LeafTest`

Statement only.  `LeafTest` reduces to *reaching* such an exit: the two premises
left explicit below are exactly `LeafTest`'s remaining work, and neither is
bookkeeping — `hexit` is the loop plus the walk (obligations 2), and the
`C.Ahat = Ahat` / `C.Vhat = Vhat` conjuncts are the identification of the exit's
payload with the `Routines` fields' payloads, which is the same «`isSome` forgets
it» gap one level down (obligation 3 starts from it). -/

/-- **`LeafTest` from a payload exit.**  If, on the main branch, the test
segment's exit *is* a `PayloadConvention` carrying the very lists the `Routines`
fields report, then the segment's verdict is `rowTest` of those lists — which is
`LeafTest`, verbatim.  What is not proved here is that the segment reaches such
an exit; that is the loop and the walk, and this theorem is the exact shape they
have to fill. -/
theorem LeafTest_of_payload_exit (R : Routines) (program : List Instr)
    (hexit : ∀ (n : Nat) (x : Instance n) (ρ : Nat → BitVec (wordLength n x.bits)),
      R.fallback n x = false → R.prelim n x (fun r => (ρ r).toNat) = none →
      ∀ (Ahat : List ℚ), R.aliasA n x (fun r => (ρ r).toNat) = some Ahat →
      ∀ (Vhat : List ℚ), R.checksumB n x (fun r => (ρ r).toNat) = some Vhat →
      ∃ C : PayloadConvention n x,
        C.Ahat = Ahat ∧ C.Vhat = Vhat
          ∧ run program x ρ (R.cost n x) = some (C.verdict C.Ahat C.Vhat)) :
    LeafTest R program := by
  intro n x ρ hf hp Ahat ha Vhat hb
  obtain ⟨C, hA, hV, hrun⟩ := hexit n x ρ hf hp Ahat ha Vhat hb
  rw [hrun, hA, hV, C.verdict_eq_rowTest]

/-! ### The named residual, stated where the next mind will find it

`LeafTest`'s four obligations, with what this file does and does not do to each:

1. **The payload convention — LANDED (this file).**  Two list-valued exits
   defined from the exit memory (`Ahat`, `Vhat`), the estimate `d = V̂_i − Â_i`
   defined from it (`dAt`, `dAt_eq`), and the three `rowTest` rules as equations
   at the exit, with `payload_rules_iff` showing the rule set *is* `rowTest` and
   `isSome_not_enough` showing why the landed fields cannot supply it.
   *Not* claimed: that any program reaches such an exit.
2. **The scan's loop rules — NOT STARTED.**  `payload_rules_iff` fixes exactly
   what an instruction-level proof must establish (three equations), but the
   first backwards jump in this calculus, and a word-op cost model for it, are
   untouched.  `payloadBlock`'s layout is *static*: the loop is what would fill
   an arbitrary number of blocks, and the convention deliberately says nothing
   about how many.
3. **The estimates' arithmetic relation — NOT STARTED.**  `dAt` is now the
   object such a statement is about («`d_i` is the bin sum»), and the fields
   `fracBits`/`blockLen` are the parameters it will be phrased in.  Nothing here
   asserts it.
4. **The multi-word accumulator — PLACE FOUND, LAYOUT NOT WRITTEN.**  The
   convention's `fracBits` and `blockLen` are §6.2's `n²` and `⌈n²/w⌉ + 1`, and
   `dAt_eq` says the estimate is two words and a scale.  What is not written is
   the word arithmetic that fills them, and the carry structure across
   `⌈n²/w⌉ + 1` words.

Statement.lean's hashes are untouched (`3dc6567e…34aa`): this module adds names
only. -/

end SubsetSumL25.Row
