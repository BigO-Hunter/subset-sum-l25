/-
Residual (ii) — **the bin sums, constructed rather than contracted**.

Why this file exists.  `KapilaEstimate` stated `BinSumAgrees`/`WideBinSumAgrees`
and `KapilaWide` wired the second into the stride-`k` exit, but neither _produced_
a `binSum`: both predicates were contracts with an existential hole where the
paper's quantity should be, and the residual text said so («no bin object exists in
the tree and neither landed leg pins one»).  A contract nobody inhabits is not a
residual, it is a hole in the statement of the theorem.  This module fixes the
`binSum` — pins it to a definite object, §6's own aggregate read in the only
vocabulary this tree has — and proves `WideBinSumAgrees` for it.  After this file
`rowTest_eq_wideBinSum`'s hypothesis is discharged **by construction**; what is
left is named in §S5, not hidden.

## §S1 — which object §6 leaves us, and why it is the digit aggregate

Eq. (6.1) defines `V_ρ = Σ_{I : Σ_{i∈I} b_i ≡ ρ} e_P(Σ_{i∈I} φ_i)` — a complex sum
over a residue bin.  The tree has no `ℂ`, no phases, and no residue machinery
beyond `Nat` mod (`KapilaChecksum`'s header says exactly this and keeps the
support content it *can* state: `checksum_sound`, `checksum_support_in_bin`).
What the tree does have is §7 step 7's comparison, which is where the bin sum is
*consumed*: the loop compares the two carried numerators at every index and takes
`|V̂ − Â| ≥ 1/2`.  So the `binSum` this module fixes is §6's aggregate at the
granularity the program reads it at:

  `binSum i = (Σ_{j<stride} (v_j − a_j)·2^{w·j}) / 2^F`,

the **signed aggregate of the two payload blocks' digits at index `i`, over the one
shared scale**.  Two facts recommend it over any other choice:

* it is what §6's `V_ρ` term *is* once the complex weight is dropped — a signed
  sum over the bin's digit positions, with `ρ = t mod P` selecting which terms
  belong (`checksum_support_in_bin`);
* it is **computable digitwise**: no cell ever holds the wide numerator
  (`numAt_not_word` forbids that), which is exactly why the comparison had to be
  re-shaped into `KapilaDigitwise`'s top-down walk.  `hitWord_binSumTest` below
  proves the loop's word test *is* the `1/2` test on this object, so the
  digitwise `digHalf`/`cmpSeg` machinery decides the bin-sum predicate — (ii) and
  (i) are one predicate, not two.

## §S2 — `WideBinSumAgrees`, proved for that `binSum`

`binSum_eq_placeValue_sub` is the whole of it: `placeValue_scale` at the two bases
clears the shared denominator, `numAt_cast` reads each numerator as its weighted
digits, `binDigits_eq_numAt_sub` distributes the difference over the digits (the
linearity that also has a `ℕ` reading — digits are why carries cost nothing here),
and the `memOf_toNat` bridge puts the memory's words back.  Nothing in the proof
consumes the payload lists, `dAt`, or the program: `wideBinSumAgrees_binSum` holds
**for every memory and every stride**, given only the digit fit.

That is the honest reading of what was proved, and it is worth stating plainly
rather than dressing up: `WideBinSumAgrees` has **no memory-side content**.  It is
not a constraint the layout must satisfy — it is the definition of what the bin
sum has to be for the wide test to be a test on bin sums.  The claim with content
is the *other* direction, which §S3 states in a form that does not mention the
memory at all.

## §S3 — the one named input (the accumulation stage)

A `binSum` defined *from* the memory would make the contract vacuous as a
*statement about the checksum phase*.  So §S3 restates it the way §6 needs it: the
phases' estimate numerators `numV`, `numA` are given independently, and

  `PayloadCarries f numV numA baseV baseA stride len`

is the single premise that the memory's digits **are** those numerators.  It is
the accumulation stage: §6.2's block tables write `⌈F/w⌉ + 1` words per estimate
(`payloadStride`, and `placeValueAt_payloadStride` proves a `payloadStride` block
carries an `F`-bit numerator *exactly*), and the tree's 24-instruction
`checksumProg` does **not** contain that stage — it saves three inputs at
`2n, 2n+1, 2n+2`, decides `a₁ + a₂ + a₃ = t`, and writes no payload block.  So
this is not a gap in the arithmetic; it is the one instruction block the text is
missing, and it is named as a `Prop` with a hypothesis-shaped interface rather than
left as prose.  `wideBinSumAgrees_carried` discharges `WideBinSumAgrees` from it.

What that hypothesis inherits from `KapilaChecksum`, said once and not implied:
the block tables, the inverse-multiplicity weighting, the residue-bin enumeration,
and the `1/8` accuracy are that file's named residual, and `PayloadCarries` does
not supply them — it supplies only «the digits are there», which is the part the
*wide layout* needs.  Also unchanged: the phase's FAIL region here is the triple
witness's, not Theorem B's `1 − o(1)`.

## §S5 — the residual, enumerated where the next mind will find it

* **(ii) the bin sums — CLOSED as a contract, one hypothesis named.**  The
  `binSum` is fixed (§S1) and `WideBinSumAgrees` is proved for it
  (`wideBinSumAgrees_binSum`), unconditionally in the memory.  The independent
  form is `wideBinSumAgrees_carried`, whose only input is `PayloadCarries` — the
  accumulation stage, named above.  **§S6 decides what *kind* of premise that is**
  (a data contract, not a program obligation) and places it as a named field of
  the seam record; the criterion is machine-checked there.
* **(i) `cmpSeg`'s segment proof** — unchanged by this file.  What this file adds
  to it is the tie `hitWord_binSumTest`: the segment's verdict is the bin-sum
  test, so the segment need not be re-argued in §6's vocabulary.
* **(iii) the program-entry reach premise** — untouched.
* **(iv) `KapilaAlgo.cost` and `D7.agrees`'s horizon** — untouched, and this file
  adds no charge: `binSum` is a *definition* of the compared quantity, not a
  computation the program performs.  The wide read's `stride` words per estimate
  remain (iv)'s to measure.

`Statement.lean` is untouched (`3dc6567e…34aa`); every name below is new and this
module is a leaf of the import DAG.

## §S6 — the seam record at the test path, and *which kind* of premise §S3 named

§S3 named `PayloadCarries` as «the accumulation stage the checksum program does not
contain».  Naming a premise settles that it is not floating; it does not settle **what
kind of premise it is**, and the two kinds cost a reader different things:

* **(a) a refinement obligation with a program** — the accumulation stage is instruction
  text the row owes, discharged §C10–§C12-style: a segment, its block-writing invariant,
  its cost shape.
* **(b) a data contract** — the caller supplies the accumulated blocks, and the premise is
  a precondition on the memory the test path reads, named beside the row's other inputs.

**The criterion.**  Does the row's `Routines` program family *contain* an accumulation
stage per §6.2, or does it read pre-accumulated payloads?  **Answered (b), from evidence:**

1. **§6.2 puts the accumulation inside the phase computation**: «Each phase is computed to
   error `2^{-2n²}` with dyadic parts, each weighted term is rounded to `n²` fractional
   bits, and the sums are exact» (`PROOF_0.4877.tex` B.4; §6.2's own «the finite-precision
   arithmetic do not change»).  In this row the phase computation *is*
   `Routines.aliasA`/`Routines.checksumB` — abstract fields returning `Option (List ℚ)`.
2. **The family's landed instruction texts are witness legs, not phase texts.**
   `prelimProg` (17 instructions), `aliasProg` (20) and `checksumProg` (24) each save their
   inputs, walk `a`'s array against `t`, and accept or reject; their **agreement fields are
   verdict-only** (`run prog … = some (phase …).isSome`; `prelim_agrees` through `failToNo`)
   — none of them reproduces an estimate list, let alone writes a payload block.
   Machine-checked in §S6 below: their memory writes are exactly `1`/`2`/`3` saves at
   `writePositions` `[6]`, `[6, 8]`, `[6, 8, 10]` — all ahead of each text's first `load` —
   and **every branch target is forward** (`noBackEdge` = `true`).  The landed texts are
   straight-line: there is no loop body in which an accumulation could run.
3. **The test path's convention already writes the memory as an *input*.**
   `PayloadConvention.mem` is documented «the segment's exit memory»; `Ahat`/`Vhat` are read
   from it, and the wide exit (`wideExit_eq_binSumDigits`) takes `hA`/`hV`, both stated
   through `numBlock`.  `payloadCarries_iff_numBlock` proves `PayloadCarries` **is** the
   digit-level form of the block equation — `numBlock w f baseV len stride =
   (List.range len).map numV ∧ …` — the row's own vocabulary, one level below the list
   equations.

So relative to every text the row has and every consumer it has, the payload blocks are
**pre-accumulated**: supplied from outside the family.  That is (b) — and the classification
is not a labelling taste, because an (a)-reading fails twice over:

* **(a) would be subsumed.**  The accumulation lives inside the phase computation, which the
  row already owes as the full `aliasProg`/`checksumProg` phase texts (the landed legs are
  verdict-only: `KapilaPrelim`/`KapilaAlias`/`KapilaChecksum`'s own named obligations).  An
  (a)-class `PayloadCarries` would be a sub-obligation of an obligation already named — a
  second charge for one debt.
* **(a) would assert a layout the paper does not fix.**  §6.2 fixes the *precision* (`n²`
  fractional bits) and exactness; it fixes no address layout.  The blocks at
  `base + i·stride` are `PayloadConvention`'s — this tree's *convention* (hence the name;
  `baseV`, `baseA`, `stride`, `blockLen` are caller-chosen fields).  A block-writing
  invariant would be a theorem about an interface we invented.  The honest form is the
  interface itself: *if* the blocks hold those numerators *then* the test path is correct —
  and the layout's inhabitation is already proved (`placeValueAt_payloadStride`: a
  `payloadStride` block carries an `F`-bit numerator exactly).

**Cost: zero.**  §S3 already recorded that `binSum` defines the compared quantity rather than
a computation the program performs; `PayloadCarries` likewise is not a summand of
`Routines.cost` — it is a precondition on the memory the segment reads.  Residual (iv)'s
horizon (§C12) is untouched by this section.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaLoop
import SubsetSumL25.Row.KapilaEstimate
import SubsetSumL25.Row.KapilaWide
import SubsetSumL25.Row.KapilaDigitwise

set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §S1 — the digit aggregate

The aggregate is stated at explicit addresses (`binDigits`), like `numAt`, so its
induction steps at the same word the reader steps at; `binSum` then addresses
estimate `i` at `base + i·stride`, exactly as `placeValue` does. -/

/-- **The signed digit aggregate of two blocks.**  At each digit position `j` the
two words' signed difference, weighted by its place `2^{w·j}`: §6's bin aggregate
once the complex weight is dropped, and the object a digitwise machine can form
without any cell holding a numerator. -/
def binDigits (w : Nat) (f : Nat → Nat) (addrV addrA stride : Nat) : ℚ :=
  ((List.range stride).map fun j =>
      ((f (addrV + j) : ℚ) - (f (addrA + j) : ℚ)) * (2 : ℚ) ^ (w * j)).sum

/-- **The empty aggregate is zero** — the digit sum's base case. -/
@[simp] theorem binDigits_zero (w : Nat) (f : Nat → Nat) (addrV addrA : Nat) :
    binDigits w f addrV addrA 0 = 0 := by
  simp [binDigits]

/-- **The aggregate is the difference of the numerators.**  Distributing the
difference over the digits is exact: the two sides are read independently, so no
carry couples them, and each digit contributes its own place value.  This is the
linearity that `sum_base_digits` reads from the bottom up (`KapilaWide`'s
`numAt` is the same sum), stated over `ℚ` because the bin sum is signed — a digit
of `Â` may exceed the digit of `V̂` at the same place. -/
theorem binDigits_eq_numAt_sub {w : Nat} (f : Nat → Nat) (addrV addrA stride : Nat) :
    binDigits w f addrV addrA stride
      = (numAt w f addrV stride : ℚ) - (numAt w f addrA stride : ℚ) := by
  induction stride with
  | zero => simp [binDigits, numAt]
  | succ m ih =>
    unfold binDigits at *
    rw [List.sum_range_succ, numAt_succ, numAt_succ, ih]
    push_cast
    ring

/-- **The bin sum.**  Estimate `i`'s bin term: the digit aggregate of the two
blocks at `base + i·stride`, over the single shared scale `2^-fracBits` — §6's
`V_ρ` term at the granularity §7 step 7 reads it (`KapilaEstimate`'s `placeValue`
is the same addressing, so the two sides differ only in sign of aggregation). -/
def binSum (w : Nat) (f : Nat → Nat) (baseV baseA stride fracBits : Nat) (i : Nat) : ℚ :=
  binDigits w f (baseV + i * stride) (baseA + i * stride) stride / (2 : ℚ) ^ fracBits

/-- **The numerator step, from `placeValue_scale`.**  `placeValue_scale` at the two
bases, subtracted: the difference of the two place values, scaled, is the
difference of the two base-`2^w` numerators.  This is the whole of what a
denominator-clearing argument has to do; everything after it is the aggregation. -/
theorem placeValue_sub_scale {w : Nat} (m : Nat → BitVec w) (baseV baseA stride fracBits i : Nat) :
    (placeValue m baseV stride fracBits i - placeValue m baseA stride fracBits i)
        * (2 : ℚ) ^ fracBits
      = ((List.range stride).map fun j =>
            ((m (baseV + i * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum
        - ((List.range stride).map fun j =>
            ((m (baseA + i * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum := by
  rw [sub_mul, placeValue_scale, placeValue_scale]

/-! ### §S2 — the bin sum *is* the wide place-value difference -/

/-- **The fixed `binSum` is the difference the wide test reads.**  Assembled from
the three landed pieces, in the order the arithmetic forces: `placeValue_scale`
clears the shared denominator (`placeValue_sub_scale`), `numAt_cast` says each
numerator is its weighted digits, and `binDigits_eq_numAt_sub` distributes the
difference over them; `memOf_toNat` is the memory bridge.  Nothing about the
payload lists, `dAt`, or the program is consumed. -/
theorem binSum_eq_placeValue_sub {w : Nat} (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w)
    (baseV baseA stride fracBits i : Nat) :
    binSum w f baseV baseA stride fracBits i
      = placeValue (memOf w f) baseV stride fracBits i
        - placeValue (memOf w f) baseA stride fracBits i := by
  have hpos : (0 : ℚ) < (2 : ℚ) ^ fracBits := by positivity
  unfold binSum
  rw [div_eq_iff (ne_of_gt hpos), placeValue_sub_scale]
  have hV : ((List.range stride).map fun j =>
        ((memOf w f (baseV + i * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum
      = ((numAt w f (baseV + i * stride) stride : Nat) : ℚ) := by
    rw [numAt_cast f (baseV + i * stride) stride]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [memOf_toNat f hfit]
  have hA : ((List.range stride).map fun j =>
        ((memOf w f (baseA + i * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum
      = ((numAt w f (baseA + i * stride) stride : Nat) : ℚ) := by
    rw [numAt_cast f (baseA + i * stride) stride]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [memOf_toNat f hfit]
  rw [hV, hA, binDigits_eq_numAt_sub]

/-- **`WideBinSumAgrees` is inhabited.**  `KapilaWide`'s exit and
`KapilaEstimate`'s `rowTest_eq_wideBinSum` both take this predicate as a
hypothesis; here it is discharged, for every memory and every stride, by the
`binSum` of §S1 fixed to the checksum phase's aggregate.  The contract item 3
carried is therefore no longer a hole in the statement: it is satisfied by the
object the paper names. -/
theorem wideBinSumAgrees_binSum {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (stride : Nat) :
    WideBinSumAgrees C (memOf w f) stride (binSum w f C.baseV C.baseA stride C.fracBits) := by
  intro i _
  exact (binSum_eq_placeValue_sub f hfit C.baseV C.baseA stride C.fracBits i).symm

/-! ### §S3 — the independent form, and the one named input

`binSum` above is *defined* from the memory, which is why §S2 holds so cheaply.
§6 needs the other form: the phases' estimates are given, and the memory must
carry them.  That premise is named once, here, and nowhere assumed.
-/

/-- **The accumulation premise — the one named input.**  The memory's digits at
`baseV + i·stride` / `baseA + i·stride` *are* the independent numerators `numV i` /
`numA i`; i.e. §6.2's block tables' output is written into the payload block.
Named as a `Prop` over the reader rather than described: the tree's
`checksumProg` decides and saves, and does not contain this stage. -/
def PayloadCarries (w : Nat) (f : Nat → Nat) (numV numA : Nat → Nat)
    (baseV baseA stride len : Nat) : Prop :=
  ∀ i, i < len →
    numAt w f (baseV + i * stride) stride = numV i
      ∧ numAt w f (baseA + i * stride) stride = numA i

/-- **`WideBinSumAgrees` from the accumulation premise.**  Given the phases'
numerators independently and the one premise that the memory carries them, the
wide place-value difference is their scaled difference — so the contract is
discharged from `PayloadCarries` alone, with the `binSum` no longer defined in
terms of the memory. -/
theorem wideBinSumAgrees_carried {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w)
    (stride : Nat) (numV numA : Nat → Nat)
    (h : PayloadCarries w f numV numA C.baseV C.baseA stride C.blockLen) :
    WideBinSumAgrees C (memOf w f) stride
      (fun i => ((numV i : ℚ) - (numA i : ℚ)) / (2 : ℚ) ^ C.fracBits) := by
  intro i hi
  show placeValue (memOf w f) C.baseV stride C.fracBits i
      - placeValue (memOf w f) C.baseA stride C.fracBits i
    = ((numV i : ℚ) - (numA i : ℚ)) / (2 : ℚ) ^ C.fracBits
  rw [← binSum_eq_placeValue_sub f hfit]
  unfold binSum
  rw [binDigits_eq_numAt_sub, (h i hi).1, (h i hi).2]

/-! ### §S4 — wiring the fix into the stride-`k` exit

`KapilaWide`'s exit theorem took `WideBinSumAgrees` as a hypothesis; with §S2 the
exit is a theorem about the bin sums and nothing else. -/

/-- **The stride-`k` loop's exit *is* the test on the bin sums.**  `KapilaWide`'s
`wideExit_eq_binSum'` with its `binSum` hypothesis discharged by
`wideBinSumAgrees_binSum`: no hypothesis about the bin sums remains, so the object
the paper's §6 asserts is the object this exit tests. -/
theorem wideExit_eq_binSumDigits {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) {stride : Nat}
    (hfrac : 1 ≤ C.fracBits)
    (hA : C.Ahat = (numBlock w f C.baseA C.blockLen stride).map (toQ C.fracBits))
    (hV : C.Vhat = (numBlock w f C.baseV C.blockLen stride).map (toQ C.fracBits)) :
    (decide (0 < hitCount (2 ^ (C.fracBits - 1))
        (numBlock w f C.baseV C.blockLen stride)
        (numBlock w f C.baseA C.blockLen stride)) : Bool)
      = ((List.range C.blockLen).map
          fun i => decide ((1 / 2 : ℚ) ≤ |binSum w f C.baseV C.baseA stride C.fracBits i|)).any id :=
  wideExit_eq_binSum' C f hfit hfrac hA hV _
    (wideBinSumAgrees_binSum C f hfit stride)

/-! ### §S5 — the bin-sum test is the digitwise predicate

The payoff of fixing the `binSum` this way rather than arbitrarily: the loop's
per-index word test (`hitWord` at `h = 2^{F−1}`), the `ℚ` test `rowTest` performs,
and the digitwise decision `digHalf`/`cmpSeg` implement are **one predicate**.
So the segment proof residual (i) does not have to be re-argued in §6's
vocabulary — and the arithmetic it decides is exactly the bin sum's. -/

/-- **The `1/2` test at a numerator *difference*.**  `halfTest_iff_wordDiff` is
stated about the two scaled operands; the bin sum is the difference over one
denominator, so the two forms are related once, here. -/
theorem halfTest_diff_iff_wordDiff {F : Nat} (hF : 1 ≤ F) (V A : Nat) :
    ((1 / 2 : ℚ) ≤ |((V : ℚ) - (A : ℚ)) / (2 : ℚ) ^ F|) ↔ 2 ^ (F - 1) ≤ wordDiff V A := by
  rw [sub_div]
  exact halfTest_iff_wordDiff hF V A

/-- **The bin-sum test is an integer comparison.**  The fixed `binSum`'s `1/2`
test is `2^{F−1} ≤ |numV − numA|` on the two carried numerators — the predicate
`KapilaDigitwise` decides digitwise, with no cell holding either numerator. -/
theorem binSumTest_iff_wordDiff {w : Nat} (f : Nat → Nat) (baseV baseA stride fracBits i : Nat)
    (hF : 1 ≤ fracBits) :
    ((1 / 2 : ℚ) ≤ |binSum w f baseV baseA stride fracBits i|)
      ↔ 2 ^ (fracBits - 1)
          ≤ wordDiff (numAt w f (baseV + i * stride) stride)
              (numAt w f (baseA + i * stride) stride) := by
  unfold binSum
  rw [binDigits_eq_numAt_sub]
  exact halfTest_diff_iff_wordDiff hF _ _

/-- **The loop's word test *is* the bin-sum test.**  §7 step 7's `hitWord` on the
two carried numerators — the quantity `scan_run` accumulates — is the `1/2` test on
the bin sum this module fixes.  So (ii) and (i) are one predicate: the digitwise
walk's verdict is the bin-sum verdict. -/
theorem hitWord_binSumTest {w : Nat} (f : Nat → Nat) (baseV baseA stride fracBits i : Nat)
    (hF : 1 ≤ fracBits) :
    hitWord (2 ^ (fracBits - 1)) (numAt w f (baseV + i * stride) stride)
        (numAt w f (baseA + i * stride) stride) = 1
      ↔ (1 / 2 : ℚ) ≤ |binSum w f baseV baseA stride fracBits i| := by
  rw [hitWord_eq_ratTest hF]
  unfold binSum
  rw [binDigits_eq_numAt_sub, ← sub_div]

/-! ### §S6 — the seam record at the test path

The header's §S6 says *which kind* of premise `PayloadCarries` is and why.  This section is
its two machine-checked halves: the **evidence** (the row's landed phase texts write no
accumulator — they are straight-line witness legs whose only memory writes are their saves),
and the **placement** (the premise as an explicit field of a seam record, used by a consumer
theorem rather than merely declared). -/

/-- `true` exactly on the one instruction that writes memory. -/
def isWrite : Instr → Bool
  | .store _ _ => true
  | _ => false

/-- Positions (in the text) of the instructions that write memory. -/
def writePositions : List Instr → List Nat
  | [] => []
  | i :: rest => (if isWrite i then [0] else []) ++ (writePositions rest).map (· + 1)

/-- `true` if every branch target is forward of its own position — i.e. the text is
straight-line, with no loop body for an accumulation stage to live in. -/
def noBackEdge : List Instr → Nat → Bool
  | [], _ => true
  | i :: rest, k =>
    (match i with
      | .blt _ _ l => decide (k < l)
      | _ => true) && noBackEdge rest (k + 1)

/-- **§4's text writes memory once, in its save.** -/
theorem prelimProg_writes : writePositions prelimProg = [6] := by decide

/-- **§5.2's alias text writes memory twice, in its saves.** -/
theorem aliasProg_writes : writePositions aliasProg = [6, 8] := by decide

/-- **§6's checksum text writes memory three times, in its saves.** -/
theorem checksumProg_writes : writePositions checksumProg = [6, 8, 10] := by decide

/-- **§4's text is straight-line** (no backward branch). -/
theorem prelimProg_straightLine : noBackEdge prelimProg 0 = true := by decide

/-- **§5.2's alias text is straight-line.** -/
theorem aliasProg_straightLine : noBackEdge aliasProg 0 = true := by decide

/-- **§6's checksum text is straight-line.** -/
theorem checksumProg_straightLine : noBackEdge checksumProg 0 = true := by decide

/-- **The three landed phase texts are straight-line** — every branch target is forward, so
none of them has a loop body, and there is no iteration in which an accumulation could run. -/
theorem phaseTexts_no_accumulation :
    noBackEdge prelimProg 0 = true ∧ noBackEdge aliasProg 0 = true
      ∧ noBackEdge checksumProg 0 = true
      ∧ writePositions prelimProg = [6] ∧ writePositions aliasProg = [6, 8]
      ∧ writePositions checksumProg = [6, 8, 10] :=
  ⟨prelimProg_straightLine, aliasProg_straightLine, checksumProg_straightLine,
    prelimProg_writes, aliasProg_writes, checksumProg_writes⟩

/-- **`PayloadCarries` is the row's own block equation**, at the digit level: the memory's two
blocks read back as the independent numerators.  `numBlock` is the stride-`k` reader the wide
exit's `hA`/`hV` already name, so the premise is stated in the vocabulary the test path uses —
not in a new one, and not as a claim about any program. -/
theorem payloadCarries_iff_numBlock {w : Nat} (f : Nat → Nat) (numV numA : Nat → Nat)
    (baseV baseA stride len : Nat) :
    PayloadCarries w f numV numA baseV baseA stride len
      ↔ (numBlock w f baseV len stride = (List.range len).map numV
          ∧ numBlock w f baseA len stride = (List.range len).map numA) := by
  unfold PayloadCarries numBlock
  constructor
  · intro h
    exact ⟨List.map_congr_left (fun s hs => (h s (List.mem_range.mp hs)).1),
      List.map_congr_left (fun s hs => (h s (List.mem_range.mp hs)).2)⟩
  · rintro ⟨hV, hA⟩ i hi
    exact ⟨(List.map_inj_left.mp hV) i (List.mem_range.mpr hi),
      (List.map_inj_left.mp hA) i (List.mem_range.mpr hi)⟩

/-- **The seam record at the test path.**  The row's program seam (`D7`) is about a program's
run; this one is about the *data* the test segment reads, and it is the only place the
accumulation appears as a premise.  `carries` is the named contract (`PayloadCarries`); the
other fields are the digit fit and the two independent numerator families it speaks about. -/
structure PayloadSeam {n : Nat} {x : Instance n} (C : PayloadConvention n x) (w : Nat)
    (f : Nat → Nat) (stride : Nat) where
  /-- Every memory word is a `w`-bit value — the digit fit the `ℚ` bridge consumes. -/
  fit : ∀ z, f z < 2 ^ w
  /-- The alias phase's independent numerators `Â_s`. -/
  numV : Nat → Nat
  /-- The checksum phase's independent numerators `V̂_ρ`. -/
  numA : Nat → Nat
  /-- **The data contract**: the payload blocks hold those numerators. -/
  carries : PayloadCarries w f numV numA C.baseV C.baseA stride C.blockLen

namespace PayloadSeam

variable {n : Nat} {x : Instance n} {C : PayloadConvention n x} {w : Nat} {f : Nat → Nat}
  {stride : Nat}

/-- **The wide bin-sum contract, from the seam record alone.**  The premise is *used*, not
declared: the record's fields are exactly `wideBinSumAgrees_carried`'s hypotheses, so §S3's
independent form is unchanged by the classification — what changed is that its input now has a
name and a place. -/
theorem agrees (S : PayloadSeam C w f stride) :
    WideBinSumAgrees C (memOf w f) stride
      (fun i => ((S.numV i : ℚ) - (S.numA i : ℚ)) / (2 : ℚ) ^ C.fracBits) :=
  wideBinSumAgrees_carried C f S.fit stride S.numV S.numA S.carries

end PayloadSeam

end SubsetSumL25.Row
