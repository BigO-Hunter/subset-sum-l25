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
  accumulation stage, named above.
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

end SubsetSumL25.Row
