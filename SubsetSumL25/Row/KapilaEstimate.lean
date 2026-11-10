/-
`LeafTest`'s **third obligation** — the estimates' arithmetic relation.

Why this file exists.  `KapilaTest` landed the payload convention: the exit
memory holds two fixed-point blocks (`PayloadConvention.Ahat`,
`PayloadConvention.Vhat`) and `PayloadConvention.dAt i = vAt i - aAt i` is the
quantity §7 step 7 compares.  `KapilaLoop` landed the bridge that makes such a
read legitimate in the first place, `payloadBlock_memOf`: the block read off a
`memOf` memory *is* the `ℕ`-valued state's words scaled to `ℚ`.

Those two facts have so far sat in different vocabularies.  `payloadBlock_memOf`
is phrased as word-level agreement between a memory and a state function `f`,
which reads as a statement about *pre-agreed memory*.  But a state function is
exactly what the phases manipulate: `f` at `baseA`/`baseV` **is** the pair of
accumulator blocks.  This file makes that identification, and proves that the
identification is all the test needs.

Three results, in the order that matters:

1. **The accumulators, named.**  `EstLayout` says the exit memory's words are a
   `ℕ`-valued accumulator state, with the fit invariant.  From it,
   `Ahat_eq_toQ` / `Vhat_eq_toQ` turn `payloadBlock_memOf` into a statement
   about the *accumulators*: the two stored blocks are `wordList f base len`
   mapped through the fixed-point scaler — no residual freedom, nothing
   threaded beside the memory.
2. **`dAt` is one shared denominator.**  `dAt_eq_accum_div` reads the estimate
   as the difference of two accumulator words over a *single* scale, and
   `hitWord_eq_dAt` composes that with `hitWord_eq_ratTest` to prove that the
   word test the program actually executes, on the accumulator words, is
   exactly §7 step 7's `ℚ` test on `dAt`.  `dAt_of_getElem?` closes the loop
   from the other side: the `s`-th entries of the two stored lists determine
   `dAt s`, so «`dAt` is `V̂_s - Â_s`» is a theorem about the blocks.
3. **What the test consumes — the bin-sum seam, pinned.**  `rowTest_Ahat` shows
   the verdict is a function of the `dAt` list alone (`rowTest` depends on the
   pointwise differences, nothing else), and `rowTest_eq_binSum` turns that
   into the exact contract item 3's residual needs: *supply `binSum` with
   `∀ i < blockLen, dAt i = binSum i`, and the test on the payloads becomes the
   test on the bin sums.*  That is the whole of what the cross-estimate
   relation has to supply — and nothing else is consumed.
4. **The layout that can carry `n²` bits, written.**  `placeValue_scale` is the
   one-denominator identity for a multi-word estimate; the carry chain
   (`placeValueAt`, `placeValueAt_succ`, `mod_mul_split`, `sum_base_digits`,
   `placeValueAt_digits`) proves that base-`2^w` digits recover a numerator
   exactly; `payloadStride_mul_spec` sizes the block; and
   `placeValueAt_payloadStride` carries a full `fracBits`-bit numerator with no
   loss — the theorem the truncation below denies the one-word read.  Item 3's
   contract is restated on that layout (`WideLayout`, `WideBinSumAgrees`,
   `rowTest_eq_wideBinSum`) and the landed contract is proved to be its
   `stride = 1` instance (`wideBinSumAgrees_one_iff`), so the two items close on
   one seam rather than two.

## The finding that moves item 4 (do not skip this)

Item 3's shape «`dAt i` = the bin sum» is only well-posed if one word can carry
one estimate.  It cannot.  §6.2 asks for `n²` fractional bits while a word holds
`w = wordLength n x.bits` bits, and `abs_dAt_mul_lt` proves what that means
here: `|dAt i| · 2^fracBits` is a **single word's worth** of numerator.  So when
`fracBits ≥ w + 1`, which is what `fracBits = n²` means at every `n ≥ 2`,
`abs_dAt_lt_half` proves `|dAt i| < 1/2`, i.e. the test `1/2 ≤ |dAt i|` can
*never* fire.  The one-word-per-index reading of `Ahat`/`aAt`/`dAt` is therefore
a truncation, not a layout, at the paper's parameters.

The repair is item 4's shape, named here: an estimate at `fracBits` fractional
bits occupies `payloadStride w fracBits = ⌈fracBits/w⌉ + 1` words and its `ℚ`
value is the *place value* `placeValue m base stride fracBits s` (the base-`2^w`
sum of that estimate's words, over one shared `2^fracBits` scale).
`placeValue_one` proves the degenerate stride-1 instance *is* the module's
`aAt`/`dAt` reading, so the module's defs are the `stride = 1` case of the
layout rather than a competitor to it.  §8.5–8.7 write that layout: the scale
identity, the carry chain, the block sizing, the exactness theorem, and item 3's
bin-sum contract restated on it.  What remains for item 4 is the program's side —
the read loop must sum `stride` words per estimate before `aAt` is a wide
reading — which is named, with the rest of the residual, at the foot of this
file.

Statement-and-proof work on a leaf module: `Statement.lean`'s hashes are
untouched (`3dc6567e…34aa`), no built module's hash moves.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaPrelim
import SubsetSumL25.Row.KapilaTest
import SubsetSumL25.Row.KapilaLoop

set_option maxHeartbeats 800000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

variable {n : Nat} {x : Instance n}

/-! ### Layer 8.0 — the accumulators

The exit memory is `memOf`-shaped: cell `i` holds `BitVec.ofNat w (f i)`.  That
is the standing form every memory in this calculus has (`KapilaPrelim`), and
`f` is the phase's `ℕ`-valued state.  Naming it for a `PayloadConvention` is
what turns the word-level bridge (`payloadBlock_memOf`) into a claim about the
accumulators: the two payload blocks are `f` read at `baseA` / `baseV`, scaled.
-/

/-- **The exit memory's accumulators.**  `f` is the `ℕ`-valued state the exit
memory encodes, under the fit invariant that makes every word operation the
corresponding `ℕ` operation. -/
structure EstLayout (C : PayloadConvention n x) where
  /-- The `ℕ`-valued accumulator state. -/
  f : Nat → Nat
  /-- The standing fit invariant: every word fits a word. -/
  fit : ∀ i, f i < 2 ^ (wordLength n x.bits)
  /-- The exit memory *is* that state, cell for cell. -/
  mem_eq : C.mem = memOf (wordLength n x.bits) f

/-- Reading a word back to `ℕ` under fit — the step that removes `BitVec`. -/
theorem memOf_toNat {w : Nat} (f : Nat → Nat) (hfit : ∀ i, f i < 2 ^ w) (i : Nat) :
    (memOf w f i).toNat = f i := by
  show (BitVec.ofNat w (f i)).toNat = f i
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfit i)]

/-- **The stored alias block is an accumulator block.**  `payloadBlock_memOf`
was an agreement between a memory and a state function; here it is the claim
«the block `Ahat` is the accumulator list, scaled», which is the form the
multi-word accumulator obligation can be stated about. -/
theorem Ahat_eq_toQ (L : EstLayout C) :
    C.Ahat = (wordList L.f C.baseA C.blockLen).map (toQ C.fracBits) := by
  rw [PayloadConvention.Ahat, L.mem_eq,
    payloadBlock_memOf L.f L.fit C.fracBits C.baseA C.blockLen]

/-- The checksum block, the same way. -/
theorem Vhat_eq_toQ (L : EstLayout C) :
    C.Vhat = (wordList L.f C.baseV C.blockLen).map (toQ C.fracBits) := by
  rw [PayloadConvention.Vhat, L.mem_eq,
    payloadBlock_memOf L.f L.fit C.fracBits C.baseV C.blockLen]

/-! ### Layer 8.1 — `dAt` is a difference of accumulators

The estimate §7 step 7 compares is `V̂_s - Â_s`.  On the accumulators it is the
difference of two words over **one** scale, so the test is a claim about one
integer (the numerator difference) and one denominator, not about two
independently-rounded rationals.  That is the arithmetic relation item 3 asked
for, in the sharpest form the module's material supports.
-/

/-- **The estimate is the accumulator difference.** -/
theorem dAt_eq_accum (L : EstLayout C) (i : Nat) :
    C.dAt i = toQ C.fracBits (L.f (C.baseV + i)) - toQ C.fracBits (L.f (C.baseA + i)) := by
  unfold PayloadConvention.dAt PayloadConvention.vAt PayloadConvention.aAt toQ
  rw [L.mem_eq]
  simp only [memOf_toNat L.f L.fit]

/-- **One shared denominator.**  `dAt i` is the difference of the two accumulator
words divided by `2^fracBits`, a single scale for both operands, which is what
lets the comparison be done as an integer comparison (`hitWord_eq_ratTest`). -/
theorem dAt_eq_accum_div (L : EstLayout C) (i : Nat) :
    C.dAt i
      = (((L.f (C.baseV + i) : Nat) : ℚ) - ((L.f (C.baseA + i) : Nat) : ℚ))
          / (2 : ℚ) ^ C.fracBits := by
  rw [dAt_eq_accum L i, toQ, toQ, ← sub_div]

/-- The absolute value, over the same single denominator. -/
theorem abs_dAt_eq (L : EstLayout C) (i : Nat) :
    |C.dAt i|
      = |((L.f (C.baseV + i) : Nat) : ℚ) - ((L.f (C.baseA + i) : Nat) : ℚ)|
          / (2 : ℚ) ^ C.fracBits := by
  have hpos : (0 : ℚ) < (2 : ℚ) ^ C.fracBits := by positivity
  rw [dAt_eq_accum_div L i, abs_div]
  simp only [abs_of_pos hpos]

/-- **The program's word test is the paper's `ℚ` test on the accumulators.**
`hitWord` is what the instruction sequence computes (`KapilaLoop` §L3), and
`hitWord_eq_ratTest` says two words at scale `2^-fracBits` are compared against
`1/2`; this composes that with `dAt`'s accumulator reading, so the comparison is
about §7 step 7's estimate and not about a proxy. -/
theorem hitWord_eq_dAt (L : EstLayout C) (hf : 1 ≤ C.fracBits) (i : Nat) :
    hitWord (2 ^ (C.fracBits - 1)) (L.f (C.baseV + i)) (L.f (C.baseA + i)) = 1
      ↔ (1 / 2 : ℚ) ≤ |C.dAt i| := by
  rw [hitWord_eq_ratTest hf, dAt_eq_accum]
  rfl

/-! ### Layer 8.2 — `dAt` is the `s`-th entry difference of the stored lists

The other corner of the same relation: the two lists `KapilaTest` defines are
`List ℚ` values, and `dAt s` is their `s`-th entry difference, so «`dAt` is
`V̂_s - Â_s`» is a statement about the stored blocks rather than a definition
that bypassed them.
-/

theorem Ahat_getElem? (C : PayloadConvention n x) (i : Nat) :
    C.Ahat[i]? = if i < C.blockLen then some (C.aAt i) else none := by
  have hmap : C.Ahat = (List.range C.blockLen).map C.aAt := PayloadConvention.Ahat_eq_map C
  rw [hmap, List.getElem?_map]
  by_cases h : i < C.blockLen
  · rw [List.getElem?_range h]
    simp [h]
  · have h' : C.blockLen ≤ i := by omega
    rw [List.getElem?_eq_none (by simp [h'])]
    simp [h]

theorem Vhat_getElem? (C : PayloadConvention n x) (i : Nat) :
    C.Vhat[i]? = if i < C.blockLen then some (C.vAt i) else none := by
  have hmap : C.Vhat = (List.range C.blockLen).map C.vAt := PayloadConvention.Vhat_eq_map C
  rw [hmap, List.getElem?_map]
  by_cases h : i < C.blockLen
  · rw [List.getElem?_range h]
    simp [h]
  · have h' : C.blockLen ≤ i := by omega
    rw [List.getElem?_eq_none (by simp [h'])]
    simp [h]

/-- **The `s`-th entries of the two stored blocks determine `dAt s`.**  This is
the equation item 3's residual starts from: whatever the payloads are, the
quantity the test compares is their entrywise difference. -/
theorem dAt_of_getElem? (C : PayloadConvention n x) (i : Nat) {a v : ℚ}
    (hA : C.Ahat[i]? = some a) (hV : C.Vhat[i]? = some v) :
    C.dAt i = v - a := by
  rw [Ahat_getElem?] at hA
  rw [Vhat_getElem?] at hV
  by_cases h : i < C.blockLen
  · rw [if_pos h] at hA hV
    simp only [Option.some.injEq] at hA hV
    rw [← hA, ← hV]
    exact PayloadConvention.dAt_def C i
  · rw [if_neg h] at hA
    simp at hA

/-! ### Layer 8.3 — the test consumes the `dAt` list, and nothing else

Item 3's residual name was «`V̂_s - Â_s` is the bin sum».  These results pin
what that obligation has to supply and how little else the verdict reads:
`rowTest` factors through the pointwise differences, and the bin-sum identity is
*sufficient* on its own.
-/

/-- A list zipped with itself is the diagonal map: the last step from
`KapilaLoop`'s `zipWith_map_map'` (which splits the two maps) to an index-wise
`map`. -/
theorem zipWith_diag {α β : Type} (F : α → α → β) (l : List α) :
    l.zipWith F l = l.map (fun x => F x x) := by
  induction l with
  | nil => rfl
  | cons a as _ => simp [List.zipWith]

/-- **The verdict reads the `dAt` list.**  §7 step 7's test on the two stored
payloads is the same test applied to the per-index estimate differences, so the
`ℚ` accumulator layout does not have to be re-checked at the test's level. -/
theorem rowTest_Ahat (C : PayloadConvention n x) :
    Routines.rowTest C.Ahat C.Vhat
      = ((List.range C.blockLen).map fun i => decide ((1 / 2 : ℚ) ≤ |C.dAt i|)).any id := by
  rw [Routines.rowTest, PayloadConvention.Ahat_eq_map, PayloadConvention.Vhat_eq_map,
    zipWith_map_map', zipWith_diag]
  rfl

/-- **The cross-estimate relation, as a predicate.**  `binSum` is whatever object
realizes «the difference of the two estimates at `s` is the bin sum», the
paper's own quantity.  Nothing here produces it: the tree has no bin object, and
neither landed leg pins one (alias certifies `Â`'s support, checksum `V̂`'s
magnitude).  What the predicate fixes is the *exact* thing such a construction
must prove. -/
def BinSumAgrees (C : PayloadConvention n x) (binSum : Nat → ℚ) : Prop :=
  ∀ i, i < C.blockLen → C.dAt i = binSum i

/-- **The bin sums suffice.**  Given the pointwise identity, the verdict on the
payloads *is* the test on the bin sums, so item 3's residual is exactly one
equation per index, and no further property of `dAt` (or of the payloads) is
consumed by `LeafTest`'s test. -/
theorem rowTest_eq_binSum (C : PayloadConvention n x) (binSum : Nat → ℚ)
    (h : BinSumAgrees C binSum) :
    Routines.rowTest C.Ahat C.Vhat
      = ((List.range C.blockLen).map fun i => decide ((1 / 2 : ℚ) ≤ |binSum i|)).any id := by
  rw [rowTest_Ahat]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [h i hi]

/-! ### Layer 8.4 — the one-word reading is a truncation, and item 4's shape

A word holds `w = wordLength n x.bits` bits; §6.2 asks for `fracBits = n²`
fractional bits.  The two are not the same size, and the module's per-index read
inherits the word's worth of numerator, which is what the next two theorems make
exact.
-/

/-- An accumulator word, as a rational, sits below the word modulus.  Stated
separately so that the cast is elaborated once, at the section's own n and x. -/
theorem est_lt_two_pow {C : PayloadConvention n x} (L : EstLayout C) (j : Nat) :
    ((L.f j : Nat) : ℚ) < (2 : ℚ) ^ (wordLength n x.bits) := by
  have h := Nat.cast_lt (α := ℚ).mpr (L.fit j)
  push_cast at h
  exact h

/-- **The estimate's numerator fits a single word.**  `|dAt i| · 2^fracBits` is
the absolute difference of two accumulator words, hence `< 2^w`: the payload read
at a per-index address cannot carry more than one word of numerator, whatever
`fracBits` is set to. -/
theorem abs_dAt_mul_lt {C : PayloadConvention n x} (L : EstLayout C) (i : Nat) :
    |C.dAt i| * (2 : ℚ) ^ C.fracBits < (2 : ℚ) ^ (wordLength n x.bits) := by
  have hpos : (0 : ℚ) < (2 : ℚ) ^ C.fracBits := by positivity
  rw [abs_dAt_eq L i, div_mul_cancel₀ _ (ne_of_gt hpos)]
  have hv : ((L.f (C.baseV + i) : Nat) : ℚ) < (2 : ℚ) ^ (wordLength n x.bits) :=
    est_lt_two_pow L (C.baseV + i)
  have ha : ((L.f (C.baseA + i) : Nat) : ℚ) < (2 : ℚ) ^ (wordLength n x.bits) :=
    est_lt_two_pow L (C.baseA + i)
  have hv0 : (0 : ℚ) ≤ ((L.f (C.baseV + i) : Nat) : ℚ) := by positivity
  have ha0 : (0 : ℚ) ≤ ((L.f (C.baseA + i) : Nat) : ℚ) := by positivity
  rw [abs_lt]
  constructor <;> linarith

/-- **At `n²` fractional bits the one-word test cannot fire.**  If `fracBits ≥
w + 1`, the regime `fracBits = n²` with `w = O(n + b)` always lands in, then
every estimate difference is below `1/2`, so `hitWord` computes `0` and §7 step
7's loop can never take its hit.  The one-word-per-index reading of
`Ahat`/`aAt`/`dAt` is therefore a **truncation, not a layout**, at the paper's
parameters; the fix is the multi-word place-value reading below. -/
theorem abs_dAt_lt_half {C : PayloadConvention n x} (L : EstLayout C)
    (h : wordLength n x.bits + 1 ≤ C.fracBits)
    (i : Nat) : |C.dAt i| < 1 / 2 := by
  have hpos : (0 : ℚ) < (2 : ℚ) ^ C.fracBits := by positivity
  have hw : wordLength n x.bits ≤ C.fracBits - 1 := by omega
  have hpow : (2 : ℚ) ^ (wordLength n x.bits) ≤ (2 : ℚ) ^ (C.fracBits - 1) :=
    pow_le_pow_right₀ (by norm_num) hw
  have h1 : |C.dAt i| * (2 : ℚ) ^ C.fracBits < (2 : ℚ) ^ (C.fracBits - 1) :=
    lt_of_lt_of_le (abs_dAt_mul_lt L i) hpow
  have hhalf : (1 / 2 : ℚ) = (2 : ℚ) ^ (C.fracBits - 1) / (2 : ℚ) ^ C.fracBits := by
    have hf : C.fracBits = (C.fracBits - 1) + 1 := by omega
    have h2 : (2 : ℚ) ^ C.fracBits = (2 : ℚ) ^ (C.fracBits - 1) * 2 := by
      conv_lhs => rw [hf]
      rw [pow_succ]
    have hp : (0 : ℚ) < (2 : ℚ) ^ (C.fracBits - 1) := by positivity
    rw [h2, div_mul_eq_div_div, div_self (ne_of_gt hp)]
  rw [hhalf, lt_div_iff₀ hpos]
  exact h1

/-- **Words per estimate at the paper's parameters**: §6.2's `⌈n²/w⌉ + 1`, i.e.
the estimate's place-value digits plus the carry word. -/
def payloadStride (w fracBits : Nat) : Nat := (fracBits + w - 1) / w + 1

/-- **The place-value reading of an estimate.**  Estimate `s` occupies the
`stride` words at `base + s * stride`, read little-endian as a base-`2^w` number
over the single scale `2^-fracBits`.  This is the object §6.2's `n²` fractional
bits actually require, and the shape item 3's bin-sum identity must be stated
about once item 4's layout exists. -/
def placeValue {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) : ℚ :=
  (((List.range stride).map fun j =>
      ((m (base + s * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum)
    / (2 : ℚ) ^ fracBits

/-- **The module's per-index read is the stride-1 instance.**  So `aAt`/`dAt` are
the degenerate case of the place-value layout rather than a competitor to it:
when one word suffices, the layout's value at estimate `s` is exactly the entry
`aAt s` the convention reads. -/
theorem placeValue_one {w : Nat} (m : Nat → BitVec w) (base fracBits s : Nat) :
    placeValue m base 1 fracBits s
      = ((m (base + s)).toNat : ℚ) / (2 : ℚ) ^ fracBits := by
  simp [placeValue]


/-! ### Layer 8.5 — the place value, scaled

`placeValue_one` settles the degenerate case; these settle the general one.  The
first theorem is the identity that makes a multi-word estimate comparable at all:
multiplying the place value by `2^fracBits` clears the *single* shared
denominator and leaves the base-`2^w` numerator, so two estimates at the same
`fracBits` compare as integers on one scale.  The second makes the address
explicit, because the carry chain changes the number of words per estimate and
therefore the address of every estimate after the first.
-/

/-- The place value is nonnegative: it is a sum of nonnegative terms over a
positive denominator. -/
theorem placeValue_nonneg {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) :
    0 ≤ placeValue m base stride fracBits s := by
  unfold placeValue
  have hpos : (0 : ℚ) ≤ (2 : ℚ) ^ fracBits := by positivity
  apply div_nonneg _ hpos
  apply List.sum_nonneg
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  have : (0 : ℚ) ≤ ((m (base + s * stride + j)).toNat : ℚ) := by positivity
  have : (0 : ℚ) ≤ (2 : ℚ) ^ (w * j) := by positivity
  positivity

/-- **The one-denominator identity.**  An estimate's place value, multiplied by
the single shared scale `2^fracBits`, is exactly the base-`2^w` numerator of its
`stride` words — no rounding, no second denominator, nothing dropped.  This is
what `abs_dAt_mul_lt` denies the one-word reading: there the numerator is bounded
by `2^w` whatever `fracBits` is; here it is the *whole* stride-`k` sum. -/
theorem placeValue_scale {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) :
    placeValue m base stride fracBits s * (2 : ℚ) ^ fracBits
      = ((List.range stride).map fun j =>
          ((m (base + s * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum := by
  unfold placeValue
  exact div_mul_cancel₀ _ (ne_of_gt (by positivity))

/-- **The place value at an explicit address.**  `placeValue` addresses estimate
`s` at `base + s * stride`; the carry chain below appends words at a fixed
address, so it needs the address as a parameter and not as a function of `s`.
The two readings agree by definition. -/
def placeValueAt {w : Nat} (m : Nat → BitVec w) (addr stride fracBits : Nat) : ℚ :=
  (((List.range stride).map fun j => ((m (addr + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum)
    / (2 : ℚ) ^ fracBits

/-- **`placeValue` is `placeValueAt` at the estimate's own address.** -/
theorem placeValue_eq_placeValueAt {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) :
    placeValue m base stride fracBits s = placeValueAt m (base + s * stride) stride fracBits :=
  rfl

/-- The empty block reads zero — the carry chain's base case. -/
@[simp] theorem placeValueAt_zero {w : Nat} (m : Nat → BitVec w) (addr fracBits : Nat) :
    placeValueAt m addr 0 fracBits = 0 := by
  simp [placeValueAt]

/-! ### Layer 8.6 — the carry chain over `payloadStride` words

A multi-word estimate is filled one word at a time, and each word lands at its own
place value: word `j` contributes `word_j · 2^{w·j}` to the numerator, over the
one shared `2^fracBits`.  That is the chain.  Nothing here propagates carries
explicitly, because in base `2^w` the carries are *the meaning of the digits*: the
numeric core (`mod_mul_split`, `sum_base_digits`) proves that reading the digits
of a numerator recovers the numerator exactly, which is the carry chain's whole
content and the exact opposite of the truncation `abs_dAt_lt_half` proved.

`payloadStride_mul_spec` then fixes how many digits are needed: `⌈fracBits/w⌉ + 1`
words hold `fracBits + w` bits, so a numerator of `fracBits` bits is carried with
a full word of headroom — the `+ 1` is the carry word, not padding.
-/

/-- **Base decomposition.**  `N % (a·b)` split into its low part `N % a` and the
carry digit `(N / a) % b` at place `a`.  This is the only arithmetic fact the
carry chain needs, and it holds for every `a, b > 0`. -/
theorem mod_mul_split (N a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    N % (a * b) = N % a + (N / a % b) * a := by
  have hN : N = (a * b) * (N / (a * b)) + N % (a * b) := (Nat.div_add_mod N (a * b)).symm
  set r := N % (a * b) with hr
  have hlt : r < a * b := Nat.mod_lt _ (by positivity)
  have h1 : (a * b) * (N / (a * b)) + r = r + a * (b * (N / (a * b))) := by
    rw [Nat.mul_assoc a b (N / (a * b)), Nat.add_comm]
  have hdiv : N / a = r / a + b * (N / (a * b)) := by
    conv_lhs => rw [hN]
    rw [h1, Nat.add_mul_div_left _ _ ha]
  have hmodA : N % a = r % a := by
    conv_lhs => rw [hN]
    rw [Nat.mul_assoc a b (N / (a * b))]
    exact Nat.mul_add_mod_self_left a (b * (N / (a * b))) r
  have hmodB : N / a % b = r / a := by
    rw [hdiv, Nat.add_mul_mod_self_left (r / a) b (N / (a * b)), Nat.mod_eq_of_lt]
    exact Nat.div_lt_of_lt_mul hlt
  have hfin : r = r % a + (r / a) * a := by
    have h := Nat.div_add_mod r a
    rw [Nat.mul_comm a (r / a), Nat.add_comm] at h
    exact h.symm
  calc N % (a * b) = r := hr.symm
    _ = r % a + (r / a) * a := hfin
    _ = N % a + (N / a % b) * a := by rw [← hmodA, ← hmodB]

/-- **The digits of a numerator recover it.**  Reading `stride` base-`2^w` digits
`N / 2^{w·j} % 2^w` and placing them at `2^{w·j}` sums to `N` modulo
`2^{w·stride}` — the losslessness the one-word reading lacks. -/
theorem sum_base_digits (N w stride : Nat) :
    ((List.range stride).map fun j => (N / 2 ^ (w * j) % 2 ^ w) * 2 ^ (w * j)).sum
      = N % 2 ^ (w * stride) := by
  induction stride with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [List.sum_range_succ, ih, Nat.mul_succ, Nat.pow_add]
    exact (mod_mul_split N (2 ^ (w * k)) (2 ^ w) (by positivity) (by positivity)).symm

/-- **The carry chain's step.**  Appending one word at address `addr + stride`
adds exactly its place value `word · 2^{w·stride}` to the numerator over the one
shared denominator.  So a stride-`k` block is built word by word, and the block's
value is the sum of its words' places — no truncation at any step. -/
theorem placeValueAt_succ {w : Nat} (m : Nat → BitVec w) (addr stride fracBits : Nat) :
    placeValueAt m addr (stride + 1) fracBits
      = placeValueAt m addr stride fracBits
        + ((m (addr + stride)).toNat : ℚ) * (2 : ℚ) ^ (w * stride) / (2 : ℚ) ^ fracBits := by
  unfold placeValueAt
  rw [List.sum_range_succ, add_div]

/-- **`payloadStride` words hold `fracBits + w` bits.**  The first conjunct is the
fit that makes the digits lossless; the second is the headroom the `+ 1` word
buys, which is why it is a carry word rather than padding. -/
theorem payloadStride_mul_spec {w : Nat} (hw : 0 < w) (fracBits : Nat) :
    fracBits ≤ w * payloadStride w fracBits
      ∧ fracBits + w ≤ w * payloadStride w fracBits := by
  have h := Nat.div_add_mod (fracBits + w - 1) w
  have hlt : (fracBits + w - 1) % w < w := Nat.mod_lt _ hw
  have h1 : fracBits ≤ w * ((fracBits + w - 1) / w) := by omega
  have h2 : w * payloadStride w fracBits = w * ((fracBits + w - 1) / w) + w := by
    unfold payloadStride
    rw [Nat.mul_succ]
  constructor
  · rw [h2]; omega
  · rw [h2]; omega

/-- **The digits of a block read back as the block's numerator.**  With the
memory's words holding `N`'s base-`2^w` digits, the place value is `N` over the
shared scale — exact, because `sum_base_digits` is exact. -/
theorem placeValueAt_digits {w : Nat} (N addr stride fracBits : Nat) (m : Nat → BitVec w)
    (hm : ∀ j, j < stride → (m (addr + j)).toNat = N / 2 ^ (w * j) % 2 ^ w) :
    placeValueAt m addr stride fracBits
      = ((N % 2 ^ (w * stride) : Nat) : ℚ) / (2 : ℚ) ^ fracBits := by
  have hcast : ∀ (l : List Nat) (g : Nat → Nat),
      (l.map fun x => ((g x : Nat) : ℚ)).sum = (((l.map g).sum : Nat) : ℚ) := by
    intro l
    induction l with
    | nil => intro g; simp
    | cons a as ih => intro g; simp [ih, Nat.cast_add]
  have hterm : ∀ j, ((m (addr + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)
      = ((((m (addr + j)).toNat) * 2 ^ (w * j) : Nat) : ℚ) := by
    intro j
    push_cast
    ring
  have hsub : ∀ j, j < stride →
      (((m (addr + j)).toNat) * 2 ^ (w * j) : Nat)
        = (N / 2 ^ (w * j) % 2 ^ w) * 2 ^ (w * j) := by
    intro j hj
    rw [hm j hj]
  have hnat : ((List.range stride).map
      fun j => ((m (addr + j)).toNat) * 2 ^ (w * j)).sum = N % 2 ^ (w * stride) := by
    rw [List.map_congr_left (fun j hj => hsub j (List.mem_range.mp hj))]
    exact sum_base_digits N w stride
  unfold placeValueAt
  rw [List.map_congr_left (fun j _ => hterm j),
    hcast (List.range stride) (fun j => ((m (addr + j)).toNat) * 2 ^ (w * j)), hnat]

/-- **A `payloadStride` block carries a `fracBits`-bit numerator exactly.**  This
is the layout that replaces the truncation: `abs_dAt_lt_half` proved that a single
word at `fracBits ≥ w + 1` forces every estimate below `1/2`; here a numerator of
`fracBits` bits — anything in `[0, 1)` on the shared scale — is carried with no
loss and a full word of headroom left for carries. -/
theorem placeValueAt_payloadStride {w fracBits N addr : Nat} (hw : 0 < w) (hN : N < 2 ^ fracBits)
    (m : Nat → BitVec w)
    (hm : ∀ j, j < payloadStride w fracBits → (m (addr + j)).toNat = N / 2 ^ (w * j) % 2 ^ w) :
    placeValueAt m addr (payloadStride w fracBits) fracBits
      = ((N : Nat) : ℚ) / (2 : ℚ) ^ fracBits := by
  have hlt : N < 2 ^ (w * payloadStride w fracBits) := by
    have h1 : fracBits ≤ w * payloadStride w fracBits := (payloadStride_mul_spec hw fracBits).1
    have h2 : (2 : Nat) ^ fracBits ≤ 2 ^ (w * payloadStride w fracBits) :=
      Nat.pow_le_pow_right (by norm_num) h1
    omega
  rw [placeValueAt_digits N addr _ fracBits m hm, Nat.mod_eq_of_lt hlt]

/-- **The `s`-indexed form, at `s = 0`.**  `placeValue` reads estimate `s` at
`base + s * stride`, so the address-explicit exactness theorem transfers to it
verbatim; the general `s` is the same theorem at address `base + s * stride`, and
this representative case is stated so the `placeValue` vocabulary the contract
above uses is known to carry a full numerator too. -/
theorem placeValue_payloadStride {w fracBits N base : Nat} (hw : 0 < w) (hN : N < 2 ^ fracBits)
    (m : Nat → BitVec w)
    (hm : ∀ j, j < payloadStride w fracBits →
      (m (base + j)).toNat = N / 2 ^ (w * j) % 2 ^ w) :
    placeValue m base (payloadStride w fracBits) fracBits 0 = ((N : Nat) : ℚ) / (2 : ℚ) ^ fracBits := by
  have h0 : base + 0 * payloadStride w fracBits = base := by omega
  rw [placeValue_eq_placeValueAt, h0]
  exact placeValueAt_payloadStride hw hN m hm

/-! ### Layer 8.7 — the bin-sum contract, restated about the real layout

Layer 8.3 stated `BinSumAgrees` about `dAt`, i.e. about the *stored lists*, which
is the only thing the landed `PayloadConvention` gives: one word per index.  At
`fracBits ≥ w + 1` those lists are truncations (§8.4), so a contract phrased on
them cannot be the cross-estimate relation the paper needs.  These results move
the contract onto the layout that can carry the estimates, and prove that the old
contract is its `stride = 1` instance — so nothing landed is displaced, only
generalized.

The residual after this layer is a *fact about the program*, not about `ℚ`: the
instruction sequence reads `base + i` (`PayloadConvention.aAt`), i.e. one word per
index, so a stride-`k` payload needs the read loop to sum `k` words per estimate
before `aAt` can be the wide reading.  That is item 4's application seam, and it
is named rather than assumed.
-/

/-- The `i`-th entry of a `range`-indexed map. -/
theorem getElem?_map_range {α : Type} (F : Nat → α) (len i : Nat) (hi : i < len) :
    ((List.range len).map F)[i]? = some (F i) := by
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **`dAt` is read off any per-index presentation of the two blocks.**  The
landed form (`Ahat_getElem?`) is the case `F = aAt`; the wide layout supplies
place values instead, so the estimate is their difference. -/
theorem dAt_eq_of_map {C : PayloadConvention n x} {F G : Nat → ℚ}
    (hA : C.Ahat = (List.range C.blockLen).map F)
    (hV : C.Vhat = (List.range C.blockLen).map G) {i : Nat} (hi : i < C.blockLen) :
    C.dAt i = G i - F i := by
  refine dAt_of_getElem? C i ?_ ?_
  · rw [hA]; exact getElem?_map_range F C.blockLen i hi
  · rw [hV]; exact getElem?_map_range G C.blockLen i hi

/-- **The verdict reads any per-index presentation of the blocks.**  `rowTest_Ahat`
is the case `F = aAt`, `G = vAt`. -/
theorem rowTest_eq_map {C : PayloadConvention n x} {F G : Nat → ℚ}
    (hA : C.Ahat = (List.range C.blockLen).map F)
    (hV : C.Vhat = (List.range C.blockLen).map G) :
    Routines.rowTest C.Ahat C.Vhat
      = ((List.range C.blockLen).map fun i => decide ((1 / 2 : ℚ) ≤ |G i - F i|)).any id := by
  rw [Routines.rowTest, hA, hV, zipWith_map_map', zipWith_diag]

/-- **The wide (stride-`k`) layout.**  The two stored blocks are the place-value
readings of a multi-word accumulator memory: estimate `s` of `Â` occupies the
`stride` words at `baseA + s * stride`, and likewise for `V̂`.  This is what
`fracBits = n²` requires and what one word per index cannot provide. -/
structure WideLayout {w : Nat} (C : PayloadConvention n x) (m : Nat → BitVec w) (stride : Nat) :
    Prop where
  /-- The alias block is the place-value readings of the wide memory. -/
  Ahat_eq : C.Ahat = (List.range C.blockLen).map (placeValue m C.baseA stride C.fracBits)
  /-- The checksum block is too. -/
  Vhat_eq : C.Vhat = (List.range C.blockLen).map (placeValue m C.baseV stride C.fracBits)

/-- **The cross-estimate relation, stated about the wide layout.**  Same content
as `BinSumAgrees` — one equation per index, nothing else — but the left side is
the difference of two *multi-word place values*, which is the quantity whose
bin-sum identity the paper asserts. -/
def WideBinSumAgrees {w : Nat} (C : PayloadConvention n x) (m : Nat → BitVec w) (stride : Nat)
    (binSum : Nat → ℚ) : Prop :=
  ∀ i, i < C.blockLen →
    placeValue m C.baseV stride C.fracBits i - placeValue m C.baseA stride C.fracBits i = binSum i

/-- **The wide place values determine `dAt`.**  So the estimate the test compares
*is* the difference of the two multi-word readings, not a proxy for it. -/
theorem dAt_eq_widePlaceValue {C : PayloadConvention n x} {w : Nat} {m : Nat → BitVec w}
    {stride : Nat} (L : WideLayout C m stride) {i : Nat} (hi : i < C.blockLen) :
    C.dAt i
      = placeValue m C.baseV stride C.fracBits i - placeValue m C.baseA stride C.fracBits i :=
  dAt_eq_of_map L.Ahat_eq L.Vhat_eq hi

/-- **The bin sums suffice, on the real layout.**  Item 3's residual contract, now
stated about `placeValue`: supply the pointwise identity between two multi-word
place values and the bin sums, and §7 step 7's verdict on the payloads *is* the
test on the bin sums.  Nothing else about `dAt`, the payloads, or the memory is
consumed. -/
theorem rowTest_eq_wideBinSum (C : PayloadConvention n x) {w : Nat} (m : Nat → BitVec w)
    {stride : Nat} (L : WideLayout C m stride) (binSum : Nat → ℚ)
    (h : WideBinSumAgrees C m stride binSum) :
    Routines.rowTest C.Ahat C.Vhat
      = ((List.range C.blockLen).map fun i => decide ((1 / 2 : ℚ) ≤ |binSum i|)).any id := by
  rw [rowTest_eq_map L.Ahat_eq L.Vhat_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [h i hi]

/-- **The wide reading at stride 1 is the module's `dAt`**, stated separately so
the bridge above reads as the substitution it is: the two place values *are* the
two accumulator words, scaled. -/
theorem dAt_eq_placeValue_one {C : PayloadConvention n x} (L : EstLayout C) (i : Nat) :
    C.dAt i
      = placeValue (memOf (wordLength n x.bits) L.f) C.baseV 1 C.fracBits i
        - placeValue (memOf (wordLength n x.bits) L.f) C.baseA 1 C.fracBits i := by
  rw [dAt_eq_accum L i, placeValue_one, placeValue_one, memOf_toNat L.f L.fit,
    memOf_toNat L.f L.fit]
  unfold toQ
  rfl

/-- **Item 3's landed contract *is* the wide contract at `stride = 1`.**  On the
module's own memory the wide place value at stride one is exactly what
`aAt`/`vAt` read (`placeValue_one`, `dAt_eq_placeValue_one`), so `BinSumAgrees`
about `dAt` and `WideBinSumAgrees` at stride one are the *same* statement — both
directions.  The restatement is therefore a strict generalization: no landed
result is displaced, and the wide form holds in the regime the paper actually
runs in (`fracBits = n² ≥ w + 1`, where `abs_dAt_lt_half` forbids the narrow
one). -/
theorem wideBinSumAgrees_one_iff {C : PayloadConvention n x} (L : EstLayout C)
    {binSum : Nat → ℚ} :
    WideBinSumAgrees C (memOf (wordLength n x.bits) L.f) 1 binSum ↔ BinSumAgrees C binSum := by
  constructor
  · intro h i hi
    rw [dAt_eq_placeValue_one L i]
    exact h i hi
  · intro h i hi
    rw [← dAt_eq_placeValue_one L i]
    exact h i hi

/-! ### The named residual, stated where the next mind will find it

`LeafTest`'s four obligations, with what this file does and does not do to each:

1. **The payload convention — LANDED** (`KapilaTest`).
2. **The scan's loop rules — NOT STARTED** (unchanged; `KapilaLoop`'s cost work
   is the charge, not the loop).
3. **The estimates' arithmetic relation — LANDED, and restated on the layout the
   parameters actually allow.**  Proved: the stored blocks *are* the accumulator
   blocks (`Ahat_eq_toQ`/`Vhat_eq_toQ`); `dAt` is their difference over one
   denominator (`dAt_eq_accum_div`), equals the `s`-th entry difference of the
   stored lists (`dAt_of_getElem?`), and the program's word test on the
   accumulators is §7 step 7's `ℚ` test (`hitWord_eq_dAt`).  The verdict reads
   nothing but the `dAt` list (`rowTest_Ahat`).  The bin-sum identity is
   *sufficient* on its own, in two forms: on the stored lists
   (`rowTest_eq_binSum`, `BinSumAgrees`) and — this round — on the multi-word
   place values (`rowTest_eq_wideBinSum`, `WideLayout` + `WideBinSumAgrees`,
   with `dAt_eq_widePlaceValue` naming `dAt` as the difference of two place
   values).  The landed form is proved to be the wide contract's `stride = 1`
   instance (`dAt_eq_placeValue_one`, `wideBinSumAgrees_one_iff`), so the
   restatement generalizes rather than displaces it.  **Not produced, and not
   producible here:** the bin sums themselves — see (ii) below.
4. **The multi-word accumulator — LAYOUT WRITTEN, APPLICATION SEAM NAMED.**
   The limit is proved rather than lamented: at `fracBits ≥ w + 1` the single-word
   reading forces every difference below `1/2` (`abs_dAt_lt_half`), so no
   one-word layout can carry §6.2's estimates.  The reading that can is now
   *written and proved*: `placeValue_scale` (one shared denominator, the whole
   stride-`k` numerator); the carry chain — `placeValueAt` (explicit address),
   `placeValueAt_succ` (each appended word lands at its own place), `mod_mul_split`
   and `sum_base_digits` (base-`2^w` digits recover the numerator exactly — the
   algebraic content of «carry»), `placeValueAt_digits` (a block of digits reads
   back as its numerator); `payloadStride_mul_spec` (the `⌈·⌉ + 1` stride holds
   `fracBits + w` bits, so the extra word is a full word of carry headroom); and
   `placeValueAt_payloadStride` — a `fracBits`-bit numerator is carried **exactly**
   by a `payloadStride` block, which is the theorem the truncation denied.

What remains, enumerated rather than implied:

* (i) **The read loop's stride arithmetic — the application seam.**  `aAt` reads
  `C.mem (C.baseA + i)`: one word per index.  A stride-`k` payload needs the
  program to sum `k` words per estimate (and to address estimate `s` at
  `base + s * stride`) before `aAt` *is* a wide reading.  That is `KapilaLoop`'s
  instruction sequence, not this module's arithmetic, and nothing here touches it.
* (ii) **The bin sums themselves.**  `BinSumAgrees`/`WideBinSumAgrees` are
  contracts, not constructions: no bin object exists in the tree and neither
  landed leg pins one (alias certifies `Â`'s support, checksum `V̂`'s magnitude).
* (iii) **The program-entry reach premise** — §7 step 7's loop is actually
  entered.  Named in `KapilaLoop`/`KapilaTest`'s residual; untouched here.
* (iv) **`KapilaAlgo.cost` and `D7.agrees`'s step horizon** — untouched by
  instruction.  Recorded here so the wide layout is not read as cost-neutral: a
  stride-`k` read costs `k` words per estimate instead of one (plus the
  accumulation), so if (i) is ever written the charge must be re-measured rather
  than inherited.

`Statement.lean`'s hashes are untouched (`3dc6567e…34aa`): this module adds
names only, and it is a leaf of the import DAG. -/

end SubsetSumL25.Row
