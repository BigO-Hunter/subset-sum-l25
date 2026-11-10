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
layout rather than a competitor to it.  What remains for item 4 is the word
arithmetic that fills a stride-`k` block and its carry chain; item 3's bin-sum
identity must be stated about `placeValue`, which is why the two items are one
seam and not two.

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

/-! ### The named residual, stated where the next mind will find it

`LeafTest`'s four obligations, with what this file does and does not do to each:

1. **The payload convention — LANDED** (`KapilaTest`).
2. **The scan's loop rules — NOT STARTED** (unchanged; `KapilaLoop`'s cost work
   is the charge, not the loop).
3. **The estimates' arithmetic relation — LANDED as far as the tree carries it,
   and with its limit proved.**  Proved: the stored blocks *are* the accumulator
   blocks (`Ahat_eq_toQ`/`Vhat_eq_toQ`); `dAt` is their difference over one
   denominator (`dAt_eq_accum_div`), equals the `s`-th entry difference of the
   stored lists (`dAt_of_getElem?`), and the program's word test on the
   accumulators is §7 step 7's `ℚ` test (`hitWord_eq_dAt`).  The verdict reads
   nothing but the `dAt` list (`rowTest_Ahat`), and the bin-sum identity is
   *sufficient* on its own (`rowTest_eq_binSum`).  **Not produced, and not
   producible here:** the bin sums themselves, since no bin object exists in the
   tree and neither landed leg pins one.  `BinSumAgrees` is that obligation's
   exact shape.
4. **The multi-word accumulator — SHAPE NAMED, LAYOUT NOT WRITTEN.**  The limit
   is proved rather than lamented: at `fracBits ≥ w + 1` the single-word reading
   forces every difference below `1/2` (`abs_dAt_lt_half`), so no one-word
   layout can carry §6.2's estimates.  The reading that can is `placeValue` at
   stride `payloadStride w fracBits`, whose stride-1 instance is the module's
   own `aAt` (`placeValue_one`).  What is left is the word arithmetic that fills
   a stride-`k` block and its carry chain, and it now has a named target object
   instead of an address one cannot compute.

`Statement.lean`'s hashes are untouched (`3dc6567e…34aa`): this module adds
names only, and it is a leaf of the import DAG. -/

end SubsetSumL25.Row
