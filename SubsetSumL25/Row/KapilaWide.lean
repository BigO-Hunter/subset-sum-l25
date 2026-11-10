/-
`KapilaEstimate`'s residual (i) — **the stride-`k` block reader**, and the verdict
the reader forces on the loop's read.

Why this file exists.  `KapilaEstimate` closed the *arithmetic* side of items 3
and 4: `placeValue`/`placeValueAt` read a multi-word estimate as one base-`2^w`
numerator over one shared `2^fracBits`, the carry chain is exact
(`sum_base_digits`, `placeValueAt_payloadStride`), and the bin-sum contract is
restated about those readings (`WideLayout`, `WideBinSumAgrees`,
`rowTest_eq_wideBinSum`, with `dAt_eq_widePlaceValue` naming `dAt` as the
difference of two place values).  What it left open was that the *program* reads
one word per index: `KapilaLoop`'s `wordList`/`memOf` are stride-1 shapes, so
`aAt` is a one-word read and `dAt_eq_widePlaceValue` has nothing to apply to.
This module builds the stride-general reader, wires it into the loop's arithmetic
at the exact granularity the loop consumes, and then reports what the wiring
shows — including one obstruction that changes the shape of the remaining work.

1. **The stride-`k` block reader, with its own induction** (§W1).  `numAt` is
   `placeValueAt`'s numerator in `ℕ` form (`Σ_{j<stride} f (addr+j)·2^{w·j}`), and
   `numBlock` is `wordList`'s stride-general sibling: estimate `s` occupies the
   `stride` words at `base + s·stride`.  Both carry their own step rules
   (`numAt_succ`, `numBlock_succ` — the second is the loop's address advance) and
   the degenerate case is *proved equal to the landed reader*
   (`numBlock_one_eq_wordList`), so nothing landed is displaced.
2. **The reader is the place value** (§W2).  `numAt_eq_placeValueAt_scale`
   multiplies out: the integer the reader accumulates, over the one shared scale,
   **is** `placeValueAt`.  `placeValue_eq_scale_numAt` is the same statement in
   the direction the layout consumes, and `wideLayout_of_numBlock` turns a
   convention whose payload blocks are the *scaled reader* into a `WideLayout` —
   after which `dAt_eq_widePlaceValue` applies (`dAt_eq_reader`).  That is what
   «so `aAt` becomes the wide reading» means, made mechanical.
3. **The loop's step at stride `k`, and the exit fold** (§W4).
   `hitCount_numBlock_step` is one iteration's arithmetic — the head pair at
   `base + j·stride`, the tail re-based at `base + (j+1)·stride` — i.e. `stride`
   where `scan_loop` writes `1`.  `hitCount_numBlock_eq_sum` is the exit fold.
   `wideExit_eq_rowTest` then says the loop's `decide (0 < ·)` accumulator *is*
   `rowTest` on the two payload blocks, and `wideExit_eq_binSum` composes that
   with `rowTest_eq_wideBinSum`, leaving item (ii) — the bin sums themselves — as
   the only remaining input.
4. **The obstruction** (§W3), and it is the load-bearing negative result:
   `numAt_not_word` proves that at `stride ≥ 2` with a nonzero top digit the
   reader's value **exceeds `2^w`**, so it is not word-resident (`numAt_one_lt`
   is the contrast: the stride-1 read always fits — which is exactly why
   `wordList`/`memOf` were stride-1 shapes).  The consequence is not a missing
   lemma but a design fact: "the loop's per-iteration read becomes the k-word
   summing read" **cannot be implemented in the `BitVec w` state**.  The digits
   fit; their sum does not.  So (i) is not a read to be widened — it is the
   *comparison* that must be re-shaped (a top-down digit walk, or a multi-word
   output with its own carry chain), and `hitWord`'s single-cell form cannot host
   it.  Stated as a theorem rather than a caveat, in the same spirit as
   `abs_dAt_lt_half` denying the one-word reading.
5. **The cost shape** (§W5), stated and not re-proved, as instructed:
   `scanWordOpsWide blockLen stride = blockLen · (2·stride + 3)`; the landed
   `scanWordOps` *is* that shape at `stride = wordOpFactor n`
   (`scanWordOpsWide_eq_scanWordOps`), and the wide charge is never larger
   (`scanWordOpsWide_le`).  What is **not** inherited is the envelope absorption
   (`scan_cost_absorbed`'s `K + 4`) nor `D7.agrees`'s step horizon: a stride-`k`
   pass executes `stride` reads and `stride` digit compares per estimate, so the
   `Instr`-step count leaves `12·N + 6` for a count linear in `stride`.  That
   re-measurement is residual (iv), and it is *not* done here.

`Statement.lean`'s hashes are untouched: this module adds names only and is a
leaf of the import DAG.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaLoop
import SubsetSumL25.Row.KapilaEstimate

set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §W1 — the stride-general block reader

`wordList f base len` reads **one** word per index (`f (base + j)`), which is why
every landed statement about the scan is a statement about a stride-1 payload.
The reader §6.2 actually needs reads `stride` words per estimate, at
`base + s·stride + j`, and its value is the base-`2^w` numerator of those words —
`placeValueAt`'s numerator, in the `ℕ` vocabulary `KapilaLoop` reasons in. -/

/-- **The stride-`k` estimate numerator.**  The `stride` words at `addr`, read
little-endian as a base-`2^w` integer: `Σ_{j<stride} f (addr + j) · 2^{w·j}`.
This is `placeValueAt`'s numerator with the memory's `BitVec` replaced by the
`ℕ`-valued state — §W2 proves the two agree. -/
def numAt (w : Nat) (f : Nat → Nat) (addr stride : Nat) : Nat :=
  ((List.range stride).map fun j => f (addr + j) * 2 ^ (w * j)).sum

/-- The empty read is zero — the reader's base case. -/
@[simp] theorem numAt_zero (w : Nat) (f : Nat → Nat) (addr : Nat) : numAt w f addr 0 = 0 := by
  simp [numAt]

/-- **The reader's carry step** (in `ℕ`): reading one more word at `addr + stride`
adds exactly its place value `word · 2^{w·stride}`.  This is `placeValueAt_succ`
without the shared denominator, and it is the reason a stride-`k` read composes
word by word. -/
theorem numAt_succ (w : Nat) (f : Nat → Nat) (addr stride : Nat) :
    numAt w f addr (stride + 1)
      = numAt w f addr stride + f (addr + stride) * 2 ^ (w * stride) := by
  unfold numAt
  rw [List.sum_range_succ]

/-- **The stride-1 read is the landed one-word read.** -/
theorem numAt_one (w : Nat) (f : Nat → Nat) (addr : Nat) : numAt w f addr 1 = f addr := by
  rw [show (1 : Nat) = 0 + 1 from rfl, numAt_succ, numAt_zero, Nat.zero_add]
  simp

/-- **A stride-1 read always fits a word** — the contrast with `numAt_not_word`
below, and the reason `wordList`/`memOf` could be stride-1 shapes at all. -/
theorem numAt_one_lt {w : Nat} (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (addr : Nat) :
    numAt w f addr 1 < 2 ^ w := by
  rw [numAt_one]
  exact hfit addr

/-- **The stride-`k` block.**  Estimate `s` occupies the `stride` words at
`base + s · stride`; this is `wordList`'s stride-general sibling, and
`numBlock_one_eq_wordList` proves the landed reader is its `stride = 1`
instance — the generalization displaces nothing. -/
def numBlock (w : Nat) (f : Nat → Nat) (base len stride : Nat) : List Nat :=
  (List.range len).map fun s => numAt w f (base + s * stride) stride

@[simp] theorem numBlock_zero (w : Nat) (f : Nat → Nat) (base stride : Nat) :
    numBlock w f base 0 stride = [] := rfl

/-- **The block's cons rule at stride `k`** — the loop's address advance.  The
head is the estimate at `base`; the rest is the same block based one **stride**
along, not one word along.  That single change of shift is the whole of the
read loop's stride arithmetic. -/
theorem numBlock_succ (w : Nat) (f : Nat → Nat) (base len stride : Nat) :
    numBlock w f base (len + 1) stride
      = numAt w f base stride :: numBlock w f (base + stride) len stride := by
  unfold numBlock
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero, Nat.zero_mul]
  congr 1
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply]
  exact congrArg (fun x => numAt w f x stride) (by rw [Nat.succ_mul]; omega)

/-- **The stride-1 reader *is* `wordList`.**  So §7 step 7's landed block
vocabulary is the degenerate case of the wide one, exactly as
`wideBinSumAgrees_one_iff` shows for the contract. -/
theorem numBlock_one_eq_wordList (w : Nat) (f : Nat → Nat) (base len : Nat) :
    numBlock w f base len 1 = wordList f base len := by
  unfold numBlock wordList
  apply List.map_congr_left
  intro s _
  rw [show base + s * 1 = base + s from by omega, numAt_one]

/-! ### §W2 — the reader *is* the place value

The `ℕ` reader of §W1 and the `ℚ` place value of `KapilaEstimate` are the same
object over one shared scale.  That is what lets a `PayloadConvention` whose
payload blocks are the *scaled reader* be a `WideLayout`, which is what lets
`dAt_eq_widePlaceValue` apply — i.e. what makes `aAt` a wide reading. -/

/-- **The reader's value, cast to `ℚ`, is the place value's numerator.**  A
`ℕ`-level identity: the sum of the `2^{w·j}`-weighted words, cast, is the sum of
the casts.  Stated at top level so its induction does not drag the surrounding
`have`s into a reverted context. -/
theorem numAt_cast {w : Nat} (f : Nat → Nat) (addr stride : Nat) :
    (numAt w f addr stride : ℚ)
      = ((List.range stride).map
          fun j => ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)).sum := by
  induction stride with
  | zero => simp [numAt]
  | succ m ih =>
    rw [numAt_succ, Nat.cast_add, ih, List.sum_range_succ]
    congr 1
    push_cast
    ring

/-- **The reader's value, multiplied out, is the place value.**  `numAt` over the
`ℕ` state equals `placeValueAt` under the one shared `2^fracBits` — no rounding,
no second denominator.  This is `placeValue_scale` seen from the `ℕ` side. -/
theorem numAt_eq_placeValueAt_scale {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (addr stride fracBits : Nat) :
    (numAt w f addr stride : ℚ)
      = placeValueAt (memOf w f) addr stride fracBits * (2 : ℚ) ^ fracBits := by
  have hterm : ∀ j : Nat, ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)
      = ((f (addr + j) * 2 ^ (w * j) : Nat) : ℚ) := by
    intro j
    push_cast
    ring
  have hstep : ∀ j : Nat, ((memOf w f (addr + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)
      = ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j) := by
    intro j
    rw [memOf_toNat f hfit (addr + j)]
  have hkey : placeValueAt (memOf w f) addr stride fracBits * (2 : ℚ) ^ fracBits
      = ((List.range stride).map
          fun j => ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)).sum := by
    unfold placeValueAt
    rw [div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℚ) < (2 : ℚ) ^ fracBits))]
    rw [List.map_congr_left (fun j _ => hstep j)]
  have hnum : ((numAt w f addr stride : Nat) : ℚ)
      = ((List.range stride).map
          fun j => ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)).sum :=
    numAt_cast f addr stride
  rw [hnum, hkey]

/-- **The place value *is* the scaled reader** — the direction a layout consumes. -/
theorem placeValue_eq_scale_numAt {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (base stride fracBits s : Nat) :
    placeValue (memOf w f) base stride fracBits s
      = (numAt w f (base + s * stride) stride : ℚ) / (2 : ℚ) ^ fracBits := by
  have h := numAt_eq_placeValueAt_scale f hfit (base + s * stride) stride fracBits
  rw [placeValue_eq_placeValueAt,
    eq_div_iff (ne_of_gt (by positivity : (0 : ℚ) < (2 : ℚ) ^ fracBits))]
  exact h.symm

/-- **A block of readers is the block of place values, scaled.**  The `ℚ` form of
`numBlock_one_eq_wordList`'s content at arbitrary stride: mapping `toQ` over the
`ℕ` reader gives exactly the list of place values `WideLayout` is stated about. -/
theorem numBlock_map_toQ_eq_placeValue {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (base len stride fracBits : Nat) :
    (numBlock w f base len stride).map (toQ fracBits)
      = (List.range len).map (placeValue (memOf w f) base stride fracBits) := by
  unfold numBlock
  rw [map_map']
  apply List.map_congr_left
  intro s _
  show toQ fracBits (numAt w f (base + s * stride) stride)
      = placeValue (memOf w f) base stride fracBits s
  unfold toQ
  exact (placeValue_eq_scale_numAt f hfit base stride fracBits s).symm

/-- **`aAt` *is* the wide reading.**  A convention whose payload blocks are the
scaled stride-general reader satisfies `WideLayout`, so the whole wide apparatus
lands on the reader without a new contract: `dAt_eq_widePlaceValue` applies
(`dAt_eq_reader`), and `rowTest_eq_wideBinSum` applies (`wideExit_eq_binSum`). -/
theorem wideLayout_of_numBlock {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (stride : Nat)
    (hA : C.Ahat = (numBlock w f C.baseA C.blockLen stride).map (toQ C.fracBits))
    (hV : C.Vhat = (numBlock w f C.baseV C.blockLen stride).map (toQ C.fracBits)) :
    WideLayout C (memOf w f) stride :=
  ⟨hA.trans (numBlock_map_toQ_eq_placeValue f hfit C.baseA C.blockLen stride C.fracBits),
   hV.trans (numBlock_map_toQ_eq_placeValue f hfit C.baseV C.blockLen stride C.fracBits)⟩

/-- **`dAt` at the stride-`k` reader.**  The estimate §7 step 7 compares *is* the
difference of the two multi-word readings of the reader — `aAt` has become the
wide reading, and this is `dAt_eq_widePlaceValue` at that instantiation. -/
theorem dAt_eq_reader {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (stride : Nat)
    (hA : C.Ahat = (numBlock w f C.baseA C.blockLen stride).map (toQ C.fracBits))
    (hV : C.Vhat = (numBlock w f C.baseV C.blockLen stride).map (toQ C.fracBits))
    {i : Nat} (hi : i < C.blockLen) :
    C.dAt i = placeValue (memOf w f) C.baseV stride C.fracBits i
      - placeValue (memOf w f) C.baseA stride C.fracBits i :=
  dAt_eq_widePlaceValue (wideLayout_of_numBlock C f hfit stride hA hV) hi

/-! ### §W3 — the k-word sum is **not** word-resident

This is the verdict the wiring forces, and it is negative: the sum a stride-`k`
read accumulates does not fit the word the loop reads it into.  The digits fit
(`hfit`); their base-`2^w` sum does not.  So a per-iteration read that *is* `numAt`
cannot be a single `load` — not for want of a lemma, but because the value is not
in the state's type. -/

/-- **The top digit is a lower bound.**  Reading one more word adds its place
value to a nonnegative sum, so the last word read dominates from below. -/
theorem numAt_ge_top (w : Nat) (f : Nat → Nat) (addr stride : Nat) :
    f (addr + stride) * 2 ^ (w * stride) ≤ numAt w f addr (stride + 1) := by
  rw [numAt_succ]
  exact Nat.le_add_left _ _

/-- **The k-word sum overflows the word.**  At `stride ≥ 1`, a nonzero top digit
makes the reader's value at least `2^w`: the read is *not* representable in a
`BitVec w` cell, so `memOf` cannot hold it and `scanProg`'s `load` cannot produce
it.  The stride-1 contrast is `numAt_one_lt` — which is exactly why the landed
`wordList`/`memOf` shapes are stride 1.

**Consequence, and it is a design fact rather than a missing lemma.**  Residual
(i) as worded («the loop's per-iteration read becomes the k-word summing read»)
is not implementable in the `BitVec w` state.  A stride-`k` payload needs either
(a) a top-down **digitwise** comparison — `stride` word compares, no single cell
ever holding the numerator — or (b) a multi-word output block with its own carry
chain, which is the layout `KapilaEstimate` already proves exact
(`placeValueAt_payloadStride`) but which the scan's `load`/`add` sequence does
not yet write.  Either way the `hitWord` single-cell form cannot host the wide
test, so the remaining work is a *comparison* re-shaping, not a read widening. -/
theorem numAt_not_word {w stride : Nat} (hs : 1 ≤ stride) (f : Nat → Nat) (addr : Nat)
    (hpos : 0 < f (addr + stride)) : 2 ^ w ≤ numAt w f addr (stride + 1) := by
  have h1 := numAt_ge_top w f addr stride
  have h4 : 2 ^ w ≤ 2 ^ (w * stride) := by
    apply Nat.pow_le_pow_right (by norm_num)
    calc w = w * 1 := (Nat.mul_one w).symm
      _ ≤ w * stride := Nat.mul_le_mul_left w hs
  have h2 : 2 ^ w ≤ f (addr + stride) * 2 ^ (w * stride) := by
    calc 2 ^ w ≤ 2 ^ (w * stride) := h4
      _ = 1 * 2 ^ (w * stride) := (one_mul _).symm
      _ ≤ f (addr + stride) * 2 ^ (w * stride) := Nat.mul_le_mul_right _ hpos
  exact le_trans h2 h1

/-- **The overflow is not an artefact of the top digit being large**: one unit of
top digit suffices.  Stated separately so the obstruction cannot be read as a
bound that a smaller layout would dodge. -/
theorem numAt_not_word_one {w stride : Nat} (hs : 1 ≤ stride) (f : Nat → Nat) (addr : Nat)
    (hpos : 1 ≤ f (addr + stride)) : 2 ^ w ≤ numAt w f addr (stride + 1) :=
  numAt_not_word hs f addr (by omega)

/-! ### §W4 — the loop's step at stride `k`, and the exit fold

`scan_loop`'s induction consumes two facts per iteration: the head pair is the
address the loop's counter names, and the accumulator over `m+1` pairs is the head
pair plus the accumulator over `m`.  At stride `k` those are the same facts with
`stride` substituted for `1` — the address advances by a stride, and the block is
`numBlock`, not `wordList`.  Proved here at the loop's own granularity, so wiring
them in is a substitution rather than a re-derivation. -/

/-- **One iteration's arithmetic, at stride `k`.**  `scan_loop` writes
`base + (N - m)` and `+ 1` here; the wide loop writes `base + j·stride` and
`+ stride`. -/
theorem hitCount_numBlock_step (h : Nat) (w : Nat) (f : Nat → Nat)
    (baseV baseA j m stride : Nat) :
    hitCount h (numBlock w f (baseV + j * stride) (m + 1) stride)
        (numBlock w f (baseA + j * stride) (m + 1) stride)
      = hitWord h (numAt w f (baseV + j * stride) stride)
          (numAt w f (baseA + j * stride) stride)
        + hitCount h (numBlock w f (baseV + (j + 1) * stride) m stride)
            (numBlock w f (baseA + (j + 1) * stride) m stride) := by
  have e : ∀ b : Nat, b + j * stride + stride = b + (j + 1) * stride := by
    intro b
    rw [Nat.succ_mul]
    omega
  rw [numBlock_succ, numBlock_succ, hitCount_succ, e, e]

/-- Splitting the first term off a `range`-indexed sum — the `sum` twin of
`wordList_succ`, proven the same way because the library's `List.map_map` is
stated through `Function.comp` and does not match under this pin's presentation
of `List.map`. -/
theorem sum_range_map_succ (F : Nat → Nat) (m : Nat) :
    ((List.range (m + 1)).map F).sum
      = F 0 + ((List.range m).map fun k => F (k + 1)).sum := by
  have hlist : (List.range m).map (F ∘ Nat.succ) = (List.range m).map fun k => F (k + 1) := by
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.sum_cons, hlist]

/-- `map`-level form of the fold: `hitCount` over two `range`-indexed blocks is the
sum of the pairwise hits.  Its own induction, and it is what turns the loop's
accumulator into a sum. -/
theorem hitCount_map_range (h : Nat) (F G : Nat → Nat) (len : Nat) :
    hitCount h ((List.range len).map F) ((List.range len).map G)
      = ((List.range len).map fun k => hitWord h (F k) (G k)).sum := by
  induction len generalizing F G with
  | zero => simp [hitCount]
  | succ m ih =>
    have hF : (List.range (m + 1)).map F = F 0 :: (List.range m).map (F ∘ Nat.succ) := by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
    have hG : (List.range (m + 1)).map G = G 0 :: (List.range m).map (G ∘ Nat.succ) := by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
    have hmap : ((List.range m).map fun k => hitWord h ((F ∘ Nat.succ) k) ((G ∘ Nat.succ) k))
        = ((List.range m).map fun k => (fun j => hitWord h (F j) (G j)) (k + 1)) := by
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
    rw [hF, hG, hitCount_succ, ih, sum_range_map_succ, hmap]

/-- **The exit fold at stride `k`.**  After the loop, the accumulator is the sum
of the per-estimate hits over the wide block — the object `scan_run` reports as
`hitCount` over `wordList`, with `numBlock` in its place. -/
theorem hitCount_numBlock_eq_sum (h : Nat) (w : Nat) (f : Nat → Nat)
    (baseV baseA len stride : Nat) :
    hitCount h (numBlock w f baseV len stride) (numBlock w f baseA len stride)
      = ((List.range len).map fun k =>
          hitWord h (numAt w f (baseV + k * stride) stride)
            (numAt w f (baseA + k * stride) stride)).sum := by
  rw [numBlock, numBlock, hitCount_map_range]

/-- **The wide exit's verdict is `rowTest` on the two payload blocks.**  This is
`scan_run`'s exit shape at stride `k`: `decide (0 < ·)` on the loop's accumulator
is the paper's test on the payloads, with the payloads being the *scaled reader*
(`hA`, `hV`) rather than the one-word blocks the landed theorem reports. -/
theorem wideExit_eq_rowTest {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) {stride : Nat}
    (hA : C.Ahat = (numBlock w f C.baseA C.blockLen stride).map (toQ C.fracBits))
    (hV : C.Vhat = (numBlock w f C.baseV C.blockLen stride).map (toQ C.fracBits))
    (hb : ∀ v a, hitWord (2 ^ (C.fracBits - 1)) v a = 1
      ↔ (1 / 2 : ℚ) ≤ |(v : ℚ) / (2 : ℚ) ^ C.fracBits - (a : ℚ) / (2 : ℚ) ^ C.fracBits|) :
    (decide (0 < hitCount (2 ^ (C.fracBits - 1))
        (numBlock w f C.baseV C.blockLen stride)
        (numBlock w f C.baseA C.blockLen stride)) : Bool)
      = Routines.rowTest C.Ahat C.Vhat := by
  have hiff : (decide (0 < hitCount (2 ^ (C.fracBits - 1))
        (numBlock w f C.baseV C.blockLen stride)
        (numBlock w f C.baseA C.blockLen stride)) : Bool)
      = anyHit (2 ^ (C.fracBits - 1)) (numBlock w f C.baseV C.blockLen stride)
          (numBlock w f C.baseA C.blockLen stride) := by
    by_cases hpos : 0 < hitCount (2 ^ (C.fracBits - 1))
        (numBlock w f C.baseV C.blockLen stride) (numBlock w f C.baseA C.blockLen stride)
    · rw [decide_eq_true hpos, (hitCount_pos_iff _ _ _).mp hpos]
    · have hne : anyHit (2 ^ (C.fracBits - 1)) (numBlock w f C.baseV C.blockLen stride)
          (numBlock w f C.baseA C.blockLen stride) ≠ true :=
        fun hc => hpos ((hitCount_pos_iff _ _ _).mpr hc)
      cases hany : anyHit (2 ^ (C.fracBits - 1)) (numBlock w f C.baseV C.blockLen stride)
          (numBlock w f C.baseA C.blockLen stride) with
      | false => rw [decide_eq_false hpos]
      | true => exact absurd hany hne
  rw [hiff, anyHit_eq_rowTest hb, hA, hV]

/-- **The exit shape with (ii) as the only input.**  `wideExit_eq_rowTest` composed
with `rowTest_eq_wideBinSum`: supply the pointwise identity between the wide place
values and a `binSum`, and the stride-`k` loop's verdict *is* the test on the bin
sums.  Nothing about `dAt`, the payload lists, or the memory is consumed beyond
the layout the reader already discharges — so the bin sums are the whole of the
remaining mathematical obligation. -/
theorem wideExit_eq_binSum {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) {stride : Nat}
    (hA : C.Ahat = (numBlock w f C.baseA C.blockLen stride).map (toQ C.fracBits))
    (hV : C.Vhat = (numBlock w f C.baseV C.blockLen stride).map (toQ C.fracBits))
    (hb : ∀ v a, hitWord (2 ^ (C.fracBits - 1)) v a = 1
      ↔ (1 / 2 : ℚ) ≤ |(v : ℚ) / (2 : ℚ) ^ C.fracBits - (a : ℚ) / (2 : ℚ) ^ C.fracBits|)
    (binSum : Nat → ℚ) (hbin : WideBinSumAgrees C (memOf w f) stride binSum) :
    (decide (0 < hitCount (2 ^ (C.fracBits - 1))
        (numBlock w f C.baseV C.blockLen stride)
        (numBlock w f C.baseA C.blockLen stride)) : Bool)
      = ((List.range C.blockLen).map fun i => decide ((1 / 2 : ℚ) ≤ |binSum i|)).any id := by
  rw [wideExit_eq_rowTest C f hA hV hb]
  exact rowTest_eq_wideBinSum C (memOf w f)
    (wideLayout_of_numBlock C f hfit stride hA hV) binSum hbin

/-- The same exit shape with `hb` supplied from the paper's parameters: at
`fracBits ≥ 1` the word test at `h = 2^{fracBits−1}` is §7 step 7's `1/2` test
(`hitWord_eq_ratTest`), so `wideExit_eq_binSum` has no test-form hypothesis left. -/
theorem wideExit_eq_binSum' {n : Nat} {x : Instance n} {w : Nat}
    (C : PayloadConvention n x) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) {stride : Nat}
    (hfrac : 1 ≤ C.fracBits)
    (hA : C.Ahat = (numBlock w f C.baseA C.blockLen stride).map (toQ C.fracBits))
    (hV : C.Vhat = (numBlock w f C.baseV C.blockLen stride).map (toQ C.fracBits))
    (binSum : Nat → ℚ) (hbin : WideBinSumAgrees C (memOf w f) stride binSum) :
    (decide (0 < hitCount (2 ^ (C.fracBits - 1))
        (numBlock w f C.baseV C.blockLen stride)
        (numBlock w f C.baseA C.blockLen stride)) : Bool)
      = ((List.range C.blockLen).map fun i => decide ((1 / 2 : ℚ) ≤ |binSum i|)).any id :=
  wideExit_eq_binSum C f hfit hA hV (fun v a => hitWord_eq_ratTest hfrac v a) binSum hbin

/-! ### §W5 — the cost shape at stride `k`, **stated**

A stride-`k` pass touches `k` words per estimate instead of one.  The landed
charge is `scanWordOps n blockLen = blockLen · (2·wordOpFactor n + 3)`; the wide
charge is the *same shape* with the actual stride in place of the upper bound
`wordOpFactor n`, which is what §6.2's `blockLen ≤ wordOpFactor n` /
`payloadStride ≤ wordOpFactor n` relation makes meaningful.

**What is not inherited, and is residual (iv)'s to fix.**  Two things move and
neither is re-measured here: the constant (`stride` replaces
`wordOpFactor n`, so the charge shrinks in the *word-op* unit) and — the load-
bearing one — the `Instr`-step horizon.  `scan_run`'s `12·N + 6` counts one
`load` per estimate per side; a stride-`k` read executes `stride` of them plus the
digit compares, so `D7.agrees`'s step horizon is a count linear in `stride`, not
`12·N + 6`.  Since `D7` is where word operations are translated into `Instr`
steps, quoting `scan_cost_absorbed`'s `K + 4` here would be the `K + 3`-versus-
`K + 7` mistake wearing a stride — so only the shape is stated. -/

/-- §7 step 7's scan at a given stride, in word operations: `blockLen` estimates,
each costing `stride` digit visits per side plus three word reads.  At
`stride = wordOpFactor n` this is exactly the landed `scanWordOps`
(`scanWordOpsWide_eq_scanWordOps`). -/
def scanWordOpsWide (blockLen stride : Nat) : Nat := blockLen * (2 * stride + 3)

/-- **The landed charge *is* the wide shape at the bound.**  So the stride
generalization is a substitution, not a new cost model. -/
theorem scanWordOpsWide_eq_scanWordOps (n blockLen : Nat) :
    scanWordOpsWide blockLen (wordOpFactor n) = scanWordOps n blockLen := rfl

/-- **The wide charge never exceeds the landed one** at any stride within §6.2's
bound — the seed of residual (iv)'s re-measurement, not its conclusion. -/
theorem scanWordOpsWide_le (n blockLen stride : Nat) (hs : stride ≤ wordOpFactor n) :
    scanWordOpsWide blockLen stride ≤ scanWordOps n blockLen := by
  unfold scanWordOpsWide scanWordOps
  exact Nat.mul_le_mul_left blockLen (by omega)

/-- The stride-1 instance, for comparison with the per-pair charge `2+3 = 5`. -/
theorem scanWordOpsWide_one (blockLen : Nat) : scanWordOpsWide blockLen 1 = 5 * blockLen := by
  unfold scanWordOpsWide
  omega

end SubsetSumL25.Row
