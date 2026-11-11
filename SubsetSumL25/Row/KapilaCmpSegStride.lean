/-
Residual (iv)'s last gap — **the stride-`k` payload read in the test segment**.

§C12 (`Row/KapilaCmpSegLoop`) restated the horizon of §7 step 7's test segment per
comparison: `blockLen` comparisons, `cmpSegCost + 6 ≤ 20 + 9p'` each, the whole run
`m · (20 + 9 · (p + m))`.  Two things sat outside that restatement and were named as
this round's work:

1. `cmpSeg` reads **one word per index** — `load 3 0` with cell `0 = addrV + p` — while
   §6.2's estimates sit in `stride`-word blocks (`payloadStride`, and
   `placeValueAt_payloadStride` proves such a block carries an `F`-bit numerator
   exactly).  So the object the segment's digit read is a term of is not a one-word
   read but the `stride`-load fold `Σ_{j<stride} f (addr + j) · 2^{w·j}`.
2. §C12's charge is therefore a stride-1 figure, and the stride has to be charged or
   shown not to be.

## §C13.1 — the fold, and what "the fold is `numAt`" actually costs

`numAt` **is** the fold (`KapilaWide` §W1: `Σ_{j<stride} f (addr+j) · 2^{w·j}`), so
`strideFold_eq_numAt` below is an identity, not a discovery, and this module says so
rather than dressing it: `strideFold` is the same sum written as the running
accumulator a program produces, and the proof is `numAt_succ` read left-to-right.
What has content is the consequence:

* **the segment's digit read is the fold's `p`-th term, at the estimate's address.**
  At estimate `i` the block starts at `baseV + i·stride`, so the digit the segment
  loads is `f ((baseV + i·stride) + p) · 2^{w·p}` — and `numAt_split` at
  `addr := baseV + i·stride` says the block *splits* at exactly that term.  So the
  landed digitwise segment is a read of the stride-`k` fold already; `cmpSeg` never
  had to materialise a numerator, which is why `numAt_not_word`'s obstruction
  (`a stride-k numerator exceeds 2^w`) does not bite here.
* **the segment's verdict is §7 step 7's test on the two folds.**
  `digHalf_estimate_eq_threshold` is `digHalf_eq_threshold` at the estimate's address:
  the decision lemma transfers from stride 1 to stride `stride` for free, because it
  was stated at an abstract address.  `payloadStride_fits_digit` discharges its one
  layout premise (`(F−1)/w + 1 ≤ stride`) at §6.2's own `stride = payloadStride w F`,
  and `digHalf_estimate_payloadStride` is the result with no hand-supplied fit left.

## §C13.2 — the charge, measured (and why `stride` does **not** multiply the reads)

The obvious reading of "charge `stride` words per estimate" is `cmpSegCost · stride`.
**That is not what the segment pays, and the difference is the whole point of (i)'s
re-specification.**  Machine-checked here (`cmpSeg_readPositions`): the segment has
exactly **four** `load` instructions — positions `[0, 1, 21, 22]` — the two prologue
digit reads and the two walk-head reads.  A comparison reads **one word per side per
digit position**, and descends at most `p` digits on an exact tie.  The stride lives
in the **addresses** (`baseV + i·stride + p`), not in the read count.  So:

    per comparison:  cmpSegCost h (baseV + i·stride) (baseA + i·stride) p r + 6  ≤  20 + 9p

with **`p = (F−1)/w` a constant** — the digit holding the `1/2` bit — not a drifting
counter.  That is a change of shape, not only of constant: §C12's figure drifts
(`20 + 9·(p + m)`) because the landed loop's counter carries two roles at once, the
digit *address* offset and the digit *position*, which coincide only at `stride = 1`.
`estFuel` below is the same run at the fold's addresses with the roles separated, and
`estFuel_le` gives `blockLen · (20 + 9p)` — **no drift term** — while
`estFuel_le_landed` shows the restated figure still fits under §C12's, so nothing
landed is contradicted; the horizon simply tightens.  `estFuel_fits` is the
§C12-shaped form `D7.agrees` consumes, and `estFuel_le_paper` is that figure in the
paper's vocabulary.

**The `stride`-word charge exists, and it is the charge of a read the row proves
impossible.**  `scanWordOpsWide blockLen stride = blockLen · (2·stride + 3)`
(`KapilaWide` §W5) prices a whole-block read — `stride` words per side per estimate.
`numAt_not_word` proves that numerator does not fit a word, so the digitwise segment
does not perform that read; its word-op charge is the same shape at the digit count it
actually visits, `scanWordOpsWide blockLen (p+1)` (`digitwise_is_wide_at_digit`), and
`digitwiseWordOps_le_wide` bounds it by the whole-block figure at any `p + 1 ≤ stride`.
So charging `stride` words per estimate into §C12 would be charging, inside the
digitwise accounting, for the read the digitwise re-specification exists to avoid —
and the charge is an upper bound rather than a false one, which is why it is stated
as a bound and not as the segment's cost.

## §C13.3 — what is *not* landed: the program

Everything above is the arithmetic, at §C12's own level.  The **program** does not
follow for free, and `sim_stride.py` (in the lane, the lane rule: simulate first)
measures why.  The landed tail reloads the walk's counter from the loop counter
(`.add 2 13 7`); at `stride = 1` the two coincide, at `stride = k > 1` they do not.
Measured on the composed program:

* **D1** with the counter at `i·k + p` and cell 2 reloaded from a `p` constant,
  iteration `i` reads exactly `(baseV + i·k + p, baseA + i·k + p)` — the fold's
  `p`-th term at estimate `i`'s address — and every load stays inside a block;
* **D2** keeping the landed reload, the walk's span becomes `i·k + p` digits instead
  of `p`, spilling into earlier estimates (measured: `{4,6,6,6}` vs `{4,4,4,4}` loads
  per iteration) and, on a block built for it, flipping a verdict (`acc = 0` where the
  per-estimate test gives `1`);
* **D3** the guard's limit must be `blockLen·k + p`, not `blockLen` — the stride-1
  shape stops the run early (measured: 1 comparison of 3);
* **D4** the per-comparison charge is exactly `cmpSegCost + 6` — the stride advance is
  one instruction either way — and **D5/D6** the correct shape's accumulator is the
  per-estimate `digHalf` count on every block measured (3 fixed + 60 swept).

So the stride read's **program** — a `cmpSeg` variant whose walk counter is reloaded
from a `p` constant, with a stride-advanced loop counter and a `blockLen·k + p`
limit — is the next named piece.  It is named, not claimed: the arithmetic above is
what this module lands.

`Statement.lean` is untouched (`3dc6567e…34aa`); every name below is new and this
module is a leaf of the import DAG.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaEstimate
import SubsetSumL25.Row.KapilaWide
import SubsetSumL25.Row.KapilaDigitwise
import SubsetSumL25.Row.KapilaCmpSegLoop

set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §C13.1 — the fold of loads, and the segment's read as its `p`-th term -/

/-- **The stride-`k` read as a fold of loads.**  `strideFold w f addr n` reads the `n`
words at `addr, addr+1, …` and accumulates them at the place weights `2^{w·j}` — the
running accumulator a program produces, in the order it produces it.  This is the
object `numAt` names; the accumulator form is what makes the equivalence with a
program's read a one-line induction rather than a convention. -/
def strideFold (w : Nat) (f : Nat → Nat) (addr : Nat) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => strideFold w f addr n + f (addr + n) * 2 ^ (w * n)

/-- The empty fold reads nothing. -/
theorem strideFold_zero (w : Nat) (f : Nat → Nat) (addr : Nat) :
    strideFold w f addr 0 = 0 := rfl

/-- The fold's step: one more load, at the next place weight. -/
theorem strideFold_succ (w : Nat) (f : Nat → Nat) (addr n : Nat) :
    strideFold w f addr (n + 1) = strideFold w f addr n + f (addr + n) * 2 ^ (w * n) := rfl

/-- **THE FOLD *IS* `numAt`** — at every address, in particular at each estimate's
`base + i·stride`.  An identity, not a discovery: `numAt`'s definition is this sum.
Stated because the segment's read is what has to be identified with it, and a stated
identity is one a caller can rewrite with. -/
theorem strideFold_eq_numAt (w : Nat) (f : Nat → Nat) (addr n : Nat) :
    strideFold w f addr n = numAt w f addr n := by
  induction n with
  | zero => rfl
  | succ m ih => rw [strideFold_succ, ih, numAt_succ]

/-- **The fold at estimate `i`'s address** — the form the test segment reads. -/
theorem strideFold_eq_numAt_block (w : Nat) (f : Nat → Nat) (base stride i : Nat) :
    strideFold w f (base + i * stride) stride = numAt w f (base + i * stride) stride :=
  strideFold_eq_numAt w f (base + i * stride) stride

/-- **The digit the segment loads is the fold's `p`-th term.**  The address the segment
computes at estimate `i` is `(base + i·stride) + p`, and the term it reads there enters
the fold at weight `2^{w·p}`.  The `numAt_split` half — that the block *splits* at that
term — is `numAt_split` at the same address, stated below so the two are one object. -/
theorem numAt_term_at_estimate (w : Nat) (f : Nat → Nat) (base stride i p : Nat) :
    f (base + i * stride + p) * 2 ^ (w * p)
      = f ((base + i * stride) + p) * 2 ^ (w * p) := rfl

/-- **The block splits at the segment's digit.**  `numAt_split` at the estimate's
address: below `2^{w·(p+1)}`, estimate `i`'s folded numerator is its digit at `p` times
the place weight, plus the low `p`-digit fold.  This is why a single-digit read decides
the comparison at all. -/
theorem numAt_split_at_estimate {w : Nat} (f : Nat → Nat) {base stride i p : Nat}
    (hp : p + 1 ≤ stride)
    (h : numAt w f (base + i * stride) stride < 2 ^ (w * (p + 1))) :
    numAt w f (base + i * stride) stride
      = f (base + i * stride + p) * 2 ^ (w * p) + numAt w f (base + i * stride) p := by
  have := numAt_split (addr := base + i * stride) f hp h
  rwa [show base + i * stride + p = (base + i * stride) + p from by omega] at this

/-- **THE SEGMENT'S VERDICT AT ESTIMATE `i` IS §7 STEP 7'S TEST ON THE TWO FOLDS.**
`digHalf_eq_threshold` at the estimate's address: the decision lemma was stated at an
abstract address, so transferring it from stride 1 to stride `stride` costs nothing.
This is the deliverable's arithmetic half — the segment's read *is* the fold's, and its
verdict *is* the test on the folds' values. -/
theorem digHalf_estimate_eq_threshold {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F)
    (f g : Nat → Nat) (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w)
    {baseV baseA stride i : Nat} (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f (baseV + i * stride) stride < 2 ^ F)
    (hAb : numAt w g (baseA + i * stride) stride < 2 ^ F) :
    (digHalf f g (baseV + i * stride) (baseA + i * stride) ((F - 1) / w) ((F - 1) % w)
        = true)
      ↔ 2 ^ (F - 1) ≤ wordDiff (numAt w f (baseV + i * stride) stride)
          (numAt w g (baseA + i * stride) stride) :=
  digHalf_eq_threshold hw hF f g hf hg hp hVb hAb

/-- **The layout premise is free at §6.2's `stride`.**  `(F−1)/w + 1 ≤ payloadStride w F`:
the `1/2` bit's digit is inside the block §6.2 sizes.  So a caller never supplies the
block-fit hypothesis by hand — `payloadStride`'s own spec gives it. -/
theorem payloadStride_fits_digit {w F : Nat} (hw : 0 < w) (hF : 1 ≤ F) :
    (F - 1) / w + 1 ≤ payloadStride w F := by
  unfold payloadStride
  have h : F - 1 ≤ F + w - 1 := by omega
  exact Nat.succ_le_succ (Nat.div_le_div_right h)

/-- **§C13.1 at §6.2's parameters**: the segment's verdict at estimate `i` is the
`1/2` test on the two `payloadStride`-word folds, with **no** block-fit premise left to
supply. -/
theorem digHalf_estimate_payloadStride {w F : Nat} (hw : 0 < w) (hF : 1 ≤ F)
    (f g : Nat → Nat) (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w)
    {baseV baseA i : Nat}
    (hVb : numAt w f (baseV + i * payloadStride w F) (payloadStride w F) < 2 ^ F)
    (hAb : numAt w g (baseA + i * payloadStride w F) (payloadStride w F) < 2 ^ F) :
    (digHalf f g (baseV + i * payloadStride w F) (baseA + i * payloadStride w F)
        ((F - 1) / w) ((F - 1) % w) = true)
      ↔ 2 ^ (F - 1) ≤ wordDiff
          (numAt w f (baseV + i * payloadStride w F) (payloadStride w F))
          (numAt w g (baseA + i * payloadStride w F) (payloadStride w F)) :=
  digHalf_estimate_eq_threshold (Nat.pos_of_ne_zero (by omega)) hF f g hf hg
    (payloadStride_fits_digit (w := w) (F := F) hw hF) hVb hAb

/-! ### §C13.2 — the charge: what the segment pays per estimate, and what it does not

`cmpSeg_readPositions` is the measurement the charge rests on: the segment has exactly
four `load` instructions, at fixed positions, so a comparison reads **one word per side
per digit position** whatever the stride.  The stride is in the addresses. -/

/-- `true` exactly on the read instruction. -/
def isLoad : Instr → Bool
  | .load _ _ => true
  | _ => false

/-- Positions (in the text) of the instructions that read memory. -/
def readPositions : List Instr → List Nat
  | [] => []
  | i :: rest => (if isLoad i then [0] else []) ++ (readPositions rest).map (· + 1)

/-- **The segment reads memory four times, at positions `[0, 1, 21, 22]`.**  Two digit
reads in the prologue, two at the walk head — and nothing else, so the stride cannot
multiply the read count: it is a change of address, not of size.  (Contrast `scanWordOpsWide`'s
`2·stride`, which prices the whole-block read `numAt_not_word` forbids.) -/
theorem cmpSeg_readPositions (cont : Nat) : readPositions (cmpSeg cont) = [0, 1, 21, 22] := rfl

/-- **The landed reload couples the two counter roles** — the stride-1 coincidence this
round's charge had to separate.  Cell `0` is `[11] + [13]` (a digit *address* offset) and
cell `2` is `[13]` **as well** (the walk's digit *position*), so the single counter `13` is
both.  At `stride = 1` that is correct; at `stride > 1` it is the collapse `sim_stride.py`
D2/D2b measures (span `i·k + p` instead of `p`, and a flipped verdict on a constructed
block).  Stated so the coupling is a citation rather than a reading of prose. -/
theorem cmpSegReload_couples_roles :
    cmpSegReload = [.add 0 11 13, .add 1 12 13, .add 2 13 7] := rfl


/-- **The per-estimate run's charge, at the fold's addresses.**  Comparison `i` runs the
segment at `baseV + i·stride` / `baseA + i·stride` — the estimate's own block — with the
digit position `p` **fixed**.  The recursion peels the head and advances **both bases by
`stride`**, which is `numBlock_succ`'s shift one level up: the read loop's stride
arithmetic is this advance, and nothing else. -/
def estFuel (h : Nat → Nat) (baseV baseA stride p r : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cmpSegCost h baseV baseA p r + 6
      + estFuel h (baseV + stride) (baseA + stride) stride p r n

@[simp] theorem estFuel_zero (h : Nat → Nat) (baseV baseA stride p r : Nat) :
    estFuel h baseV baseA stride p r 0 = 0 := rfl

/-- The run's peel step — the shape §C12's `cmpLoopFuel` has, with the stride in the
addresses instead of in the counter. -/
theorem estFuel_succ (h : Nat → Nat) (baseV baseA stride p r n : Nat) :
    estFuel h baseV baseA stride p r (n + 1)
      = cmpSegCost h baseV baseA p r + 6
        + estFuel h (baseV + stride) (baseA + stride) stride p r n := rfl

/-- **THE RESTATED PER-COMPARISON CHARGE — `blockLen · (20 + 9p)`, no drift.**  Every
comparison in the run costs at most `20 + 9p` (`cmpSeg_hitCharge_le`) and `p` is the
same digit position for all of them, so the run's charge is the flat product.  §C12's
`m · (20 + 9·(p+m))` carried the drift term because the landed counter was also the
digit position; with the roles separated (`sim_stride.py` D2/D2b measure what happens
when they are not) the drift disappears. -/
theorem estFuel_le (h : Nat → Nat) (baseV baseA stride p r : Nat) :
    ∀ n, estFuel h baseV baseA stride p r n ≤ n * (20 + 9 * p) := by
  intro n
  induction n generalizing baseV baseA with
  | zero => simp
  | succ m ih =>
    have hstep : estFuel h baseV baseA stride p r (m + 1)
        = cmpSegCost h baseV baseA p r + 6
          + estFuel h (baseV + stride) (baseA + stride) stride p r m := rfl
    rw [hstep, Nat.succ_mul]
    have hih := ih (baseV := baseV + stride) (baseA := baseA + stride)
    have hc := cmpSeg_hitCharge_le h baseV baseA p r
    omega

/-- **The restated figure still fits under §C12's**, so nothing landed is contradicted:
the drift-free charge is below the drift form at every `n`. -/
theorem estFuel_le_landed (h : Nat → Nat) (baseV baseA stride p r : Nat) :
    ∀ n, estFuel h baseV baseA stride p r n ≤ n * (20 + 9 * (p + n)) := by
  intro n
  have h1 := estFuel_le h baseV baseA stride p r n
  have h2 : n * (20 + 9 * p) ≤ n * (20 + 9 * (p + n)) :=
    Nat.mul_le_mul_left n (by omega)
  omega

/-- **The charge is a Σ, stated so a caller reads it as one** — the `estFuel` twin of
`cmpLoopFuel_eq_sum`, at the fold's drifting addresses and the fixed digit. -/
theorem estFuel_eq_sum (h : Nat → Nat) (baseV baseA stride p r : Nat) :
    ∀ n, estFuel h baseV baseA stride p r n
      = ∑ i ∈ Finset.range n,
          (cmpSegCost h (baseV + i * stride) (baseA + i * stride) p r + 6) := by
  intro n
  induction n generalizing baseV baseA with
  | zero => simp
  | succ m ih =>
    have hstep : estFuel h baseV baseA stride p r (m + 1)
        = cmpSegCost h baseV baseA p r + 6
          + estFuel h (baseV + stride) (baseA + stride) stride p r m := rfl
    rw [hstep, ih (baseV := baseV + stride) (baseA := baseA + stride)]
    have hshift := sum_range_shift
      (fun i => cmpSegCost h (baseV + i * stride) (baseA + i * stride) p r + 6) 0 m
    simp only [Nat.zero_add, Nat.one_add] at hshift
    rw [hshift]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro i _
      rw [show baseV + stride + i * stride = baseV + (i + 1) * stride from by
        rw [Nat.succ_mul]; omega]
      rw [show baseA + stride + i * stride = baseA + (i + 1) * stride from by
        rw [Nat.succ_mul]; omega]

/-- **The restated §C12 figure in the paper's vocabulary.**  `blockLen` comparisons, the
digit position at `(F−1)/w` where the `1/2` bit lives, at any stride the block fits.
The three parameter hypotheses are carried so the statement is the paper's
parameterization rather than the generic one; the bound itself does not consume them
(the charge is `cmpSeg_hitCharge_le`'s, and `p` is a constant either way), and
`payloadStride_fits_digit` is what discharges the fit in a caller. -/
theorem estFuel_le_paper (h : Nat → Nat) (baseV baseA stride : Nat) (blockLen : Nat)
    {w F : Nat} (_hw : 1 ≤ w) (_hF : 1 ≤ F)
    (_hfit : (F - 1) / w + 1 ≤ stride) :
    estFuel h baseV baseA stride ((F - 1) / w) ((F - 1) % w) blockLen
      ≤ blockLen * (20 + 9 * ((F - 1) / w)) :=
  estFuel_le h baseV baseA stride ((F - 1) / w) ((F - 1) % w) blockLen

/-- **THE HORIZON-FIT FORM, at the restated charge** — `estFuel_fits`'s §C12 twin: a
horizon covering `prologue + blockLen·(20+9p) + epilogue` covers the segment's run.  As
in §C12, the envelope absorption is `envE_absorb`'s and is not re-proved here. -/
theorem estFuel_fits {h : Nat → Nat} {baseV baseA stride p r pro epi T : Nat} {n : Nat}
    (hT : pro + n * (20 + 9 * p) + epi ≤ T) :
    pro + estFuel h baseV baseA stride p r n + epi ≤ T := by
  have := estFuel_le h baseV baseA stride p r n
  omega

/-! ### §C13.2b — the `stride`-word charge, and why it is a bound and not the cost

`scanWordOpsWide` (`KapilaWide` §W5) is `blockLen · (2·stride + 3)`: `blockLen` estimates
each reading `stride` words per side.  That is the charge of the **whole-block** read.
`numAt_not_word` proves such a numerator does not fit a state word, so the digitwise
segment performs the read at its digit count instead — one word per side per digit
position — which is the same shape at `p + 1` visits. -/

/-- **The digitwise charge *is* the wide shape at the digit count.**  So §C13.2's
measurement is a substitution into the landed cost model, not a new model. -/
theorem digitwise_is_wide_at_digit (blockLen p : Nat) :
    scanWordOpsWide blockLen (p + 1) = blockLen * (2 * (p + 1) + 3) := rfl

/-- **The digitwise read never costs more than the whole-block read** — the honest form
of "charge `stride` words per estimate": it is an upper bound on what the segment pays,
reached only when the comparison visits every word of both blocks.  `p + 1 ≤ stride` is
the block fit `payloadStride_fits_digit` supplies. -/
theorem digitwiseWordOps_le_wide (blockLen p stride : Nat) (hp : p + 1 ≤ stride) :
    blockLen * (2 * (p + 1) + 3) ≤ scanWordOpsWide blockLen stride := by
  unfold scanWordOpsWide
  exact Nat.mul_le_mul_left blockLen (by omega)

end SubsetSumL25.Row
