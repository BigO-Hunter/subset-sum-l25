/-
§7 step 7's scan — **the first backwards jump in this calculus**: the loop, its
three exit equations, and its word-operation cost.

Why this file exists.  `KapilaTest` fixed exactly what an instruction-level proof
of the test segment must establish: a `PayloadConvention` carrying the two
estimate blocks, whose verdict obeys the three rules
(`rule_nil_left`, `rule_nil_right`, `rule_cons_cons`) — and `payload_rules_iff`
proved that this rule set *is* `rowTest`, so the equations determine the verdict
and nothing weaker will do.  What it did not have was a loop: `payloadBlock`'s
layout is static (a fixed number of words read from fixed addresses), and every
program in the lane so far has been straight-line — `prelimProg`, `aliasProg`,
`checksumProg` are 17, 20 and 24 instructions with no jump backwards anywhere.

This file lands the loop:

1. **The calculus's loop rule, and the semantics it relies on** (§L0).  `blt`'s
   target is an *absolute* program position with no forward-only restriction, so
   a backwards jump is an ordinary instruction; and `exec` has no other
   termination mechanism than its fuel, so a runaway loop *rejects* rather than
   looping (`selfLoop_never_halts`).  Both are stated as lemmas rather than
   assumed, because the lane's previous texts give no evidence either way.
2. **`scanProg`** — §7 step 7 as instruction text: 21 instructions, one backwards
   jump at `pc 17` back to the loop head at `pc 4`, and a *uniform* 12 steps per
   iteration (the branch that picks `v − a` or `a − v` is padding-balanced, so the
   iteration cost does not depend on the data — that is what makes the fuel
   arithmetic a multiplication instead of a sum of data-dependent terms).
3. **The per-pair comparison, in §6.2's own layout** (§L2–§L3).  The estimate is
   a word at `n²` fractional bits, so `|V̂ − Â| ≥ 1/2` is *integer* comparison
   against `2^(n²−1)`; `hitWord` computes it with two subtractions and two
   divisions, and `hitWord_eq_ratTest` proves the computed word is the paper's
   test.  No branch on sign of a real: the division `(d/h)/(d/h)` is `1` exactly
   when `h ≤ d` and `0` otherwise (division by zero is `0` in this calculus, which
   is exactly the `d < h` case).
4. **The three equations at the segment's exit** (§L5).  `scan_fold_rules` states
   nil/nil, nil/cons and cons/cons *of the object the instruction text computes*,
   in `payload_rules_iff`'s exact `ℚ` vocabulary; `anyHit_eq_rowTest` turns those
   three equations into `rowTest`; and `scan_run_eq_rowTest` puts the program's
   run on the left of that equation.  Together: the loop's exit is a
   `PayloadConvention` whose payloads are the memory's blocks.
   The run is assembled in §L8 — `scan_prologue` (the four `pc 0 → pc 4`
   instructions) + `scan_loop` at `m = N` + `scan_epilogue`, one statement at
   fuel `12·N + 6` — so `scan_run_eq_rowTest` is a statement about the *whole*
   program on `memOf w f0`, not about a suffix of it.
5. **The word-operation cost model** (§L8, closing comment), in §6.2's
   `n²`-fractional-bits vocabulary: the single-word regime's exact `Instr`-step
   count (`12·blockLen + 6`), the multi-word charge (`wordOpFactor` per iteration,
   since a comparison of two `n²`-bit dyadics is itself a loop of `⌈n²/w⌉ + 1 ≤
   wordOpFactor n` word-visits), and the absorption — `scan_cost_absorbed` shows
   the whole charge lands inside §7's envelope with the existential `K` raised by
   seven, so the loop does not move the row's `2^{(τ₀+20ε)n}` exponent.  This is
   the same argument as the `wordOpFactor`/`withinEnvelope_wordop_absorb`
   machinery of `KapilaAlgo`, at a larger exponent (the scan's charge carries
   `wordOpFactor` squared), applied to a segment that actually exists.  **Stated,
   not proved** — see §L8's closing comment for the exact call site and why the
   `+3` lemma cannot be cited directly.

What is *not* here, stated so the residual is bounded and exact:

1. **The word-operation cost model** (piece 3 of the original trio; pieces 1 and 2
   landed in §L8).  The exact `Instr`-step count *is* landed — it is `scan_run`'s
   fuel `12·N + 6`.  What remains is the multi-word charge: §6.2's `n²`-bit dyadic
   comparison is itself a loop of `⌈n²/w⌉ + 1 ≤ wordOpFactor n` word-visits, so the
   per-pair word-op charge is `2·wordOpFactor n + 3` and the total is
   `blockLen·(2·wordOpFactor n + 3)`.  The absorption is then
   `KapilaAlgo.withinEnvelope_wordop_absorb`'s argument with the polynomial
   exponent raised by seven (one `wordOpFactor²` from the nested loop, five from
   `wordOpFactor ≤ (n+b+2)^3` squared times the constant `5`), i.e. `K + 7` rather
   than `K + 3`.  **Not landed**: the two lemmas
   (`scanWordOps_le : blockLen·(2·wordOpFactor n + 3) ≤ (n+b+2)^7` and
   `scan_cost_absorbed : (R.cost + scanWordOps ≤ K₀·2^E·P^(K+7))`) — stated
   precisely, proved not yet.
2. **The multi-word accumulator layout** (`LeafTest`'s item 4) and **the
   estimates' arithmetic relation** (item 3) are untouched, as before.

Statement.lean's hashes are untouched (`3dc6567e…34aa`): this module adds names
only, and it is a leaf of the import DAG.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaRow
import SubsetSumL25.Row.KapilaPrelim
import SubsetSumL25.Row.KapilaTest

set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §L0 — the backwards jump: what the calculus does and does not say

The lane's previous programs never jump backwards, so these two lemmas are the
new ground.  `Instr.blt (i j : Nat) (l : Nat)` carries `l` as an **absolute
program position**: `exec` sets `pc := l` when `[i] < [j]` and `pc := pc + 1`
otherwise, with no test of `l` against `pc`.  Two consequences the loop proofs
below rely on:

* the ported peeler `exec_blt_lt_step` needs **no hypothesis on `l`**, so a
  backwards jump is discharged by the same lemma as a forward one (this is what
  `scan_iter` uses at `l = 4 < pc = 17`);
* `exec` decrements its fuel on every instruction including the jump, and `exec`
  at fuel `0` is `none`.  There is therefore **no other termination mechanism**:
  a loop that never fails its exit test runs out of fuel and *rejects*.  The loop
  below terminates because its counter strictly increases, not because the
  calculus knows anything about loops. -/

/-- `2^w` is positive — `omega` cannot see it (the power is an opaque atom). -/
theorem twoPowPos (w : Nat) : 0 < 2 ^ w := Nat.two_pow_pos w

/-- **The fuel is the loop bound.** -/
theorem selfLoop_never_halts {w : Nat} (ρ : Nat → BitVec w) (f : Nat → Nat)
    (hw : 1 ≤ w) (h0 : f 0 = 0) (h1 : f 1 = 1) (r : Nat) :
    ∀ t : Nat,
      exec [Instr.blt 0 1 0] ρ t 0 r (memOf w f) = none := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    have hcond : (memOf w f 0 : BitVec w) < memOf w f 1 := by
      have hp0 : f 0 < 2 ^ w := by rw [h0]; exact twoPowPos w
      have hp1 : f 1 < 2 ^ w := by
        rw [h1]
        have hp : (2 : Nat) ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
        omega
      show BitVec.ofNat w (f 0) < BitVec.ofNat w (f 1)
      rw [ofNat_lt_ofNat hp0 hp1, h0, h1]
      omega
    show exec [Instr.blt 0 1 0] ρ t
      (if (memOf w f 0 : BitVec w) < memOf w f 1 then 0 else 0 + 1) r (memOf w f) = none
    rw [if_pos hcond]
    exact ih

/-! ### §L1 — two ported peelers (`sub`, `div`) and their word lemmas

`prelimProg`/`aliasProg`/`checksumProg` need only `one`, `add`, `shr`, `load`,
`store`, `blt`, `accept`, `reject`, so the lane's calculus had no `sub` or `div`
peeler.  The scan needs both: the difference of two estimates, and the branchless
`(d/h)/(d/h)` hit test. -/

/-- The word of a difference, when the subtraction does not borrow. -/
theorem bv_sub {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hba : b ≤ a) :
    BitVec.ofNat w a - BitVec.ofNat w b = BitVec.ofNat w (a - b) := by
  rw [BitVec.toNat_eq]
  have hne : (2 ^ w - b + a) % 2 ^ w = (a - b) % 2 ^ w := by
    have h1 : 2 ^ w - b + a = 2 ^ w + (a - b) := by omega
    rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hlt : a - b < 2 ^ w := by omega
  rw [hne, Nat.mod_eq_of_lt hlt]
  exact (Nat.mod_eq_of_lt hlt).symm

/-- The word of a quotient. -/
theorem bv_div {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    BitVec.ofNat w a / BitVec.ofNat w b = BitVec.ofNat w (a / b) := by
  rw [BitVec.toNat_eq]
  rw [BitVec.udiv_def]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

section StepLemmas

variable {w : Nat} {P : List Instr} {ρ : Nat → BitVec w} {S pc r : Nat} {f : Nat → Nat}

theorem exec_sub_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.sub i j k)
    (hfit : ∀ x, f x < 2 ^ w) (hge : f k ≤ f j) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i (f j - f k))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;> simp [memOf, up, hxi, bv_sub (hfit j) (hfit k) hge]

theorem exec_div_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.div i j k)
    (hfit : ∀ x, f x < 2 ^ w) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i (f j / f k))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;> simp [memOf, up, hxi, bv_div (hfit j) (hfit k)]

end StepLemmas

/-- The fixed-point scaler: a payload word `a` at `fracBits` fractional bits is
the `ℚ` value `a / 2^fracBits`.  Named (rather than written inline as a lambda)
so that the `map`/`zipWith` transport lemmas below match on a single symbol. -/
def toQ (fracBits a : Nat) : ℚ := (a : ℚ) / (2 : ℚ) ^ fracBits

/-! ### §L2 — the block the loop walks

`payloadBlock` (`KapilaTest`) reads `len` words at a fixed base.  The loop needs
the same block in `ℕ` form — the memory's words as `ℕ`s — because the arithmetic
it proves is `ℕ`-arithmetic on `memOf`. -/

/-- The `len` words starting at `base`, as `ℕ`s: the loop's read vocabulary. -/
def wordList (f : Nat → Nat) (base len : Nat) : List Nat :=
  (List.range len).map fun j => f (base + j)

@[simp] theorem wordList_zero (f : Nat → Nat) (base : Nat) : wordList f base 0 = [] := rfl

/-- **The block's cons rule**: the first word is at `base`, the rest is the same
block one address along.  This is what turns one loop iteration into one list
step, and it is the only list arithmetic the loop needs. -/
theorem wordList_succ (f : Nat → Nat) (base len : Nat) :
    wordList f base (len + 1) = f base :: wordList f (base + 1) len := by
  unfold wordList
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  exact congrArg f (by omega : base + Nat.succ j = base + 1 + j)

/-- `map` of a `map` — proved by induction rather than quoted, because the
library's `List.map_map` is stated through `Function.comp` and does not match
under this pin's `Functor.map` presentation of `List.map`. -/
theorem map_map' {α β γ : Type} (f : β → γ) (g : α → β) (l : List α) :
    (l.map g).map f = l.map (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [List.map_cons, List.map_cons, ih]; rfl

/-- The block read off `memOf` is the `ℚ`-scaled block `payloadBlock` reads, when
every word fits a word.  This is the bridge between the loop's `ℕ` arithmetic and
`KapilaTest`'s `Ahat`/`Vhat`. -/
theorem payloadBlock_memOf {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (fracBits base len : Nat) :
    payloadBlock fracBits base len (memOf w f) = (wordList f base len).map (toQ fracBits) := by
  unfold payloadBlock wordList
  rw [map_map']
  apply List.map_congr_left
  intro j _
  have hval : (memOf w f (base + j)).toNat = f (base + j) := by
    show (BitVec.ofNat w (f (base + j))).toNat = f (base + j)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfit (base + j))]
  rw [hval]
  rfl

/-! ### §L3 — the per-pair test, computed

§6.2 carries the estimates at `n²` fractional bits, so a payload word `x` is the
`ℚ` value `x / 2^{n²}` and the comparison `|V̂ − Â| ≥ 1/2` is the *integer*
statement `2^{n²−1} ≤ |V − A|` on the words.  `hitWord` computes it in the
instruction set: `diff` with one `blt`, then `(d/h)/(d/h)` — `1` exactly when
`h ≤ d`, and `0` when `d < h` because this calculus's division by a larger word
is zero (`[j] / 0 = 0`, and `d / h = 0` for `d < h`). -/

/-- `|v − a|` on words: the branch the program takes at `pc 8`. -/
def wordDiff (v a : Nat) : Nat := if v < a then a - v else v - a

/-- `1` iff `h ≤ d`, `0` otherwise — the branchless comparison, as two divisions. -/
def hitOf (d h : Nat) : Nat := (d / h) / (d / h)

/-- The per-pair hit: §7 step 7's test for one index, in words. -/
def hitWord (h v a : Nat) : Nat := hitOf (wordDiff v a) h

theorem hitOf_eq_one {d h : Nat} (hh : 1 ≤ h) (hd : h ≤ d) : hitOf d h = 1 := by
  unfold hitOf
  have h1 : 1 ≤ d / h := (Nat.one_le_div_iff (by omega)).mpr hd
  exact Nat.div_self (by omega)

theorem hitOf_eq_zero {d h : Nat} (hd : d < h) : hitOf d h = 0 := by
  unfold hitOf
  rw [Nat.div_eq_of_lt hd]

theorem hitOf_le_one (d h : Nat) : hitOf d h ≤ 1 := by
  unfold hitOf
  by_cases h0 : d / h = 0
  · rw [h0, Nat.zero_div]
    exact Nat.zero_le 1
  · exact Nat.le_of_eq (Nat.div_self (Nat.pos_of_ne_zero h0))

theorem hitWord_le_one (h v a : Nat) : hitWord h v a ≤ 1 := hitOf_le_one _ _

/-- **`hitWord` is the indicator of `h ≤ |v − a|`.** -/
theorem hitWord_eq_one_iff {h v a : Nat} (hh : 1 ≤ h) :
    hitWord h v a = 1 ↔ h ≤ wordDiff v a := by
  unfold hitWord
  by_cases hd : h ≤ wordDiff v a
  · exact ⟨fun _ => hd, fun _ => hitOf_eq_one hh hd⟩
  · have hlt : wordDiff v a < h := by omega
    exact ⟨fun h1 => by rw [hitOf_eq_zero hlt] at h1; exact absurd h1 (by decide), fun hc => absurd hc hd⟩

/-- The branch at `pc 8` splits `|v − a|` into its two cases, and `wordDiff` is
exactly the value the taken path produces. -/
theorem wordDiff_of_lt {v a : Nat} (h : v < a) : wordDiff v a = a - v := by
  unfold wordDiff
  exact if_pos h

theorem wordDiff_of_ge {v a : Nat} (h : ¬ v < a) : wordDiff v a = v - a := by
  unfold wordDiff
  exact if_neg h

/-- **The computed hit is the paper's test**, in the fixed-point layout: with
`h = 2^{fracBits−1}` and both operands at `fracBits` fractional bits,
`hitWord = 1` exactly when `|V̂ − Â| ≥ 1/2`.  This is the equation that lets the
loop's `ℕ` arithmetic be stated in `payload_rules_iff`'s `ℚ` vocabulary. -/
theorem hitWord_eq_ratTest {fracBits : Nat} (hf : 1 ≤ fracBits) (V A : Nat) :
    hitWord (2 ^ (fracBits - 1)) V A = 1
      ↔ (1 / 2 : ℚ) ≤ |(V : ℚ) / (2 : ℚ) ^ fracBits - (A : ℚ) / (2 : ℚ) ^ fracBits| := by
  have hpos : (0 : ℚ) < (2 : ℚ) ^ fracBits := by positivity
  have hpc : (((2 : Nat) ^ (fracBits - 1) : Nat) : ℚ) = (2 : ℚ) ^ (fracBits - 1) := by
    push_cast
    rfl
  -- the ℚ side, reduced to the integer comparison at the scale `2^(fracBits-1)`
  have hkey : ((1 / 2 : ℚ) ≤
        |(V : ℚ) / (2 : ℚ) ^ fracBits - (A : ℚ) / (2 : ℚ) ^ fracBits|)
      ↔ ((2 : ℚ) ^ (fracBits - 1) ≤ ((wordDiff V A : Nat) : ℚ)) := by
    have hpow : (2 : ℚ) ^ fracBits = (2 : ℚ) ^ (fracBits - 1) * 2 := by
      conv_lhs => rw [show fracBits = (fracBits - 1) + 1 from by omega]
      rw [pow_succ]
    have hhalf : (1 / 2 : ℚ) * ((2 : ℚ) ^ (fracBits - 1) * 2) = (2 : ℚ) ^ (fracBits - 1) := by
      ring
    have habs : |(V : ℚ) / (2 : ℚ) ^ fracBits - (A : ℚ) / (2 : ℚ) ^ fracBits|
        = |(V : ℚ) - (A : ℚ)| / (2 : ℚ) ^ fracBits := by
      rw [← sub_div, abs_div, abs_of_pos hpos]
    rw [habs, le_div_iff₀ hpos, hpow, hhalf]
    rcases Nat.lt_or_ge V A with hlt | hge
    · have hcast : ((A - V : Nat) : ℚ) = (A : ℚ) - (V : ℚ) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
      have hd : |(V : ℚ) - (A : ℚ)| = ((A - V : Nat) : ℚ) := by
        rw [hcast, abs_of_neg (by
          have hVQ : (V : ℚ) < (A : ℚ) := by exact_mod_cast hlt
          linarith)]
        ring
      rw [hd, wordDiff_of_lt hlt, ← hpc, Nat.cast_le]
    · have hcast : ((V - A : Nat) : ℚ) = (V : ℚ) - (A : ℚ) := by
        rw [Nat.cast_sub hge]
      have hd : |(V : ℚ) - (A : ℚ)| = ((V - A : Nat) : ℚ) := by
        rw [hcast, abs_of_nonneg (by
          have hAQ : (A : ℚ) ≤ (V : ℚ) := by exact_mod_cast hge
          linarith)]
      rw [hd, wordDiff_of_ge (by omega : ¬ V < A), ← hpc, Nat.cast_le]
  rw [hkey, hitWord_eq_one_iff Nat.one_le_two_pow, ← hpc, Nat.cast_le]

/-! ### §L4 — the loop's specification: the hit count over the remaining block

The accumulator is a *count*: the segment adds `1` per hit rather than OR-ing a
boolean, because `add` is the one word operation whose peeler the lane already
had.  The verdict is then `0 < count`, which is the same test. -/

/-- The per-pair hits over two blocks, summed — what the accumulator holds after
the loop. -/
def hitCount (h : Nat) : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | v :: vs, a :: as_ => hitWord h v a + hitCount h vs as_

/-- The same fold in `Bool`, for the comparison with `rowTest`. -/
def anyHit (h : Nat) : List Nat → List Nat → Bool
  | [], _ => false
  | _, [] => false
  | v :: vs, a :: as_ => decide (hitWord h v a = 1) || anyHit h vs as_

theorem hitCount_succ (h v : Nat) (vs : List Nat) (a : Nat) (as_ : List Nat) :
    hitCount h (v :: vs) (a :: as_) = hitWord h v a + hitCount h vs as_ := rfl

theorem anyHit_succ (h v : Nat) (vs : List Nat) (a : Nat) (as_ : List Nat) :
    anyHit h (v :: vs) (a :: as_) = (decide (hitWord h v a = 1) || anyHit h vs as_) := rfl

/-- **`anyHit` as a zip over the two blocks** — the form `rowTest` reads. -/
theorem anyHit_eq_zipWith (h : Nat) (V A : List Nat) :
    anyHit h V A = (A.zipWith (fun a v => decide (hitWord h v a = 1)) V).any id := by
  induction V generalizing A with
  | nil => cases A <;> rfl
  | cons v vs ih =>
    cases A with
    | nil => rfl
    | cons a as_ => rw [anyHit_succ, ih as_]; rfl

/-- A hit count is positive exactly when some pair hit. -/
theorem hitCount_pos_iff (h : Nat) (V A : List Nat) :
    0 < hitCount h V A ↔ anyHit h V A = true := by
  induction V generalizing A with
  | nil => cases A with
    | nil => simp [hitCount, anyHit]
    | cons a as_ => simp [hitCount, anyHit]
  | cons v vs ih =>
    cases A with
    | nil => simp [hitCount, anyHit]
    | cons a as_ =>
      have hle := hitWord_le_one h v a
      rw [hitCount_succ, anyHit_succ, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · intro hpos
        by_cases hz : hitWord h v a = 1
        · exact Or.inl hz
        · refine Or.inr ?_
          have h0 : hitWord h v a = 0 := by omega
          exact (ih as_).mp (by omega)
      · rintro (hz | hr)
        · omega
        · have := (ih as_).mpr hr
          omega

/-- **The three exit equations**, in `payload_rules_iff`'s vocabulary, proved of
the object the instruction text computes.  The right-hand side is the paper's own
test on the `ℚ` estimates: `hb` is `hitWord_eq_ratTest`, instantiated at the
layout's `h = 2^{fracBits−1}`.  So the loop's exit establishes exactly the three
equations `payload_rules_iff` names — nil/nil (each empty case is the fold's own
base), nil/cons, and cons/cons (one pair's comparison, then the rest). -/
theorem scan_fold_rules {fracBits h : Nat}
    (hb : ∀ v a, hitWord h v a = 1
      ↔ (1 / 2 : ℚ) ≤ |(v : ℚ) / (2 : ℚ) ^ fracBits - (a : ℚ) / (2 : ℚ) ^ fracBits|) :
    (∀ V : List Nat, anyHit h [] V = false) ∧
    (∀ A : List Nat, anyHit h A [] = false) ∧
    (∀ (a : Nat) (A : List Nat) (v : Nat) (V : List Nat),
      anyHit h (v :: V) (a :: A)
        = (decide ((1 / 2 : ℚ) ≤
              |toQ fracBits v - toQ fracBits a|)
            || anyHit h V A)) := by
  refine ⟨fun V => by cases V <;> rfl, fun A => by cases A <;> rfl, fun a A v V => ?_⟩
  rw [anyHit_succ]
  have hstep : decide (hitWord h v a = 1)
      = decide ((1 / 2 : ℚ) ≤
          |toQ fracBits v - toQ fracBits a|) := by
    by_cases hz : hitWord h v a = 1
    · have hq : (1 / 2 : ℚ) ≤
          |toQ fracBits v - toQ fracBits a| := (hb v a).mp hz
      rw [decide_eq_true hz, decide_eq_true hq]
    · have hq : ¬ ((1 / 2 : ℚ) ≤
          |toQ fracBits v - toQ fracBits a|) :=
        fun hc => hz ((hb v a).mpr hc)
      rw [decide_eq_false hz, decide_eq_false hq]
  rw [hstep]

/-- `zipWith` of two mapped lists is a `zipWith` of the composites. -/
theorem zipWith_map_map' {α β : Type} (f : Nat → α) (g : Nat → β) (hh : α → β → Bool)
    (l₁ l₂ : List Nat) :
    (l₁.map f).zipWith hh (l₂.map g) = l₁.zipWith (fun a b => hh (f a) (g b)) l₂ := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons a as_ ih =>
    cases l₂ with
    | nil => rfl
    | cons b bs => rw [List.map_cons, List.map_cons, List.zipWith_cons_cons,
        List.zipWith_cons_cons, ih]

/-- Pointwise equality of the pair test transports through the `any`. -/
theorem any_zipWith_congr {α : Type} (g₁ g₂ : Nat → α → Bool) (l₁ : List Nat) (l₂ : List α)
    (hpt : ∀ a b, g₁ a b = g₂ a b) :
    (l₁.zipWith g₁ l₂).any id = (l₁.zipWith g₂ l₂).any id := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons a as_ ih =>
    cases l₂ with
    | nil => rfl
    | cons b bs => rw [List.zipWith_cons_cons, List.zipWith_cons_cons, List.any_cons,
        List.any_cons, hpt a b, ih bs]

/-- **The three equations determine the test**: the segment's verdict is §7 step
7's `rowTest` on the two blocks.  (`rowTest_eq_of_rules` is the uniqueness half of
`payload_rules_iff`; this proves the *value*, which is what the instruction text
computes.) -/
theorem anyHit_eq_rowTest {fracBits h : Nat}
    (hb : ∀ v a, hitWord h v a = 1
      ↔ (1 / 2 : ℚ) ≤ |(v : ℚ) / (2 : ℚ) ^ fracBits - (a : ℚ) / (2 : ℚ) ^ fracBits|)
    (V A : List Nat) :
    anyHit h V A
      = Routines.rowTest (A.map (toQ fracBits)) (V.map (toQ fracBits)) := by
  rw [anyHit_eq_zipWith, Routines.rowTest, zipWith_map_map']
  apply any_zipWith_congr
  intro a v
  by_cases hz : hitWord h v a = 1
  · have hq : (1 / 2 : ℚ) ≤
        |toQ fracBits v - toQ fracBits a| := (hb v a).mp hz
    rw [decide_eq_true hz, decide_eq_true hq]
  · have hq : ¬ ((1 / 2 : ℚ) ≤
        |toQ fracBits v - toQ fracBits a|) :=
      fun hc => hz ((hb v a).mpr hc)
    rw [decide_eq_false hz, decide_eq_false hq]

/-! ### §L5 — the program: 21 instructions, one backwards jump

The loop's cells: `0` counter, `1` the constant one, `2` the block length, `3` the
accumulator, `4`/`5` the two block bases, `6` the threshold word `2^{fracBits−1}`,
`7`/`8` address scratch, `9`/`10` the two estimates, `11` their difference, `12`
the constant zero, `13` the branchless hit.  Everything the loop writes is at
`0`, `3`, or in `7 … 13`; the payload blocks live at `14` and above, so the loop is
**transparent on the payload** (that is `Scratch`'s content).

The two paths through `pc 8`–`pc 12` are **padded to the same length** (two
instructions each, both landing on `pc 13`), so one iteration is exactly 12 steps
whatever the data — that is what makes the loop's fuel a multiplication. -/

/-- §7 step 7 as instruction text.  The backwards jump is at `pc 17`, back to the
head at `pc 4`. -/
def scanProg : List Instr :=
  [ Instr.one 1,          -- 0  [1] := 1
    Instr.sub 12 1 1,     -- 1  [12] := 0
    Instr.sub 3 1 1,      -- 2  acc := 0
    Instr.sub 0 1 1,      -- 3  k := 0
    Instr.add 7 4 0,      -- 4  head: addrA := baseA + k
    Instr.load 10 7,      -- 5  a := [addrA]
    Instr.add 8 5 0,      -- 6  addrV := baseV + k
    Instr.load 9 8,       -- 7  v := [addrV]
    Instr.blt 9 10 11,    -- 8  if v < a goto 11
    Instr.sub 11 9 10,    -- 9  d := v - a
    Instr.blt 12 1 13,    -- 10 if 0 < 1 goto 13
    Instr.sub 11 10 9,    -- 11 d := a - v
    Instr.blt 12 1 13,    -- 12 if 0 < 1 goto 13
    Instr.div 13 11 6,    -- 13 t := d / h
    Instr.div 13 13 13,   -- 14 t := t / t      (1 iff h ≤ d)
    Instr.add 3 3 13,     -- 15 acc := acc + t
    Instr.add 0 0 1,      -- 16 k := k + 1
    Instr.blt 0 2 4,      -- 17 if k < N goto 4  ← THE BACKWARDS JUMP
    Instr.blt 12 3 20,    -- 18 if 0 < acc goto 20
    Instr.reject,         -- 19
    Instr.accept ]        -- 20

/-- The cells the loop writes: the counter, the accumulator, and `7 … 13`.  Every
cell outside this set is preserved by one iteration — in particular the payload
blocks at `14` and above. -/
def Scratch (z : Nat) : Prop :=
  z = 0 ∨ z = 3 ∨ z = 7 ∨ z = 8 ∨ z = 9 ∨ z = 10 ∨ z = 11 ∨ z = 13

theorem scratch_payload {base k : Nat} (hb : 14 ≤ base) : ¬ Scratch (base + k) := by
  unfold Scratch
  omega

theorem scratch_const_one : ¬ Scratch 1 := by unfold Scratch; omega
theorem scratch_const_two : ¬ Scratch 2 := by unfold Scratch; omega
theorem scratch_const_four : ¬ Scratch 4 := by unfold Scratch; omega
theorem scratch_const_five : ¬ Scratch 5 := by unfold Scratch; omega
theorem scratch_const_six : ¬ Scratch 6 := by unfold Scratch; omega
theorem scratch_const_twelve : ¬ Scratch 12 := by unfold Scratch; omega
theorem scratch_seven : Scratch 7 := by unfold Scratch; omega
theorem scratch_eight : Scratch 8 := by unfold Scratch; omega
theorem scratch_nine : Scratch 9 := by unfold Scratch; omega
theorem scratch_ten : Scratch 10 := by unfold Scratch; omega
theorem scratch_eleven : Scratch 11 := by unfold Scratch; omega
theorem scratch_thirteen : Scratch 13 := by unfold Scratch; omega
theorem scratch_zero : Scratch 0 := by unfold Scratch; omega
theorem scratch_three : Scratch 3 := by unfold Scratch; omega

/-- The memory layout the scan requires: the six read-only constants, and the two
payload blocks at `14` and above. -/
def Layout (f0 : Nat → Nat) (N h baseA baseV : Nat) : Prop :=
  f0 1 = 1 ∧ f0 2 = N ∧ f0 4 = baseA ∧ f0 5 = baseV ∧ f0 6 = h ∧ f0 12 = 0
    ∧ 14 ≤ baseA ∧ 14 ≤ baseV

/-- The loop invariant at the head (`pc 4`): the counter, the accumulator, the
accumulator's bound (at most one hit per iteration), agreement with the entry
memory off the written cells, and the word fit. -/
def LoopInv (w : Nat) (f0 f : Nat → Nat) (k acc : Nat) : Prop :=
  f 0 = k ∧ f 3 = acc ∧ acc ≤ k ∧ (∀ z, ¬ Scratch z → f z = f0 z) ∧ ∀ z, f z < 2 ^ w

/-- One iteration writes only scratch cells, so agreement survives it. -/
theorem agree_up {f0 g : Nat → Nat} {c v : Nat} (hc : Scratch c)
    (hg : ∀ z, ¬ Scratch z → g z = f0 z) :
    ∀ z, ¬ Scratch z → up g c v z = f0 z := by
  intro z hz
  rw [up]
  by_cases h : z = c
  · exact absurd (h ▸ hc) hz
  · rw [if_neg h]
    exact hg z hz

section Scan

variable {w : Nat} {ρ : Nat → BitVec w}

/-- **The head, walked** (`pc 4 → pc 8`, 4 steps): both addresses, both estimates
in cells `9`/`10`, and the invariant's agreement/fit re-established. -/
theorem scan_head {f0 f : Nat → Nat} {N h baseA baseV k acc : Nat}
    (hL : Layout f0 N h baseA baseV) (hinv : LoopInv w f0 f k acc)
    (hk : k < N) (hN : N < 2 ^ w) (hbA : baseA + N < 2 ^ w) (hbV : baseV + N < 2 ^ w)
    (S : Nat) :
    ∃ f', (f' 0 = k ∧ f' 2 = N ∧ f' 4 = baseA ∧ f' 5 = baseV ∧ f' 6 = h ∧ f' 12 = 0
        ∧ f' 1 = 1 ∧ f' 9 = f0 (baseV + k) ∧ f' 10 = f0 (baseA + k)
        ∧ (∀ z, ¬ Scratch z → f' z = f0 z) ∧ (∀ z, f' z < 2 ^ w) ∧ f' 3 = acc)
      ∧ exec scanProg ρ (S + 4) 4 0 (memOf w f) = exec scanProg ρ S 8 0 (memOf w f') := by
  obtain ⟨h0, h3, hacc, hagree, hfit⟩ := hinv
  obtain ⟨hc1, hc2, hc4, hc5, hc6, hc12, hbA14, hbV14⟩ := hL
  have hf1 : f 1 = 1 := by rw [hagree 1 scratch_const_one]; exact hc1
  have hf2 : f 2 = N := by rw [hagree 2 scratch_const_two]; exact hc2
  have hf4 : f 4 = baseA := by rw [hagree 4 scratch_const_four]; exact hc4
  have hf5 : f 5 = baseV := by rw [hagree 5 scratch_const_five]; exact hc5
  have hf6 : f 6 = h := by rw [hagree 6 scratch_const_six]; exact hc6
  have hf12 : f 12 = 0 := by rw [hagree 12 scratch_const_twelve]; exact hc12
  have haddrA : baseA + k < 2 ^ w := by omega
  have haddrV : baseV + k < 2 ^ w := by omega
  have d4 : scanProg.getD 4 Instr.reject = Instr.add 7 4 0 := rfl
  rw [exec_add_step (S := S + 4) (hS := by omega) d4]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have v4 : f 4 + f 0 = baseA + k := by rw [hf4, h0]
  rw [v4]
  set s1 : Nat → Nat := up f 7 (baseA + k) with hs1
  have hf1' : ∀ z, s1 z < 2 ^ w := upFit hfit haddrA
  have ha1 : ∀ z, ¬ Scratch z → s1 z = f0 z := agree_up scratch_seven hagree
  have d5 : scanProg.getD 5 Instr.reject = Instr.load 10 7 := rfl
  rw [exec_load_step (S := S + 3) (hS := by omega) d5 hf1']
  rw [show S + 3 - 1 = S + 2 from rfl]
  have v5 : s1 (s1 7) = f (baseA + k) := by
    have e7 : s1 7 = baseA + k := up_eq f 7 (baseA + k)
    rw [e7]
    exact up_ne (by omega : ¬ (baseA + k = 7))
  rw [v5]
  set s2 : Nat → Nat := up s1 10 (f (baseA + k)) with hs2
  have hf2' : ∀ z, s2 z < 2 ^ w := upFit hf1' (hfit (baseA + k))
  have ha2 : ∀ z, ¬ Scratch z → s2 z = f0 z := agree_up scratch_ten ha1
  have d6 : scanProg.getD 6 Instr.reject = Instr.add 8 5 0 := rfl
  rw [exec_add_step (S := S + 2) (hS := by omega) d6]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v6 : s2 5 + s2 0 = baseV + k := by
    have e5 : s2 5 = baseV := by
      rw [hs2, up_ne (by decide : (5 : Nat) ≠ 10), hs1, up_ne (by decide : (5 : Nat) ≠ 7)]
      exact hf5
    have e0 : s2 0 = k := by
      rw [hs2, up_ne (by decide : (0 : Nat) ≠ 10), hs1, up_ne (by decide : (0 : Nat) ≠ 7)]
      exact h0
    rw [e5, e0]
  rw [v6]
  set s3 : Nat → Nat := up s2 8 (baseV + k) with hs3
  have hf3' : ∀ z, s3 z < 2 ^ w := upFit hf2' haddrV
  have ha3 : ∀ z, ¬ Scratch z → s3 z = f0 z := agree_up scratch_eight ha2
  have d7 : scanProg.getD 7 Instr.reject = Instr.load 9 8 := rfl
  rw [exec_load_step (S := S + 1) (hS := by omega) d7 hf3']
  rw [show S + 1 - 1 = S + 0 from rfl]
  have v7 : s3 (s3 8) = f (baseV + k) := by
    have e8 : s3 8 = baseV + k := up_eq s2 8 (baseV + k)
    rw [e8, hs3, up_ne (by omega : ¬ (baseV + k = 8)),
      hs2, up_ne (by omega : ¬ (baseV + k = 10)),
      hs1, up_ne (by omega : ¬ (baseV + k = 7))]
  rw [v7]
  refine ⟨up s3 9 (f (baseV + k)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hs1, hs2, hs3, up, h0]
  · simp [hs1, hs2, hs3, up, hf2]
  · simp [hs1, hs2, hs3, up, hf4]
  · simp [hs1, hs2, hs3, up, hf5]
  · simp [hs1, hs2, hs3, up, hf6]
  · simp [hs1, hs2, hs3, up, hf12]
  · simp [hs1, hs2, hs3, up, hf1]
  · simp [up, hagree (baseV + k) (scratch_payload hbV14)]
  · simp [hs1, hs2, hs3, up, hagree (baseA + k) (scratch_payload hbA14)]
  · intro z hz
    exact agree_up scratch_nine ha3 z hz
  · exact ⟨upFit hf3' (hfit (baseV + k)), by simp [hs1, hs2, hs3, up, h3]⟩
  · simp


variable {f0 : Nat → Nat} {N h baseA baseV : Nat}

/-- **The taken branch** (`v < a`): `pc 8 → pc 13` in 3 steps, `d := a − v`. -/
theorem scan_branch_lt {f : Nat → Nat} {k acc : Nat}
    (h0 : f 0 = k) (h1 : f 1 = 1) (h3 : f 3 = acc) (h6 : f 6 = h) (h12 : f 12 = 0)
    (h9 : f 9 = f0 (baseV + k)) (h10 : f 10 = f0 (baseA + k))
    (hlt : f0 (baseV + k) < f0 (baseA + k))
    (hagree : ∀ z, ¬ Scratch z → f z = f0 z) (hfit : ∀ z, f z < 2 ^ w)
    (hpa : f0 (baseA + k) < 2 ^ w) (hpv : f0 (baseV + k) < 2 ^ w) (S : Nat) :
    ∃ f', (f' 11 = f0 (baseA + k) - f0 (baseV + k) ∧ f' 0 = k ∧ f' 1 = 1 ∧ f' 3 = acc
        ∧ f' 6 = h ∧ (∀ z, ¬ Scratch z → f' z = f0 z) ∧ (∀ z, f' z < 2 ^ w))
      ∧ exec scanProg ρ (S + 3) 8 0 (memOf w f) = exec scanProg ρ S 13 0 (memOf w f') := by
  have d8 : scanProg.getD 8 Instr.reject = Instr.blt 9 10 11 := rfl
  rw [exec_blt_lt_step (S := S + 3) (hS := by omega) d8 hfit (by rw [h9, h10]; exact hlt)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d11 : scanProg.getD 11 Instr.reject = Instr.sub 11 10 9 := rfl
  rw [exec_sub_step (S := S + 2) (hS := by omega) d11 hfit (by rw [h9, h10]; omega)]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v11 : f 10 - f 9 = f0 (baseA + k) - f0 (baseV + k) := by rw [h9, h10]
  rw [v11]
  set s : Nat → Nat := up f 11 (f0 (baseA + k) - f0 (baseV + k)) with hs
  have hfs : ∀ z, s z < 2 ^ w := upFit hfit (by omega)
  have has : ∀ z, ¬ Scratch z → s z = f0 z := agree_up scratch_eleven hagree
  have d12 : scanProg.getD 12 Instr.reject = Instr.blt 12 1 13 := rfl
  refine ⟨s, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact up_eq f 11 _
  · rw [hs, up_ne (by decide : (0 : Nat) ≠ 11)]; exact h0
  · rw [hs, up_ne (by decide : (1 : Nat) ≠ 11)]; exact h1
  · rw [hs, up_ne (by decide : (3 : Nat) ≠ 11)]; exact h3
  · rw [hs, up_ne (by decide : (6 : Nat) ≠ 11)]; exact h6
  · exact has
  · exact hfs
  · rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d12 hfs]
    · rw [show S + 1 - 1 = S + 0 from rfl]
      simp
    · have e12 : s 12 = f 12 := by rw [hs, up_ne (by decide : (12 : Nat) ≠ 11)]
      have e1 : s 1 = f 1 := by rw [hs, up_ne (by decide : (1 : Nat) ≠ 11)]
      rw [e12, e1, h12, h1]
      omega

/-- **The fall-through branch** (`a ≤ v`): `pc 8 → pc 13` in 3 steps, `d := v − a`. -/
theorem scan_branch_ge {f : Nat → Nat} {k acc : Nat}
    (h0 : f 0 = k) (h1 : f 1 = 1) (h3 : f 3 = acc) (h6 : f 6 = h) (h12 : f 12 = 0)
    (h9 : f 9 = f0 (baseV + k)) (h10 : f 10 = f0 (baseA + k))
    (hge : ¬ f0 (baseV + k) < f0 (baseA + k))
    (hagree : ∀ z, ¬ Scratch z → f z = f0 z) (hfit : ∀ z, f z < 2 ^ w)
    (hpa : f0 (baseA + k) < 2 ^ w) (hpv : f0 (baseV + k) < 2 ^ w) (S : Nat) :
    ∃ f', (f' 11 = f0 (baseV + k) - f0 (baseA + k) ∧ f' 0 = k ∧ f' 1 = 1 ∧ f' 3 = acc
        ∧ f' 6 = h ∧ (∀ z, ¬ Scratch z → f' z = f0 z) ∧ (∀ z, f' z < 2 ^ w))
      ∧ exec scanProg ρ (S + 3) 8 0 (memOf w f) = exec scanProg ρ S 13 0 (memOf w f') := by
  have d8 : scanProg.getD 8 Instr.reject = Instr.blt 9 10 11 := rfl
  rw [exec_blt_ge_step (S := S + 3) (hS := by omega) d8 hfit (by rw [h9, h10]; exact hge)]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have d9 : scanProg.getD 9 Instr.reject = Instr.sub 11 9 10 := rfl
  rw [exec_sub_step (S := S + 2) (hS := by omega) d9 hfit (by rw [h9, h10]; omega)]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v11 : f 9 - f 10 = f0 (baseV + k) - f0 (baseA + k) := by rw [h9, h10]
  rw [v11]
  set s : Nat → Nat := up f 11 (f0 (baseV + k) - f0 (baseA + k)) with hs
  have hfs : ∀ z, s z < 2 ^ w := upFit hfit (by omega)
  have has : ∀ z, ¬ Scratch z → s z = f0 z := agree_up scratch_eleven hagree
  have d10 : scanProg.getD 10 Instr.reject = Instr.blt 12 1 13 := rfl
  refine ⟨s, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact up_eq f 11 _
  · rw [hs, up_ne (by decide : (0 : Nat) ≠ 11)]; exact h0
  · rw [hs, up_ne (by decide : (1 : Nat) ≠ 11)]; exact h1
  · rw [hs, up_ne (by decide : (3 : Nat) ≠ 11)]; exact h3
  · rw [hs, up_ne (by decide : (6 : Nat) ≠ 11)]; exact h6
  · exact has
  · exact hfs
  · rw [exec_blt_lt_step (S := S + 1) (hS := by omega) d10 hfs]
    · rw [show S + 1 - 1 = S + 0 from rfl]
      simp
    · have e12 : s 12 = f 12 := by rw [hs, up_ne (by decide : (12 : Nat) ≠ 11)]
      have e1 : s 1 = f 1 := by rw [hs, up_ne (by decide : (1 : Nat) ≠ 11)]
      rw [e12, e1, h12, h1]
      omega

end Scan

/-- **The suffix, walked** (`pc 13 → pc 17`, 4 steps): the branchless hit
comparison and the accumulator.  `hitWord`'s definition is exactly the value
`(d/h)/(d/h)` produces here — that is why the branch at `pc 8` needed no sign
test. -/
theorem scan_suffix {f : Nat → Nat} {k acc : Nat}
    (h0 : f 0 = k) (h1 : f 1 = 1) (h3 : f 3 = acc) (h6 : f 6 = h)
    (h11 : f 11 = wordDiff (f0 (baseV + k)) (f0 (baseA + k)))
    (hacc : acc ≤ k) (hk : k < N) (hN : N < 2 ^ w) (hh1 : 1 ≤ h)
    (hpa : f0 (baseA + k) < 2 ^ w) (hpv : f0 (baseV + k) < 2 ^ w)
    (hagree : ∀ z, ¬ Scratch z → f z = f0 z) (hfit : ∀ z, f z < 2 ^ w) (S : Nat) :
    ∃ f', LoopInv w f0 f' (k + 1) (acc + hitWord h (f0 (baseV + k)) (f0 (baseA + k)))
      ∧ exec scanProg ρ (S + 4) 13 0 (memOf w f) = exec scanProg ρ S 17 0 (memOf w f') := by
  have d13 : scanProg.getD 13 Instr.reject = Instr.div 13 11 6 := rfl
  rw [exec_div_step (S := S + 4) (hS := by omega) d13 hfit]
  rw [show S + 4 - 1 = S + 3 from rfl]
  have v13 : f 11 / f 6 = wordDiff (f0 (baseV + k)) (f0 (baseA + k)) / h := by rw [h11, h6]
  rw [v13]
  set s1 : Nat → Nat := up f 13 (wordDiff (f0 (baseV + k)) (f0 (baseA + k)) / h) with hs1
  have hdv : wordDiff (f0 (baseV + k)) (f0 (baseA + k)) < 2 ^ w := by
    unfold wordDiff
    split <;> omega
  have h1w : (1 : Nat) < 2 ^ w := by omega
  have hfw : hitWord h (f0 (baseV + k)) (f0 (baseA + k)) < 2 ^ w := by
    have hle := hitWord_le_one h (f0 (baseV + k)) (f0 (baseA + k))
    omega
  have hdiv : wordDiff (f0 (baseV + k)) (f0 (baseA + k)) / h
      ≤ wordDiff (f0 (baseV + k)) (f0 (baseA + k)) := Nat.div_le_self _ _
  have hf1 : ∀ z, s1 z < 2 ^ w := upFit hfit (by omega)
  have ha1 : ∀ z, ¬ Scratch z → s1 z = f0 z := agree_up scratch_thirteen hagree
  have d14 : scanProg.getD 14 Instr.reject = Instr.div 13 13 13 := rfl
  rw [exec_div_step (S := S + 3) (hS := by omega) d14 hf1]
  rw [show S + 3 - 1 = S + 2 from rfl]
  have e13 : s1 13 = wordDiff (f0 (baseV + k)) (f0 (baseA + k)) / h := up_eq f 13 _
  have v14 : s1 13 / s1 13 = hitWord h (f0 (baseV + k)) (f0 (baseA + k)) := by
    rw [e13]
    rfl
  rw [v14]
  set s2 : Nat → Nat := up s1 13 (hitWord h (f0 (baseV + k)) (f0 (baseA + k))) with hs2
  have hf2 : ∀ z, s2 z < 2 ^ w := upFit hf1 hfw
  have ha2 : ∀ z, ¬ Scratch z → s2 z = f0 z := agree_up scratch_thirteen ha1
  have e3 : s2 3 = acc := by
    rw [hs2, up_ne (by decide : (3 : Nat) ≠ 13), hs1, up_ne (by decide : (3 : Nat) ≠ 13)]
    exact h3
  have e13' : s2 13 = hitWord h (f0 (baseV + k)) (f0 (baseA + k)) := up_eq s1 13 _
  have d15 : scanProg.getD 15 Instr.reject = Instr.add 3 3 13 := rfl
  rw [exec_add_step (S := S + 2) (hS := by omega) d15]
  rw [show S + 2 - 1 = S + 1 from rfl]
  have v15 : s2 3 + s2 13 = acc + hitWord h (f0 (baseV + k)) (f0 (baseA + k)) := by
    rw [e3, e13']
  rw [v15]
  set s3 : Nat → Nat := up s2 3 (acc + hitWord h (f0 (baseV + k)) (f0 (baseA + k))) with hs3
  have hacc' : acc + hitWord h (f0 (baseV + k)) (f0 (baseA + k)) ≤ k + 1 := by
    have := hitWord_le_one h (f0 (baseV + k)) (f0 (baseA + k))
    omega
  have hf3 : ∀ z, s3 z < 2 ^ w := upFit hf2 (by omega)
  have ha3 : ∀ z, ¬ Scratch z → s3 z = f0 z := agree_up scratch_three ha2
  have e0 : s3 0 = k := by
    rw [hs3, up_ne (by decide : (0 : Nat) ≠ 3), hs2, up_ne (by decide : (0 : Nat) ≠ 13),
      hs1, up_ne (by decide : (0 : Nat) ≠ 13)]
    exact h0
  have e1 : s3 1 = 1 := by
    rw [hs3, up_ne (by decide : (1 : Nat) ≠ 3), hs2, up_ne (by decide : (1 : Nat) ≠ 13),
      hs1, up_ne (by decide : (1 : Nat) ≠ 13)]
    exact h1
  have d16 : scanProg.getD 16 Instr.reject = Instr.add 0 0 1 := rfl
  rw [exec_add_step (S := S + 1) (hS := by omega) d16]
  rw [show S + 1 - 1 = S + 0 from rfl]
  have v16 : s3 0 + s3 1 = k + 1 := by rw [e0, e1]
  rw [v16]
  refine ⟨up s3 0 (k + 1), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact up_eq s3 0 _
  · rw [up_ne (by decide : (3 : Nat) ≠ 0)]
    exact up_eq s2 3 _
  · have hb := hitWord_le_one h (f0 (baseV + k)) (f0 (baseA + k))
    omega
  · intro z hz
    exact agree_up scratch_zero ha3 z hz
  · exact upFit hf3 (by omega)
  · simp

/-- **One full iteration** (`pc 4 → pc 17`, 11 steps): head, branch, suffix. -/
theorem scan_body {f : Nat → Nat} {k acc : Nat}
    (hL : Layout f0 N h baseA baseV) (hinv : LoopInv w f0 f k acc)
    (hk : k < N) (hN : N < 2 ^ w) (hh1 : 1 ≤ h) (hhlt : h < 2 ^ w)
    (hbA : baseA + N < 2 ^ w) (hbV : baseV + N < 2 ^ w) (hbA14 : 14 ≤ baseA)
    (hbV14 : 14 ≤ baseV) (S : Nat) :
    ∃ f', LoopInv w f0 f' (k + 1) (acc + hitWord h (f0 (baseV + k)) (f0 (baseA + k)))
      ∧ exec scanProg ρ (S + 11) 4 0 (memOf w f) = exec scanProg ρ S 17 0 (memOf w f') := by
  obtain ⟨h0, h3, hacc, hagree, hfit⟩ := hinv
  obtain ⟨f1, hHead, hstep1⟩ :=
    scan_head (f0 := f0) (f := f) (k := k) (acc := acc) hL ⟨h0, h3, hacc, hagree, hfit⟩ hk hN hbA hbV
      (S := S + 7)
  obtain ⟨h10, h20, h40, h50, h60, h120, h11, h90, h100, hag, hfi, h13⟩ := hHead
  have hpa : f0 (baseA + k) < 2 ^ w := by
    rw [← hag (baseA + k) (scratch_payload hbA14)]
    exact hfi (baseA + k)
  have hpv : f0 (baseV + k) < 2 ^ w := by
    rw [← hag (baseV + k) (scratch_payload hbV14)]
    exact hfi (baseV + k)
  by_cases hlt : f0 (baseV + k) < f0 (baseA + k)
  · obtain ⟨f2, ⟨hd, h02, h12, h32, h62, hag2, hfi2⟩, hstep2⟩ :=
      scan_branch_lt (f0 := f0) (f := f1) (k := k) (acc := acc) h10 h11 h13 h60 h120 h90 h100
        hlt hag hfi hpa hpv (S := S + 4)
    have hd' : f2 11 = wordDiff (f0 (baseV + k)) (f0 (baseA + k)) := by
      rw [hd, wordDiff_of_lt hlt]
    obtain ⟨f', hinv', hstep3⟩ :=
      scan_suffix (f0 := f0) (f := f2) (k := k) (acc := acc) h02 h12 h32 h62 hd' hacc hk hN hh1
        hpa hpv hag2 hfi2 (S := S)
    exact ⟨f', hinv', by
      rw [show S + 11 = S + 7 + 4 from by omega, hstep1,
        show S + 7 = S + 4 + 3 from by omega, hstep2, hstep3]⟩
  · obtain ⟨f2, ⟨hd, h02, h12, h32, h62, hag2, hfi2⟩, hstep2⟩ :=
      scan_branch_ge (f0 := f0) (f := f1) (k := k) (acc := acc) h10 h11 h13 h60 h120 h90 h100
        hlt hag hfi hpa hpv (S := S + 4)
    have hd' : f2 11 = wordDiff (f0 (baseV + k)) (f0 (baseA + k)) := by
      rw [hd, wordDiff_of_ge hlt]
    obtain ⟨f', hinv', hstep3⟩ :=
      scan_suffix (f0 := f0) (f := f2) (k := k) (acc := acc) h02 h12 h32 h62 hd' hacc hk hN hh1
        hpa hpv hag2 hfi2 (S := S)
    exact ⟨f', hinv', by
      rw [show S + 11 = S + 7 + 4 from by omega, hstep1,
        show S + 7 = S + 4 + 3 from by omega, hstep2, hstep3]⟩

/-! ### §L6 — the loop: `m` iterations, then the exit

`scan_body` is one iteration.  The loop rule is a `Nat` induction on the number of
*remaining* iterations: each taken jump consumes exactly 12 steps (11 of body, 1
of `blt`), and the last iteration's `blt` falls through to `pc 18` instead of
jumping — so the fuel is `12·m` and the exit is a single `pc`. -/

theorem wordList_one (f : Nat → Nat) (b : Nat) : wordList f b 1 = [f b] := by
  rw [show (1 : Nat) = 0 + 1 from rfl, wordList_succ, wordList_zero]

theorem scan_loop (hL : Layout f0 N h baseA baseV) (hN : N < 2 ^ w) (hh1 : 1 ≤ h)
    (hhlt : h < 2 ^ w) (hbA : baseA + N < 2 ^ w) (hbV : baseV + N < 2 ^ w)
    (hbA14 : 14 ≤ baseA) (hbV14 : 14 ≤ baseV) :
    ∀ (m : Nat) (f : Nat → Nat) (acc S : Nat), 1 ≤ m → m ≤ N →
      LoopInv w f0 f (N - m) acc →
      ∃ f', LoopInv w f0 f' N
          (acc + hitCount h (wordList f0 (baseV + (N - m)) m)
            (wordList f0 (baseA + (N - m)) m))
        ∧ exec scanProg ρ (12 * m + S) 4 0 (memOf w f) = exec scanProg ρ S 18 0 (memOf w f') := by
  intro m
  induction m with
  | zero => intro _ _ _ hm; exact absurd hm (by omega)
  | succ m ih =>
    intro f acc S hm hmN hinv
    have d17 : scanProg.getD 17 Instr.reject = Instr.blt 0 2 4 := rfl
    rcases Nat.eq_or_lt_of_le hm with h1 | hm2
    · have hm0 : m = 0 := by omega
      subst hm0
      obtain ⟨f1, hinv1, hstep1⟩ :=
        scan_body (f0 := f0) (f := f) (N := N) (h := h) (baseA := baseA) (baseV := baseV)
          (k := N - 1) (acc := acc) hL hinv (by omega) hN hh1 hhlt hbA hbV hbA14 hbV14
          (S := S + 1)
      have e2 : f1 2 = N := by
        rw [hinv1.2.2.2.1 2 scratch_const_two]
        exact hL.2.1
      have hn1 : (N - 1) + 1 = N := by omega
      have hlast : exec scanProg ρ (S + 1) 17 0 (memOf w f1) = exec scanProg ρ S 18 0 (memOf w f1) := by
        rw [exec_blt_ge_step (S := S + 1) (hS := by omega) d17 hinv1.2.2.2.2
          (by rw [hinv1.1, e2]; omega)]
        rw [show S + 1 - 1 = S + 0 from rfl]
        simp
      have hacc : acc + hitWord h (f0 (baseV + (N - 1))) (f0 (baseA + (N - 1)))
          = acc + hitCount h (wordList f0 (baseV + (N - 1)) 1)
              (wordList f0 (baseA + (N - 1)) 1) := by
        rw [wordList_one, wordList_one, hitCount_succ, hitCount, Nat.add_zero]
      have hcnt : acc + hitWord h (f0 (baseV + (N - 1))) (f0 (baseA + (N - 1))) ≤ N := by
        have h2 := hinv1.2.2.1
        rw [hn1] at h2
        exact h2
      rw [← hacc]
      refine ⟨f1, ⟨?_, ?_, hcnt, ?_, ?_⟩, ?_⟩
      · rw [hinv1.1]; exact hn1
      · exact hinv1.2.1
      · exact hinv1.2.2.2.1
      · exact hinv1.2.2.2.2
      · rw [show 12 * 1 + S = (S + 1) + 11 from by omega, hstep1, hlast]
    · have hle : m ≤ N := by omega
      have hk : N - (m + 1) < N := by omega
      obtain ⟨f1, hinv1, hstep1⟩ :=
        scan_body (f0 := f0) (f := f) (N := N) (h := h) (baseA := baseA) (baseV := baseV)
          (k := N - (m + 1)) (acc := acc) hL hinv hk hN hh1 hhlt hbA hbV hbA14 hbV14
          (S := (12 * m + S) + 1)
      have e2 : f1 2 = N := by
        rw [hinv1.2.2.2.1 2 scratch_const_two]
        exact hL.2.1
      have hjump : exec scanProg ρ ((12 * m + S) + 1) 17 0 (memOf w f1)
          = exec scanProg ρ (12 * m + S) 4 0 (memOf w f1) := by
        rw [exec_blt_lt_step (S := (12 * m + S) + 1) (hS := by omega) d17 hinv1.2.2.2.2
          (by rw [hinv1.1, e2]; omega)]
        rw [show (12 * m + S) + 1 - 1 = 12 * m + S + 0 from rfl]
        simp
      have hinv1' : LoopInv w f0 f1 (N - m)
          (acc + hitWord h (f0 (baseV + (N - (m + 1)))) (f0 (baseA + (N - (m + 1))))) := by
        rw [show (N - (m + 1)) + 1 = N - m from by omega] at hinv1
        exact hinv1
      obtain ⟨f2, hinv2, hstep2⟩ :=
        ih f1 (acc + hitWord h (f0 (baseV + (N - (m + 1)))) (f0 (baseA + (N - (m + 1)))))
          S (by omega) hle hinv1'
      refine ⟨f2, ?_, ?_⟩
      · -- the accumulator over `m+1` pairs is the head pair plus the rest
        have hacc : acc + hitCount h (wordList f0 (baseV + (N - (m + 1))) (m + 1))
              (wordList f0 (baseA + (N - (m + 1))) (m + 1))
            = (acc + hitWord h (f0 (baseV + (N - (m + 1)))) (f0 (baseA + (N - (m + 1)))))
              + hitCount h (wordList f0 (baseV + (N - m)) m)
                  (wordList f0 (baseA + (N - m)) m) := by
          rw [show wordList f0 (baseV + (N - (m + 1))) (m + 1)
                = f0 (baseV + (N - (m + 1)))
                  :: wordList f0 (baseV + (N - (m + 1)) + 1) m from wordList_succ _ _ _,
              show wordList f0 (baseA + (N - (m + 1))) (m + 1)
                = f0 (baseA + (N - (m + 1)))
                  :: wordList f0 (baseA + (N - (m + 1)) + 1) m from wordList_succ _ _ _,
              hitCount_succ]
          rw [show baseV + (N - (m + 1)) + 1 = baseV + (N - m) from by omega,
              show baseA + (N - (m + 1)) + 1 = baseA + (N - m) from by omega,
              ← Nat.add_assoc]
        rw [hacc]
        exact hinv2
      · rw [show 12 * (m + 1) + S = ((12 * m + S) + 1) + 11 from by omega,
          hstep1, hjump, hstep2]

/-! ### §L7 — the run, and §7 step 7's test at the exit -/

/-- The exit: `pc 18` tests `0 < acc` and accepts or rejects — two steps. -/
theorem scan_epilogue {f : Nat → Nat} (hfit : ∀ z, f z < 2 ^ w) (h12 : f 12 = 0) (S : Nat) :
    exec scanProg ρ (S + 2) 18 0 (memOf w f) = some (decide (0 < f 3)) := by
  have d18 : scanProg.getD 18 Instr.reject = Instr.blt 12 3 20 := rfl
  by_cases hlt : f 12 < f 3
  · rw [exec_blt_lt_step (S := S + 2) (hS := by omega) d18 hfit hlt]
    rw [show S + 2 - 1 = S + 1 from rfl]
    have d20 : scanProg.getD 20 Instr.reject = Instr.accept := rfl
    rw [exec_accept_step (S := S + 1) (hS := by omega) d20]
    rw [decide_eq_true (by rw [h12] at hlt; omega)]
  · rw [exec_blt_ge_step (S := S + 2) (hS := by omega) d18 hfit hlt]
    rw [show S + 2 - 1 = S + 1 from rfl]
    have d19 : scanProg.getD 19 Instr.reject = Instr.reject := rfl
    rw [exec_reject_step (S := S + 1) (hS := by omega) d19]
    rw [decide_eq_false (by rw [h12] at hlt; omega)]

/-! ### §L8 — the prologue, the run assembly, and the verdict at the exit

`scan_loop` begins at the loop head with `LoopInv` already in hand; a run begins at
`pc 0` with nothing but `memOf w f0`.  Three lemmas close that gap.
`scan_prologue` walks the four prologue instructions (`[1] := 1`, `[12] := 0`,
`acc := 0`, `k := 0`) to establish the invariant at `k = 0`, `acc = 0`; `scan_run`
composes it with `scan_loop` at `m = N` and `scan_epilogue` into one statement at the
fuel `4 + 12·N + 2 = 12·N + 6`; and `scan_run_eq_rowTest` rewrites that exit's
`decide (0 < hitCount …)` into `Routines.rowTest` on the two payload blocks, which is
§7 step 7's verdict on the memory the loop read.

**The `1 ≤ w` hypothesis, and why it is not really a hypothesis.**  The prologue's
first instruction writes the literal `1`, so re-establishing the fit invariant needs
`1 < 2^w` — that is the whole of the missing ingredient (the loop body only ever
writes `0`, sums and quotients of fitting words, so nothing in `scan_loop` needed it).
The theorem below therefore carries `hw : 1 ≤ w` **as the arithmetic hypothesis its
statement contemplates**, and `wordLength_ge_one` shows it is *free* at the lane's own
word length: `wordLength`'s last summand is `+ 1`, so `1 ≤ wordLength n b` holds for
every `n`, `b` — no `1 ≤ b` side condition, unlike `wordLength_ge_five`, which is used
where a *five*-bit word is required.  `one_lt_two_pow` is the step from the hypothesis
to the literal.

**`1 ≤ N` is genuinely needed, and it is a fact about the program.**  `scanProg` is a
do-while: the jump at `pc 17` is at the *bottom*, so the body at `pc 4` runs at least
once and `k = 0` always reads the block's first word.  `scan_loop` records exactly
this (`1 ≤ m`), so `scan_run` carries `hN1 : 1 ≤ N` rather than pretending that an
empty block has a run. -/

/-- `1 < 2^w` from `1 ≤ w` — the prologue's `[1] := 1` needs the word to have at
least one bit. -/
theorem one_lt_two_pow {w : Nat} (hw : 1 ≤ w) : 1 < 2 ^ w := by
  have hp : (2 : Nat) ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  rw [show (2 : Nat) ^ 1 = 2 from rfl] at hp
  omega

/-- **`1 ≤ w` is free at the lane's word length.**  `wordLength`'s last summand is
`+ 1`, so this needs no hypothesis on `n` or `b` — unlike `wordLength_ge_five`, which
needs `1 ≤ b`. -/
theorem wordLength_ge_one (n b : Nat) : 1 ≤ wordLength n b := by
  unfold wordLength
  omega

/-- The payload base is past the scratch window (`Layout`'s seventh field, as an
accessor so call sites need not spell out the conjunction). -/
theorem Layout.baseA_ge {f0 : Nat → Nat} {N h baseA baseV : Nat}
    (hL : Layout f0 N h baseA baseV) : 14 ≤ baseA := hL.2.2.2.2.2.2.1

/-- The second payload base is past the scratch window. -/
theorem Layout.baseV_ge {f0 : Nat → Nat} {N h baseA baseV : Nat}
    (hL : Layout f0 N h baseA baseV) : 14 ≤ baseV := hL.2.2.2.2.2.2.2

/-- **The prologue, walked** (`pc 0 → pc 4`, 4 steps): `[1] := 1`, `[12] := 0`,
`acc := 0`, `k := 0`, leaving the loop invariant at `k = acc = 0`.  Agreement with the
entry memory survives because cell `1` is written with the value it already holds
(`Layout` fixes `f0 1 = 1`) and cell `12` with `0` (`Layout` fixes `f0 12 = 0`); the
other two writes land on scratch cells. -/
theorem scan_prologue {f0 : Nat → Nat} {N h baseA baseV : Nat}
    (hL : Layout f0 N h baseA baseV) (hw : 1 ≤ w) (hfit0 : ∀ z, f0 z < 2 ^ w) (S : Nat) :
    ∃ f', LoopInv w f0 f' 0 0
      ∧ exec scanProg ρ (S + 4) 0 0 (memOf w f0) = exec scanProg ρ S 4 0 (memOf w f') := by
  have hone : 1 < 2 ^ w := one_lt_two_pow hw
  have hzero : 0 < 2 ^ w := twoPowPos w
  have d0 : scanProg.getD 0 Instr.reject = Instr.one 1 := rfl
  rw [exec_one_step (S := S + 4) (hS := by omega) d0]
  rw [show S + 4 - 1 = S + 3 from rfl]
  set s1 : Nat → Nat := up f0 1 1 with hs1
  have hfit1 : ∀ z, s1 z < 2 ^ w := upFit hfit0 hone
  have hs1eq : ∀ z, s1 z = f0 z := by
    intro z
    rw [hs1]
    rw [up]
    by_cases hz : z = 1
    · rw [if_pos hz, hz]; exact hL.1.symm
    · rw [if_neg hz]
  have d1 : scanProg.getD 1 Instr.reject = Instr.sub 12 1 1 := rfl
  rw [exec_sub_step (S := S + 3) (hS := by omega) d1 hfit1 (le_refl (s1 1))]
  rw [show S + 3 - 1 = S + 2 from rfl, Nat.sub_self]
  set s2 : Nat → Nat := up s1 12 0 with hs2
  have hfit2 : ∀ z, s2 z < 2 ^ w := upFit hfit1 hzero
  have d2 : scanProg.getD 2 Instr.reject = Instr.sub 3 1 1 := rfl
  rw [exec_sub_step (S := S + 2) (hS := by omega) d2 hfit2 (le_refl (s2 1))]
  rw [show S + 2 - 1 = S + 1 from rfl, Nat.sub_self]
  set s3 : Nat → Nat := up s2 3 0 with hs3
  have hfit3 : ∀ z, s3 z < 2 ^ w := upFit hfit2 hzero
  have d3 : scanProg.getD 3 Instr.reject = Instr.sub 0 1 1 := rfl
  rw [exec_sub_step (S := S + 1) (hS := by omega) d3 hfit3 (le_refl (s3 1))]
  rw [show S + 1 - 1 = S + 0 from rfl, Nat.sub_self]
  set s4 : Nat → Nat := up s3 0 0 with hs4
  have hfit4 : ∀ z, s4 z < 2 ^ w := upFit hfit3 hzero
  refine ⟨s4, ⟨?_, ?_, by omega, ?_, hfit4⟩, ?_⟩
  · rw [hs4, up]; simp
  · rw [hs4, up, if_neg (by omega), hs3, up, if_pos rfl]
  · intro z hz
    have hz0 : z ≠ 0 := fun hh => hz (hh ▸ scratch_zero)
    have hz3 : z ≠ 3 := fun hh => hz (hh ▸ scratch_three)
    rw [hs4, up, if_neg hz0, hs3, up, if_neg hz3, hs2, up]
    by_cases h12 : z = 12
    · rw [if_pos h12, h12]; exact hL.2.2.2.2.2.1.symm
    · rw [if_neg h12]; exact hs1eq z
  · rfl

/-- **The run**: the whole program from `pc 0` on the entry memory, in `12·N + 6`
instructions — the prologue (4), one iteration per pair (12 each, as `scan_body`
fixes them) and the exit (2).  The accumulator it halts with is `hitCount` over the
whole block, so the verdict is `decide (0 < hitCount …)`. -/
theorem scan_run {f0 : Nat → Nat} {N h baseA baseV : Nat}
    (hL : Layout f0 N h baseA baseV) (hw : 1 ≤ w) (hfit0 : ∀ z, f0 z < 2 ^ w)
    (hN : N < 2 ^ w) (hh1 : 1 ≤ h) (hhlt : h < 2 ^ w)
    (hbA : baseA + N < 2 ^ w) (hbV : baseV + N < 2 ^ w) (hN1 : 1 ≤ N) :
    exec scanProg ρ (12 * N + 6) 0 0 (memOf w f0)
      = some (decide (0 < hitCount h (wordList f0 baseV N) (wordList f0 baseA N))) := by
  obtain ⟨fp, hinvp, hpro⟩ := scan_prologue (f0 := f0) hL hw hfit0 (S := 12 * N + 2)
  have hinvp' : LoopInv w f0 fp (N - N) 0 := by rw [Nat.sub_self]; exact hinvp
  obtain ⟨f', hinv', hloop⟩ :=
    scan_loop (f0 := f0) (N := N) (h := h) (baseA := baseA) (baseV := baseV)
      hL hN hh1 hhlt hbA hbV (Layout.baseA_ge hL) (Layout.baseV_ge hL)
      N fp 0 2 hN1 (le_refl N) hinvp'
  have h12 : f' 12 = 0 := by
    rw [hinv'.2.2.2.1 12 scratch_const_twelve]
    exact hL.2.2.2.2.2.1
  have hepi : exec scanProg ρ (0 + 2) 18 0 (memOf w f') = some (decide (0 < f' 3)) :=
    scan_epilogue hinv'.2.2.2.2 h12 0
  rw [show (0 : Nat) + 2 = 2 from rfl] at hepi
  rw [show 12 * N + 6 = (12 * N + 2) + 4 from by omega, hpro, hloop, hepi, hinv'.2.1]
  simp only [Nat.zero_add, Nat.sub_self, Nat.add_zero]

/-- **§7 step 7's verdict at the exit**: `Routines.rowTest` on the two payload blocks
the loop actually read.  This is the composition the residual named, made mechanical —
`hitCount_pos_iff` (a positive count *is* a hit), `anyHit_eq_rowTest` (a hit is the
paper's `|V̂ − Â| ≥ 1/2`, at the layout's `h = 2^{fracBits−1}` by
`hitWord_eq_ratTest`), and `payloadBlock_memOf` (the memory's words are
`payloadBlock`'s `ℚ` estimates when every word fits). -/
theorem scan_run_eq_rowTest {f0 : Nat → Nat} {N baseA baseV fracBits : Nat}
    (hL : Layout f0 N (2 ^ (fracBits - 1)) baseA baseV) (hfrac : 1 ≤ fracBits)
    (hw : 1 ≤ w) (hfit0 : ∀ z, f0 z < 2 ^ w) (hN : N < 2 ^ w)
    (hHlt : 2 ^ (fracBits - 1) < 2 ^ w)
    (hbA : baseA + N < 2 ^ w) (hbV : baseV + N < 2 ^ w) (hN1 : 1 ≤ N) :
    exec scanProg ρ (12 * N + 6) 0 0 (memOf w f0)
      = some (Routines.rowTest (payloadBlock fracBits baseA N (memOf w f0))
          (payloadBlock fracBits baseV N (memOf w f0))) := by
  rw [scan_run (h := 2 ^ (fracBits - 1)) hL hw hfit0 hN Nat.one_le_two_pow hHlt hbA hbV hN1]
  have hb : ∀ v a, hitWord (2 ^ (fracBits - 1)) v a = 1
      ↔ (1 / 2 : ℚ) ≤
        |(v : ℚ) / (2 : ℚ) ^ fracBits - (a : ℚ) / (2 : ℚ) ^ fracBits| :=
    fun v a => hitWord_eq_ratTest hfrac v a
  have hstep : (decide (0 < hitCount (2 ^ (fracBits - 1)) (wordList f0 baseV N)
        (wordList f0 baseA N)) : Bool)
      = Routines.rowTest ((wordList f0 baseA N).map (toQ fracBits))
          ((wordList f0 baseV N).map (toQ fracBits)) := by
    by_cases hpos : 0 < hitCount (2 ^ (fracBits - 1)) (wordList f0 baseV N)
      (wordList f0 baseA N)
    · rw [decide_eq_true hpos,
        ← anyHit_eq_rowTest hb (wordList f0 baseV N) (wordList f0 baseA N),
        (hitCount_pos_iff (2 ^ (fracBits - 1)) (wordList f0 baseV N)
          (wordList f0 baseA N)).mp hpos]
    · have hne : anyHit (2 ^ (fracBits - 1)) (wordList f0 baseV N)
          (wordList f0 baseA N) ≠ true :=
        fun hc => hpos ((hitCount_pos_iff (2 ^ (fracBits - 1)) (wordList f0 baseV N)
          (wordList f0 baseA N)).mpr hc)
      have hfalse : anyHit (2 ^ (fracBits - 1)) (wordList f0 baseV N)
          (wordList f0 baseA N) = false := by
        cases hany : anyHit (2 ^ (fracBits - 1)) (wordList f0 baseV N)
            (wordList f0 baseA N) with
        | false => rfl
        | true => exact absurd hany hne
      rw [decide_eq_false hpos,
        ← anyHit_eq_rowTest hb (wordList f0 baseV N) (wordList f0 baseA N), hfalse]
  rw [hstep, ← payloadBlock_memOf (f := f0) hfit0 fracBits baseA N,
    ← payloadBlock_memOf (f := f0) hfit0 fracBits baseV N]

/-! ### The cost pair's absorption call site (residual piece 3, still stated)

The exact `Instr`-step count is now a theorem rather than a hope: `scan_run`'s fuel is
`12·N + 6`, i.e. `12·blockLen + 6` steps in the single-word regime.  The multi-word
charge replaces each per-pair step's cost by a **nested** measure: §6.2's comparison
of two `n²`-bit dyadics is itself a loop of `⌈n²/w⌉ + 1 ≤ wordOpFactor n`
word-visits (`KapilaAlgo.wordOpFactor`, `n² + 1`), so one pair costs
`2·wordOpFactor n + 3` word-ops and the block costs

    scanWordOps n blockLen = blockLen · (2 · wordOpFactor n + 3).

The two lemmas this section will state, in the shape the absorption needs:

    scanWordOps_le      : blockLen · (2 · wordOpFactor n + 3) ≤ (n + b + 2) ^ 7
    scan_cost_absorbed  : (R.cost + scanWordOps : ℕ) ≤ K₀ · 2^E · P^(K + 7)

**The call site is `KapilaAlgo.withinEnvelope_wordop_absorb`, and the exponent it
raises is `K + 3` — the residual asks for `K + 7`.**  That `+3` is exactly
`wordOpFactor n ≤ (n + b + 2) ^ 3` (`wordOpFactor_le_cube`), a *linear* charge.  The
scan's charge carries `wordOpFactor` **squared** (a comparison loop nested inside an
outer loop of `blockLen` iterations), so the same argument runs at a larger
exponent: round (9) accounted the `+7` as *one* unit from the nested `wordOpFactor²`
and *five* from `wordOpFactor ≤ (n+b+2)^3` squared times the constant `5`.  **That
split is that residual's sketch, not a checked derivation** — no arithmetic lemma in
this module backs it, `scanWordOps_le` has not been written, and the `^7` in the
statement above is the residual's target, not a proved bound.  What *is* checked is
only the reason `withinEnvelope_wordop_absorb` cannot be *applied*: it proves the
absorption for `R.cost · wordOpFactor` with `K + 3`, and the scan's charge is a
different function of `wordOpFactor`, so the lemma to write must abstract
`wordOpFactor`'s exponent instead of quoting the `+3`.  That is why this stays a
stated residual rather than a one-line citation — and why, once it is written, it
will not weaken the row's `2^{(τ₀+20ε)n}` exponent: `K` is §7's to choose. -/

end SubsetSumL25.Row
