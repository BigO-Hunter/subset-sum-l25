/-
Row assembly for `ss/kapila 0.4877` — **piece (b): the D7 seam** and
**piece (c): the bound in the challenge's own vocabulary**.

This module is the row's statement-of-record.  It proves
`BigOSpeedrun.SubsetSum.SolvedInTime (4877 / 10000)` — the literal the board
files — from three inputs:

1. `Routines` (`SubsetSumL25.Row.KapilaAlgo`) — §7's procedure, executably;
2. `CorrectAt` — §7's correctness paragraph in the trusted statement's own tape
   vocabulary (its docstring names the measured in-tree cores and what the
   hypothesis adds);
3. `D7` — **the one named seam**: §7's bit-cost → `Instr`-step translation,
   deliberately not imported.

Everything else is proved here: §1's exponent gap and its absorption
(`KapilaAbsorb`), the `BigO` at the row's literal, the tape/`count` transfer,
and the horizon glide `exec` is inert once halted.
-/
import Mathlib
import SubsetSumL25.Row.KapilaAlgo
import SubsetSumL25.Row.KapilaAbsorb

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### Glide: `exec` is inert once halted -/

/-- Fuel monotonicity of the challenge's `exec`: once a run has halted (value
not `none`), extra fuel does not change the value.  `SolvedInTime` fixes a
single horizon `T n` for every random outcome, so halting must be monotone. -/
theorem exec_eq_of_halted {w : ℕ} (P : List Instr) (ρ : ℕ → BitVec w) :
    ∀ (t : ℕ) (pc r : ℕ) (m : ℕ → BitVec w),
      exec P ρ t pc r m ≠ none → ∀ k : ℕ, exec P ρ (t + k) pc r m = exec P ρ t pc r m := by
  intro t
  induction t with
  | zero => intro pc r m h k; exact absurd rfl h
  | succ t ih =>
    intro pc r m h k
    rw [show t + 1 + k = (t + k) + 1 by omega]
    simp only [exec] at h ⊢
    rw [List.getD_eq_getElem?_getD] at h ⊢
    generalize hS : P[pc]?.getD Instr.reject = S at h ⊢
    cases S <;> (first | rfl | (exact ih _ _ _ h k))

/-- **Fuel transport, the direction a refinement proof needs.**  A segment
argument exhibits halting at some explicit step count `t`; the row's obligation
is at the abstract horizon `R.cost n x`.  This carries the first to the second,
so one segment's proof never has to count the whole run at once. -/
theorem exec_mono_halted {w : ℕ} (P : List Instr) (ρ : ℕ → BitVec w)
    (t pc r : ℕ) (m : ℕ → BitVec w) (v : Bool)
    (h : exec P ρ t pc r m = some v) (k : ℕ) :
    exec P ρ (t + k) pc r m = some v := by
  have hne : exec P ρ t pc r m ≠ none := by
    intro hc
    rw [h] at hc
    exact Option.some_ne_none v hc
  rw [exec_eq_of_halted P ρ t pc r m hne k, h]

/-- `count` only sees its predicate pointwise. -/
theorem count_congr {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ s, p s ↔ q s) : ∀ N : ℕ, count p N = count q N
  | 0 => rfl
  | N + 1 => by
    rw [count, count, count_congr h N]
    by_cases hp : p N
    · have hq : q N := (h N).1 hp
      simp only [hp, hq, ite_true]
    · have hq : ¬ q N := fun hq => hp ((h N).2 hq)
      simp only [hp, hq, ite_false]

/-- `count` of a predicate that holds everywhere is the whole count. -/
theorem count_const {p : ℕ → Prop} [DecidablePred p] (h : ∀ s, p s) :
    ∀ N : ℕ, count p N = N
  | 0 => rfl
  | N + 1 => by
    rw [count, count_const h N]
    simp [h N]

/-! ### What the guard has already decided

`D7.agrees_main`'s hypothesis is `R.fallback n x = false`.  Unfolding §7's
routing (`fallback_eq_false_iff`, proved where the routing is defined, in
`SubsetSumL25.Row.KapilaAlgo`) shows this is *exactly* «`n ≥ n_*` and the
bit-guard holds» — so the main obligation's premise **is** the statement that
the fallback shadow is absent.  It cannot be discharged, or weakened, by
proving that absence afresh: that reading of the seam is vacuous, and the
unfolding lemma is the measurement of it.

What guard coverage does buy is the other direction.  `KapilaGuard`'s
`guardOk_eventually` + `fallback_false_eventually` say the shadow is *eventually
absent on the statement's routed class*, so the main branch is the one that runs
there and the exact fallback (with its free correctness,
`correctAt_of_fallback_det`) is confined to `n < N`. -/

/-! ### What the row is allowed to assume

Two hypotheses, both at the same documented boundary, both stated in the
*paper's* vocabulary — never in terms of the program we do not have. -/

/-- §7's correctness paragraph, as the trusted statement counts it: at the
procedure's own horizon `t = R.cost n x`, the right verdict comes from at least
two thirds of the `2^(w·t)` equally likely random prefixes.

Why this is a hypothesis and not a theorem here.  Every *mathematical*
ingredient is measured axiom-clean in-tree: Proposition P
(`prop_p_chebyshev`, B5); Theorem A part 1 (`thmA_part1_fail_le`, consuming
`cor_A6_per_alias` and the cap's Markov tail); Theorem B (B4's
`lem_B2_domination`, `row_errors_le_six_eps`); isolation
(`L2_1_isolation_prob`, 11/12).  What is not in-tree is the composition across
this procedure's sample space — the union of §7's five failure events, and the
identification of the abstract draws with the `Draws` stream.  That
identification is the same exec-refinement boundary as `D7`; stating it
explicitly keeps the row's remaining obligation visible instead of hiding it
inside a proof term. -/
def CorrectAt (R : Routines) (n : ℕ) (x : Instance n) : Prop :=
  let t := R.cost n x
  let N := 2 ^ (wordLength n x.bits * t)
  (x.yes ∧ 2 * N ≤ 3 * count
      (fun s => R.run n x (fun r => ((tape (wordLength n x.bits) s) r).toNat) = true) N) ∨
  (¬ x.yes ∧ 2 * N ≤ 3 * count
      (fun s => R.run n x (fun r => ((tape (wordLength n x.bits) s) r).toNat) = false) N)

/-- **The D7 seam** — the campaign's one named seam, and the only
program-side assumption in the row.

The landed O4/O5/O7/O8 statements count in **Base's own counters** (word
operations / elementary steps); the trusted statement counts in **its** `Instr`
steps at word length `w = wordLength n b`.  Bridging the two is a translation:
a program in the challenge's instruction set, plus the statement that at the
abstract cost horizon its run reproduces the abstract decision on the same
random words.

Note what is *not* here: no correctness claim, no probability, no cost
arithmetic.  Correctness is `CorrectAt`; the cost accounting is
`Routines.WithinEnvelope` + `runtime_absorb`.  The seam is only the program and
the outcome agreement. -/
structure D7 (R : Routines) where
  /-- One finite program for all `n` and `b` — the statement's `P : List Instr`.
  The verified `α = 1/2` package (`subsetsum-v2-snapshot`) is a worked instance
  of this field's shape: one `List Instr`, no advice, no dependence on `c`. -/
  program : List Instr
  /-- **The fallback branch's translation** — the branch the guard routes to,
  and the branch that already has a worked reference.

  `R.fallback n x = true` means the input is below the cutoff or violates
  `10⁶⌈log₂(b+1)⌉ ≤ n`, so §7 step 1 runs §6.3's *exact* meet-in-the-middle:
  `Routines.run` collapses to `Routines.mitm` and `Routines.cost` to
  `Routines.mitmCost`, and this field becomes, verbatim, «`program` computes the
  meet-in-the-middle decision» — which is `subsetsum-v2-snapshot`'s `prog2`
  (`Race.bound : SolvedInTime (1/2)`, verdict `decide (isSum …)` on every tape).
  `fallback_agrees_iff` below records that identification mechanically, and
  `correctAt_of_fallback_det` records that this branch's *correctness* needs no
  union bound. -/
  agrees_fallback : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    R.fallback n x = true →
      run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat))
  /-- **The main branch's translation.**  The same equation, taken on the inputs
  the guard *admits*.  This is the half no in-tree program implements yet; it is
  a separate field — not a conjunct of the old `agrees` — precisely so the two
  halves can be discharged independently, in either order, each against its own
  reference.

  Two things are now *measured* about this half rather than assumed:

  * its hypothesis (`R.fallback n x = false`) unfolds to «`n ≥ n_*` **and** the
    bit-guard holds» (`fallback_eq_false_iff`) — so it is already the statement
    that the fallback shadow is absent, and proving that absence does not
    reduce it;
  * it is *equivalent* to four per-segment leaves with concrete verdicts
    (`agrees_main_iff_leaves`), and those leaves are about a program whose
    segments — `prelim`, `aliasA`, `checksumB` — are still opaque fields of an
    arbitrary `Routines`.  Discharging it therefore begins with giving
    `Routines` those three programs and their agreement hypotheses; see the
    section «The main branch, cut into instruction-segments» in
    `SubsetSumL25.Row.KapilaRow`. -/
  agrees_main : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    R.fallback n x = false →
      run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat))

/-- **The seam, reassembled from its two branches.**  The guard is a `Bool`
decided by `n` and `x` alone, so `cases` on it is exhaustive and the two fields
above *are* the whole obligation.  Consumers (and `kapila_row`) keep seeing the
single equation they always saw. -/
theorem D7.agrees {R : Routines} (D : D7 R) :
    ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
      run D.program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat)) := by
  intro n x ρ
  cases h : R.fallback n x
  · exact D.agrees_main n x ρ h
  · exact D.agrees_fallback n x ρ h

/-- Assemble the seam from a program and its two branch obligations. -/
def D7.ofBranches {R : Routines} (program : List Instr)
    (hfb : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
      R.fallback n x = true →
        run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat)))
    (hm : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
      R.fallback n x = false →
        run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat))) :
    D7 R := ⟨program, hfb, hm⟩

/-- **The fallback branch, unfolded: it is §6.3's exact MITM and nothing else.**

On that branch the procedure's own definitions collapse (`Routines.run` to
`Routines.mitm`, `Routines.cost` to `Routines.mitmCost`), so the branch's
translation obligation is *the same proposition* as «`program` computes the
meet-in-the-middle decision at the meet-in-the-middle cost».  Stating it this way
is what makes the branch portable: the worked reference (`subsetsum-v2-snapshot`)
proves a statement of exactly this shape, over exactly this `Instr` set, and
needs no §7 arithmetic at all. -/
theorem fallback_agrees_iff (R : Routines) (program : List Instr) :
    (∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
        R.fallback n x = true →
          run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat)))
      ↔ (∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
        R.fallback n x = true →
          run program x ρ (R.mitmCost n x) = some (R.mitm n x)) := by
  have hrun : ∀ (n : ℕ) (x : Instance n) (ω : Draws), R.fallback n x = true →
      R.run n x ω = R.mitm n x := by
    intro n x ω hf
    simp [Routines.run, hf]
  have hcost : ∀ (n : ℕ) (x : Instance n), R.fallback n x = true →
      R.cost n x = R.mitmCost n x := by
    intro n x hf
    simp [Routines.cost, hf]
  constructor
  · intro H n x ρ hf
    rw [← hcost n x hf, ← hrun n x (fun r => (ρ r).toNat) hf]
    exact H n x ρ hf
  · intro H n x ρ hf
    rw [hcost n x hf, hrun n x (fun r => (ρ r).toNat) hf]
    exact H n x ρ hf

/-- **The guard's coverage, correctness half.**  On an input the guard routes to
the exact fallback, §7's `CorrectAt` needs no union bound at all.

The fallback is §6.3's exact meet-in-the-middle — deterministic — so if it
decides `x.yes` correctly then *every* tape agrees, `count` is the whole tape
space, and the two-thirds majority is vacuous.  The five failure events of §7's
union bound, the `2/3`, and the abstract-draw / sample-space identification
therefore all live strictly on the main branch.  (The snapshot's lane reaches the
same collapse through `correct_of_det`, its verdict being `decide (isSum …)` on
every tape.) -/
theorem correctAt_of_fallback_det (R : Routines) (n : ℕ) (x : Instance n)
    (hfb : R.fallback n x = true)
    (hdet : (x.yes ∧ R.mitm n x = true) ∨ (¬ x.yes ∧ R.mitm n x = false)) :
    CorrectAt R n x := by
  have hrun : ∀ ω : Draws, R.run n x ω = R.mitm n x := by
    intro ω
    simp [Routines.run, hfb]
  unfold CorrectAt
  dsimp only
  rcases hdet with ⟨hy, hm⟩ | ⟨hny, hm⟩
  · refine Or.inl ⟨hy, ?_⟩
    have hall : ∀ s : ℕ,
        R.run n x (fun r => ((tape (wordLength n x.bits) s) r).toNat) = true := by
      intro s
      rw [hrun]
      exact hm
    rw [count_const hall]
    exact Nat.mul_le_mul_right _ (by norm_num)
  · refine Or.inr ⟨hny, ?_⟩
    have hall : ∀ s : ℕ,
        R.run n x (fun r => ((tape (wordLength n x.bits) s) r).toNat) = false := by
      intro s
      rw [hrun]
      exact hm
    rw [count_const hall]
    exact Nat.mul_le_mul_right _ (by norm_num)

/-! ### The main branch, cut into instruction-segments

`agrees_main` is one equation, but it is not one obligation.  On the main branch
`Routines.run` is a three-deep dispatch over `prelim`, `aliasA`, `checksumB`, and
the four reachable leaves have *concrete* verdicts.  `agrees_main_iff_leaves`
records that split: proving the four leaves proves the equation, and — the
leaves carrying no `Option` plumbing — each leaf is exactly what an
instruction-level proof of that segment has to establish (reach the segment's
exit with that word in the accumulator, at fuel `R.cost n x`).

Two measurements are recorded here, because they decide how this half can be
worked, and neither is visible from the statement of `agrees_main`:

1. **The main obligation is not yet well-posed at the level stated.**  Three of
   the four segments are opaque fields of an *arbitrary* `Routines`.  No fixed
   `List Instr` computes an arbitrary total function `Instance n → Draws →
   Option Bool`, so `agrees_main` cannot be discharged for arbitrary `R` by
   writing a program: `Routines` must first gain *the programs* for `prelim`,
   `aliasA`, `checksumB` (and `mitm`) together with their own agreement
   hypotheses, and only then does `agrees_main` become a proposition about
   specific instruction text.  The missing lever is that refinement, not a
   longer proof of the same statement.

2. **The concrete program is a multi-word program, so `cost` must count word
   operations.**  §6.2 carries the estimates at `n²` fractional bits, while the
   statement's word is `w = 4(n+b) + ⌈log₂((n+2)⁴)⌉ = O(n+b)`; at `b = 1` the
   two cross at `n = 7` and `n²` stays ahead thereafter, so an `n²`-fractional
   dyadic does not fit in one word.  The trusted statement anticipates exactly
   this («arithmetic exceeding these limits is implemented by multiple word
   operations and charged accordingly»), hence `Routines.cost` must bound the
   *word-operation* count of the concrete program — a requirement on the `cost`
   field that `WithinEnvelope` alone does not state, and part of the D7
   boundary.

The test segment is the one segment §7 fully specifies (`rowTest`), so it is the
one with a worked reference here — including the paper's own squared form of the
comparison (`|B̂_s| ≥ 1/2 ⟺ |B̂_s|² ≥ 1/4`, `abs_ge_half_iff`) and the cons/nil
rules a loop proof consumes (`rowTest_cons_cons`, `rowTest_nil_left`,
`rowTest_nil_right`). -/

/-- The main branch's value, case 1: Proposition P (§4) decides, and its verdict
is the row's verdict.  Core: `prop_p_chebyshev` (B5). -/
theorem run_eq_of_prelim_some (R : Routines) (n : ℕ) (x : Instance n) (ω : Draws)
    (hf : R.fallback n x = false) {b : Bool} (hp : R.prelim n x ω = some b) :
    R.run n x ω = b := by
  simp [Routines.run, hf, hp]

/-- Case 2: Theorem A's `FAIL` — «If it fails, return NO», verbatim. -/
theorem run_eq_false_of_alias_none (R : Routines) (n : ℕ) (x : Instance n) (ω : Draws)
    (hf : R.fallback n x = false) (hp : R.prelim n x ω = none)
    (ha : R.aliasA n x ω = none) : R.run n x ω = false := by
  simp [Routines.run, hf, hp, ha]

/-- Case 3: Theorem B's `FAIL` — the same NO. -/
theorem run_eq_false_of_checksum_none (R : Routines) (n : ℕ) (x : Instance n) (ω : Draws)
    (hf : R.fallback n x = false) (hp : R.prelim n x ω = none)
    {Ahat : List ℚ} (ha : R.aliasA n x ω = some Ahat)
    (hb : R.checksumB n x ω = none) : R.run n x ω = false := by
  simp [Routines.run, hf, hp, ha, hb]

/-- Case 4: both phases produce estimates, and §7 step 7's test decides. -/
theorem run_eq_rowTest (R : Routines) (n : ℕ) (x : Instance n) (ω : Draws)
    (hf : R.fallback n x = false) (hp : R.prelim n x ω = none)
    {Ahat : List ℚ} (ha : R.aliasA n x ω = some Ahat)
    {Vhat : List ℚ} (hb : R.checksumB n x ω = some Vhat) :
    R.run n x ω = Routines.rowTest Ahat Vhat := by
  simp [Routines.run, hf, hp, ha, hb]

/-- The test on an empty left list never fires (`zipWith` truncates). -/
theorem rowTest_nil_left (V : List ℚ) : Routines.rowTest [] V = false := by
  simp [Routines.rowTest]

/-- Nor on an empty right list. -/
theorem rowTest_nil_right (A : List ℚ) : Routines.rowTest A [] = false := by
  simp [Routines.rowTest]

/-- **The test's loop rule** — its cons/cons step, in the `Bool`-or shape a
scan over the stored estimate list needs. -/
theorem rowTest_cons_cons (a : ℚ) (A : List ℚ) (v : ℚ) (V : List ℚ) :
    Routines.rowTest (a :: A) (v :: V)
      = (decide ((1 / 2 : ℚ) ≤ |v - a|) || Routines.rowTest A V) := by
  simp [Routines.rowTest]

/-- **§7 step 7 in the paper's own squared vocabulary.**  The paper states the
test as «the sum of the squares of the dyadic real and imaginary parts exceeds
1/4»; the estimate list carries the magnitude `|B̂_s| = |V̂_s − Â_s|`, and on
`ℚ` the two forms agree — so the in-tree test is the paper's test. -/
theorem abs_ge_half_iff (d : ℚ) : (1 / 2 : ℚ) ≤ |d| ↔ (1 / 4 : ℚ) ≤ d * d := by
  have h0 : (0 : ℚ) ≤ |d| := abs_nonneg d
  have hsq : |d| ^ 2 = d ^ 2 := sq_abs d
  have hd : d ^ 2 = d * d := by ring
  constructor
  · intro h; nlinarith [h0, h]
  · intro h
    have h2 : (1 / 2 : ℚ) ^ 2 ≤ |d| ^ 2 := by rw [hsq, hd]; linarith
    nlinarith [h0, h2]

/-- Segment 2 (Proposition P): on the guard's complement, if the phase decides,
the program's verdict at the abstract horizon is that decision. -/
def LeafP (R : Routines) (program : List Instr) : Prop :=
  ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    R.fallback n x = false → ∀ b : Bool, R.prelim n x (fun r => (ρ r).toNat) = some b →
      run program x ρ (R.cost n x) = some b

/-- Segment 5 (Theorem A's `FAIL`): the program reaches NO. -/
def LeafAnone (R : Routines) (program : List Instr) : Prop :=
  ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    R.fallback n x = false → R.prelim n x (fun r => (ρ r).toNat) = none →
      R.aliasA n x (fun r => (ρ r).toNat) = none →
      run program x ρ (R.cost n x) = some false

/-- Segment 6 (Theorem B's `FAIL`): the program reaches NO. -/
def LeafBnone (R : Routines) (program : List Instr) : Prop :=
  ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    R.fallback n x = false → R.prelim n x (fun r => (ρ r).toNat) = none →
      ∀ Ahat : List ℚ, R.aliasA n x (fun r => (ρ r).toNat) = some Ahat →
        R.checksumB n x (fun r => (ρ r).toNat) = none →
        run program x ρ (R.cost n x) = some false

/-- Segment 7 (§7 step 7's test): the program's verdict is the test of the two
stored estimate lists. -/
def LeafTest (R : Routines) (program : List Instr) : Prop :=
  ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    R.fallback n x = false → R.prelim n x (fun r => (ρ r).toNat) = none →
      ∀ Ahat : List ℚ, R.aliasA n x (fun r => (ρ r).toNat) = some Ahat →
        ∀ Vhat : List ℚ, R.checksumB n x (fun r => (ρ r).toNat) = some Vhat →
        run program x ρ (R.cost n x) = some (Routines.rowTest Ahat Vhat)

/-- The four segment obligations, no `Option` plumbing left. -/
def MainLeaves (R : Routines) (program : List Instr) : Prop :=
  LeafP R program ∧ LeafAnone R program ∧ LeafBnone R program ∧ LeafTest R program

/-- **`agrees_main`, cut per instruction-segment.**  The main branch's dispatch
is exhaustive over the three phases' outcomes, so the single equation is
*equivalent* to the four leaves above — no obligation is added, none is dropped,
and each leaf states a concrete verdict for one segment. -/
theorem agrees_main_iff_leaves (R : Routines) (program : List Instr) :
    (∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
        R.fallback n x = false →
          run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat)))
      ↔ MainLeaves R program := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n x ρ hf b hp
      rw [H n x ρ hf, run_eq_of_prelim_some R n x _ hf hp]
    · intro n x ρ hf hp ha
      rw [H n x ρ hf, run_eq_false_of_alias_none R n x _ hf hp ha]
    · intro n x ρ hf hp Ahat ha hb
      rw [H n x ρ hf, run_eq_false_of_checksum_none R n x _ hf hp ha hb]
    · intro n x ρ hf hp Ahat ha Vhat hb
      rw [H n x ρ hf, run_eq_rowTest R n x _ hf hp ha hb]
  · rintro ⟨hP, hA, hB, hT⟩ n x ρ hf
    cases hp : R.prelim n x (fun r => (ρ r).toNat) with
    | some b =>
      rw [run_eq_of_prelim_some R n x _ hf hp]
      exact hP n x ρ hf b hp
    | none =>
      cases ha : R.aliasA n x (fun r => (ρ r).toNat) with
      | none =>
        rw [run_eq_false_of_alias_none R n x _ hf hp ha]
        exact hA n x ρ hf hp ha
      | some Ahat =>
        cases hb : R.checksumB n x (fun r => (ρ r).toNat) with
        | none =>
          rw [run_eq_false_of_checksum_none R n x _ hf hp ha hb]
          exact hB n x ρ hf hp Ahat ha hb
        | some Vhat =>
          rw [run_eq_rowTest R n x _ hf hp ha hb]
          exact hT n x ρ hf hp Ahat ha Vhat hb

/-- The consumer form: four segment proofs are `agrees_main`. -/
theorem agrees_main_of_leaves {R : Routines} {program : List Instr}
    (h : MainLeaves R program) :
    ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
      R.fallback n x = false →
        run program x ρ (R.cost n x) = some (R.run n x (fun r => (ρ r).toNat)) :=
  (agrees_main_iff_leaves R program).mpr h

/-! ### The runtime envelope in reals, its monotonicity, and its absorption -/

/-- §7's «Running time» envelope, with the input's own `b` replaced by the
bound `n^c` the statement allows. -/
noncomputable def envE (c K : ℕ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ))
    * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K

theorem envE_pos (c K n : ℕ) : 0 < envE c K n := by
  rw [envE]
  refine mul_pos (Real.rpow_pos_of_pos (by norm_num) _) ?_
  exact pow_pos (by positivity) _

/-- `envE` is monotone in `n` — this is what lets the finite set of small `n`
below the absorption threshold be absorbed by a single constant. -/
theorem envE_mono (c K : ℕ) {n m : ℕ} (h : n ≤ m) : envE c K n ≤ envE c K m := by
  rw [envE, envE]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  have hexp : (tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ)
      ≤ (tau0 + 20 * epsPat) * (m : ℝ) + 2 * (m : ℝ) ^ (0.7 : ℝ) := by
    have ht : (0 : ℝ) ≤ tau0 + 20 * epsPat := by
      rw [tau0, epsPat]; norm_num
    have hpow : (n : ℝ) ^ (0.7 : ℝ) ≤ (m : ℝ) ^ (0.7 : ℝ) :=
      Real.rpow_le_rpow hn hnm (by norm_num)
    nlinarith
  have h1 : (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ))
      ≤ (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (m : ℝ) + 2 * (m : ℝ) ^ (0.7 : ℝ)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hexp
  have h2 : ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
      ≤ ((m : ℝ) + (m : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K := by
    apply pow_le_pow_left₀ (by positivity)
    have hnc : (n : ℝ) ^ ((c : ℕ) : ℝ) ≤ (m : ℝ) ^ ((c : ℕ) : ℝ) :=
      Real.rpow_le_rpow hn hnm (by positivity)
    linarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- §1's gap applied to `envE`: past the threshold, the sub-exponential and
polynomial factors are inside the slack. -/
theorem envE_absorb (c K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → envE c K n ≤ (2 : ℝ) ^ (alphaRow * (n : ℝ)) := by
  obtain ⟨N, hN⟩ := runtime_absorb c K
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [envE, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  exact h

/-! ### The horizon and the `BigO` -/

/-- The row's horizon: `T n = 2^(⌈0.4877·n⌉ + C₀)`. -/
noncomputable def rowHorizon (C₀ : ℕ) (n : ℕ) : ℕ := 2 ^ (Nat.ceil (alphaRow * (n : ℝ)) + C₀)

/-- **The bound in the statement's own `BigO`**: `T n ^ 10000 ≤ K · 2^(4877·n)`
with `K = 2^(10000·C₀ + 10000)`. -/
theorem rowHorizon_bigO (C₀ : ℕ) : BigO (rowHorizon C₀) (4877 / 10000) := by
  refine ⟨2 ^ (10000 * C₀ + 10000), ?_⟩
  intro n _
  have hden : (4877 / 10000 : Rat).den = 10000 := by norm_num
  have hnum : (4877 / 10000 : Rat).num.toNat = 4877 := by norm_num
  rw [hden, hnum]
  have hceil : Nat.ceil (alphaRow * (n : ℝ)) ≤ 4877 * n / 10000 + 1 := by
    rw [Nat.ceil_le]
    have hgoal : alphaRow * (n : ℝ) ≤ ((4877 * n / 10000 + 1 : ℕ) : ℝ) := by
      have hnat : 4877 * n ≤ 10000 * (4877 * n / 10000 + 1) := by
        have h1 := Nat.div_add_mod (4877 * n) 10000
        have h2 := Nat.mod_lt (4877 * n) (by norm_num : 0 < 10000)
        omega
      have hreal : 4877 * (n : ℝ) ≤ 10000 * ((4877 * n / 10000 + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have ha : alphaRow * (n : ℝ) = 4877 * (n : ℝ) / 10000 := by
        rw [alphaRow]; ring
      rw [ha]
      linarith
    exact hgoal
  have hexp : Nat.ceil (alphaRow * (n : ℝ)) + C₀ ≤ 4877 * n / 10000 + 1 + C₀ := by omega
  have hmono : rowHorizon C₀ n ≤ 2 ^ (4877 * n / 10000 + 1 + C₀) := by
    rw [rowHorizon]
    exact Nat.pow_le_pow_right (by norm_num) hexp
  have harith : (4877 * n / 10000 + 1 + C₀) * 10000 ≤ 4877 * n + 10000 + 10000 * C₀ := by
    have h1 : (4877 * n / 10000) * 10000 ≤ 4877 * n := Nat.div_mul_le_self _ _
    nlinarith
  calc rowHorizon C₀ n ^ 10000
      ≤ (2 ^ (4877 * n / 10000 + 1 + C₀)) ^ 10000 := Nat.pow_le_pow_left hmono 10000
    _ = 2 ^ ((4877 * n / 10000 + 1 + C₀) * 10000) := by rw [← pow_mul]
    _ ≤ 2 ^ (4877 * n + 10000 + 10000 * C₀) := Nat.pow_le_pow_right (by norm_num) harith
    _ = 2 ^ (10000 * C₀ + 10000) * 2 ^ (4877 * n) := by
      rw [← pow_add]
      congr 1
      omega

/-! ### The row theorem -/

/-- `K ≤ 2^C` in reals whenever `K ≤ C` — the constant-absorption step
(we use the crude `K ≤ 2^K`, so the absorbed constant is generous and the
arithmetic stays in `ℕ`). -/
theorem const_le_two_pow {K C : ℕ} (h : K ≤ C) : (K : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
  have h1 : K ≤ 2 ^ C :=
    le_trans (le_of_lt (Nat.lt_two_pow_self (n := K)))
      (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h)
  have h2 : (K : ℝ) ≤ ((2 ^ C : ℕ) : ℝ) := by exact_mod_cast h1
  calc (K : ℝ) ≤ ((2 ^ C : ℕ) : ℝ) := h2
    _ = (2 : ℝ) ^ (C : ℝ) := by
        push_cast
        rw [Real.rpow_natCast]

/-- `(2 : ℝ)^(⌈0.4877·n⌉ + C₀) = 2^⌈0.4877·n⌉ · 2^C₀` in the ℕ power sense. -/
theorem rowHorizon_eq (C₀ n : ℕ) :
    (rowHorizon C₀ n : ℝ)
      = (2 : ℝ) ^ (Nat.ceil (alphaRow * (n : ℝ)) : ℕ) * (2 : ℝ) ^ C₀ := by
  rw [rowHorizon]
  push_cast
  rw [pow_add]

/-- **`ss/kapila 0.4877` — the row's bound in the challenge's own vocabulary.**

Hypotheses (all documented, all at the D7 boundary):
`hcorr` = §7's correctness paragraph (`CorrectAt`); `henv` = §7's «Running
time» counter envelope (`Routines.WithinEnvelope`, whose Theorem A bullet is
in-tree via `o8_time_bound`/`thmA_part2`); `hD7` = the one named seam.

Conclusion: the trusted statement's own `SolvedInTime` at the literal the board
files, `4877 / 10000`. -/
theorem kapila_row
    (R : Routines)
    (hcorr : ∀ (n : ℕ) (x : Instance n), 2 ≤ n → CorrectAt R n x)
    (henv : ∀ c : ℕ, R.WithinEnvelope c)
    (hD7 : D7 R) :
    SolvedInTime (4877 / 10000 : Rat) := by
  classical
  refine ⟨hD7.program, ?_, ?_⟩
  · -- correctness: `CorrectAt` transferred through `D7.agrees`
    intro n x hn
    have hc := hcorr n x hn
    have htrue : count
        (fun s => run hD7.program x (tape (wordLength n x.bits) s) (R.cost n x) = some true)
        (2 ^ (wordLength n x.bits * R.cost n x))
        = count
          (fun s => R.run n x (fun r => ((tape (wordLength n x.bits) s) r).toNat) = true)
          (2 ^ (wordLength n x.bits * R.cost n x)) := by
      apply count_congr
      intro s
      rw [hD7.agrees n x (tape (wordLength n x.bits) s)]
      simp
    have hfalse : count
        (fun s => run hD7.program x (tape (wordLength n x.bits) s) (R.cost n x) = some false)
        (2 ^ (wordLength n x.bits * R.cost n x))
        = count
          (fun s => R.run n x (fun r => ((tape (wordLength n x.bits) s) r).toNat) = false)
          (2 ^ (wordLength n x.bits * R.cost n x)) := by
      apply count_congr
      intro s
      rw [hD7.agrees n x (tape (wordLength n x.bits) s)]
      simp
    refine ⟨R.cost n x, fun ρ => ?_, ?_⟩
    · rw [hD7.agrees]; simp
    · dsimp only
      rw [htrue, hfalse]
      unfold CorrectAt at hc
      dsimp only at hc
      exact hc
  · -- the time bound: one horizon for every outcome
    intro c
    obtain ⟨K₀, K, henv⟩ := henv c
    obtain ⟨Nabs, hNabs⟩ := envE_absorb c K
    -- the constant that absorbs §7's `K₀` and the finitely many `n < Nabs`
    set Big : ℕ := Nat.ceil ((K₀ : ℝ) * envE c K Nabs) + 1 with hBig
    set C₀ : ℕ := K₀ + Big + 2 with hC₀
    refine ⟨rowHorizon C₀, rowHorizon_bigO C₀, ?_⟩
    intro n x hn hbits ρ
    -- §7's envelope at this `c`, with `b ≤ n^c`
    have hcost : (R.cost n x : ℝ) ≤ (K₀ : ℝ) * envE c K n := by
      have h := henv n x hn hbits
      rw [envE]
      have hbits' : (x.bits : ℝ) ≤ (n : ℝ) ^ ((c : ℕ) : ℝ) := by exact_mod_cast hbits
      have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ)) :=
        le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
      have hle : (n : ℝ) + (x.bits : ℝ) + 2 ≤ (n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2 := by
        linarith
      have h2 : ((n : ℝ) + (x.bits : ℝ) + 2) ^ K
          ≤ ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K :=
        pow_le_pow_left₀ (by positivity) hle K
      calc (R.cost n x : ℝ)
          ≤ (K₀ : ℝ) * (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ))
              * ((n : ℝ) + (x.bits : ℝ) + 2) ^ K := h
        _ = (K₀ : ℝ) * ((2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ))
              * ((n : ℝ) + (x.bits : ℝ) + 2) ^ K) := by ring
        _ ≤ (K₀ : ℝ) * ((2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ))
              * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h2 hbase
        _ = (K₀ : ℝ) * envE c K n := by rw [envE]
    -- the ceiling dominates the absorbed exponent (all in `rpow`)
    set kR : ℝ := (Nat.ceil (alphaRow * (n : ℝ)) : ℝ) with hkR
    have hkR_nonneg : (0 : ℝ) ≤ kR := by positivity
    have hkR_ge : alphaRow * (n : ℝ) ≤ kR := by
      rw [hkR]
      exact Nat.le_ceil _
    have hceil_le : (2 : ℝ) ^ (alphaRow * (n : ℝ)) ≤ (2 : ℝ) ^ kR :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hkR_ge
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ kR := Real.one_le_rpow (by norm_num) hkR_nonneg
    have hstep : (R.cost n x : ℝ) ≤ (2 : ℝ) ^ kR * (2 : ℝ) ^ (C₀ : ℝ) := by
      rcases Nat.lt_or_ge n Nabs with hsmall | hbig
      · -- below the threshold: the single constant `Big` covers it
        have hmono : envE c K n ≤ envE c K Nabs := envE_mono c K (le_of_lt hsmall)
        have hBig2 : (K₀ : ℝ) * envE c K n ≤ (Big : ℝ) := by
          have h1 : (K₀ : ℝ) * envE c K n ≤ (K₀ : ℝ) * envE c K Nabs :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
          have h3 : ((K₀ : ℝ) * envE c K Nabs) ≤ ((Nat.ceil ((K₀ : ℝ) * envE c K Nabs) : ℕ) : ℝ) :=
            Nat.le_ceil _
          have h4 : ((Nat.ceil ((K₀ : ℝ) * envE c K Nabs) : ℕ) : ℝ) ≤ (Big : ℝ) := by
            have : Nat.ceil ((K₀ : ℝ) * envE c K Nabs) ≤ Big := by omega
            exact_mod_cast this
          linarith
        have hBig3 : (Big : ℝ) ≤ (2 : ℝ) ^ (C₀ : ℝ) := const_le_two_pow (by omega)
        calc (R.cost n x : ℝ) ≤ (K₀ : ℝ) * envE c K n := hcost
          _ ≤ (Big : ℝ) := hBig2
          _ ≤ (2 : ℝ) ^ (C₀ : ℝ) := hBig3
          _ ≤ (2 : ℝ) ^ kR * (2 : ℝ) ^ (C₀ : ℝ) := le_mul_of_one_le_left (by positivity) hone
      · -- past the threshold: §1's gap does the work
        have habs : envE c K n ≤ (2 : ℝ) ^ (alphaRow * (n : ℝ)) := hNabs n hbig
        have hKle : (K₀ : ℝ) ≤ (2 : ℝ) ^ (C₀ : ℝ) := const_le_two_pow (by omega)
        have h1 : (K₀ : ℝ) * envE c K n
            ≤ (2 : ℝ) ^ (C₀ : ℝ) * (2 : ℝ) ^ kR := by
          exact mul_le_mul hKle (le_trans habs hceil_le) (le_of_lt (envE_pos c K n)) (by positivity)
        calc (R.cost n x : ℝ) ≤ (K₀ : ℝ) * envE c K n := hcost
          _ ≤ (2 : ℝ) ^ (C₀ : ℝ) * (2 : ℝ) ^ kR := h1
          _ = (2 : ℝ) ^ kR * (2 : ℝ) ^ (C₀ : ℝ) := by ring
    -- the program halts: `D7.agrees` at `cost`, then fuel is inert
    have hhaltEq : exec hD7.program ρ (R.cost n x) 0 0
        (loadWords (wordLength n x.bits) x.input) = some (R.run n x (fun r => (ρ r).toNat)) := by
      have h := hD7.agrees n x ρ
      rwa [run] at h
    have hcostNat : R.cost n x ≤ rowHorizon C₀ n := by
      have hcast : ∀ a : ℕ, ((2 ^ a : ℕ) : ℝ) = (2 : ℝ) ^ (a : ℝ) := by
        intro a
        push_cast
        rw [Real.rpow_natCast]
      have hrow : ((rowHorizon C₀ n : ℕ) : ℝ) = (2 : ℝ) ^ kR * (2 : ℝ) ^ (C₀ : ℝ) := by
        rw [rowHorizon, hcast, hkR]
        push_cast
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have h : (R.cost n x : ℝ) ≤ (rowHorizon C₀ n : ℝ) := by
        rw [hrow]
        exact hstep
      exact_mod_cast h
    obtain ⟨k, hk⟩ : ∃ k, R.cost n x + k = rowHorizon C₀ n :=
      ⟨rowHorizon C₀ n - R.cost n x, by omega⟩
    have hglide := exec_eq_of_halted hD7.program ρ (R.cost n x) 0 0
      (loadWords (wordLength n x.bits) x.input) (by rw [hhaltEq]; simp) k
    show (exec hD7.program ρ (rowHorizon C₀ n) 0 0 (loadWords (wordLength n x.bits) x.input)).isSome
    rw [← hk, hglide, hhaltEq]
    simp

end SubsetSumL25.Row
