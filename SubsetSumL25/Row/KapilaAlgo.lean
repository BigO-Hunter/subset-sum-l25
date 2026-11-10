/-
Row assembly for `ss/kapila 0.4877` — **piece (a): the algorithm as an
executable definition**.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298), §2.2
(parameters), §7 (the algorithm and its running time).

Why this file exists.  The landed O5/O7/O8 modules are the **mathematical
cores** of the checksum / alias / accounting theorems — Real-valued bounds on
abstract counters.  They are not the procedure.  A board row needs a
*procedure*: one finite program, run on every input, halting on every outcome.
This file is the procedure of §7 written as a computable Lean definition, so
that the assembly's remaining obligation is a translation (see
`SubsetSumL25.Row.KapilaRow.D7`), not a search for what the algorithm is.

Division of labour, stated plainly:

* **§7's dispatch** (guard → exact fallback; tie weights and transform;
  Proposition P; the prime and the phases; Theorem A; Theorem B; the
  `|B̂_s| ≥ 1/2` test) is written here, executably — the test runs over the
  finite estimate list, in `ℚ` (`n²` fractional bits, §6.2), so the comparison
  is `decide`-able integer arithmetic and not a real-number oracle.
* **the six sub-procedures** (§6.3's exact meet-in-the-middle; Proposition P;
  Theorem A's alias phase sums; Theorem B's checksum; the transform) are
  fields of `Routines`.  Making them `List Instr` programs *is* the D7 seam —
  the campaign's one named seam — and this file deliberately does not pretend
  otherwise.  What it does do is fix their **types**: once written, the seam
  has nowhere to hide (a `Routines` value is a computable function, and the
  cost fields are ℕ-valued, so §7's accounting is ℕ arithmetic, not prose).

Nothing here is new mathematics.  Every parameter is Base's; every envelope is
§7's; the credit chain is Base → Bills → us.
-/
import Mathlib
import SubsetSumL25.Row.Statement

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §2.2 — the parameters, verbatim from Base's table

These are the paper's constants, carried as reals so that §7's exponent
arithmetic and Theorem A/B's error displays can be stated without casts at
every use.  `alphaRow` is the row's bound: `0.4877 = 4877/10000`. -/

/-- «τ₀ = 0.48769» — the work exponent. -/
noncomputable def tau0 : ℝ := 48769 / 100000

/-- «η = 0.51613» — the large prime `P` has about `ηn` bits. -/
noncomputable def etaP : ℝ := 51613 / 100000

/-- «ε = 10⁻⁸» — pattern accuracy. -/
noncomputable def epsPat : ℝ := 1 / 100000000

/-- «μ = 0.473» — the block `M` has about `μn` elements. -/
noncomputable def muBlock : ℝ := 473 / 1000

/-- «a = 0.0082» — the left masks have about `a|M|` elements. -/
noncomputable def aMask : ℝ := 82 / 10000

/-- «γ = 0.06035» — the small prime `P′` has about `γ|M|` bits. -/
noncomputable def gammaP : ℝ := 6035 / 100000

/-- «l = 0.48377» — the left part `L` has about `ln` elements. -/
noncomputable def lPart : ℝ := 48377 / 100000

/-- The row's bound `α = 0.4877 = 4877/10000`. -/
noncomputable def alphaRow : ℝ := 4877 / 10000

/-- The slack §1 spends: `α − (τ₀ + 20ε) = 49/5000000 = 9.8·10⁻⁶`. -/
noncomputable def slack : ℝ := 49 / 5000000

/-- §7's input guard: `10⁶⌈log₂(b+1)⌉ ≤ n`, with `b` the challenge's
`Instance.bits` (so `⌈log₂(b+1)⌉ = ⌊log₂ b⌋ + 1`, the identity the statement's
README checks).  Applied to `x.bits`, this is `10⁶·(⌊log₂ x.bits⌋ + 1) ≤ n`. -/
def guardOk (n b : ℕ) : Prop := 1000000 * (Nat.log2 b + 1) ≤ n

instance (n b : ℕ) : Decidable (guardOk n b) := by unfold guardOk; infer_instance

/-! ### The sub-procedures of §7, and the dispatch

`Routines` is a *record of computable functions*: every decision field is a total
function, so `Routines.run` below is a genuine executable definition (no
`noncomputable`, no `Classical.choice` in the data).  The randomness is a
single stream `ω : ℕ → ℕ` of fresh independent uniform words — the paper's
«a fresh independent uniform word costs one operation», read
one-way as the trusted statement's `rand` demands.  The transcription
`ω r ↦ (ρ r).toNat` from the challenge's `ρ : ℕ → BitVec w` is the seam's job
(`D7.agrees`), not this file's.

**Reification (per-field programs).**  Each decision field now carries *its
instruction text* (`mitmProg`, `prelimProg`, `aliasProg`, `checksumProg`) and
*its agreement hypothesis* — «that program, at that field's cost, halts with that
field's verdict».  This is what makes `agrees_main` a proposition about specific
instruction text rather than about an arbitrary total function: an arbitrary
`Instance n → Draws → Option Bool` has no program, and no amount of proving
changes that.  The first field is *discharged*, not merely named: `mitmProg`'s
agreement has exactly the shape `fallback_agrees_iff` exhibits, so supplying it
proves `D7.agrees_fallback` verbatim (`fallback_agrees_of_mitmProg`), and the
reference package (`subsetsum-v2-snapshot`'s `prog2`) already proves a statement
of that shape.  The three phase programs are **named obligations**: stated, with
the exact hypothesis their leaf consumes, so the structure is complete and each
leaf has precisely one program premise. -/

/-- The procedure's view of the random tape: fresh uniform words, read
one-way, indexed by draw number. -/
abbrev Draws := ℕ → ℕ

/-- §7's own reading of a phase's `FAIL`: «If it fails, return NO».  A phase field
is `Option Bool` (`none` = `FAIL`); the *decision* it contributes is this map.  It
is *not* injective (`none` and `some false` agree), and that is the point: which
of the two happened is a fact about **control flow** — `LeafAnone`/`LeafBnone` say
the run goes on to the next phase — not about the accumulator a segment leaves
behind.  Stating per-field agreement through this map keeps each phase's program
obligation a statement about *its own* verdict and nothing else. -/
def failToNo : Option Bool → Bool
  | some b => b
  | none => false

/-- §7's sub-procedures, each an executable function, each with the cost
counter §7 charges it.  `none` is the paper's `FAIL`.

Estimates are `List ℚ`: the `nN₀ + 1` values `Â_s` (respectively `V̂_ρ`),
carried at the `n²` fractional bits of §6.2.  A finite list is what makes
§7 step 7's test decidable — the paper's «the test compares the sum of the
squares of the dyadic real and imaginary parts with 1/4» is integer
arithmetic on dyadics, not a real-number oracle.

The docstrings name, for each field, which landed module holds the
mathematical core and what supplying the field costs the assembly. -/
structure Routines where
  /-- §7 step 1: «the exact meet-in-the-middle fallback of Section 6.3».
  A deterministic `List Instr` witness for this already exists: the verified
  `α = 1/2` package (`subsetsum-v2-snapshot`, `Race.bound : SolvedInTime
  (1/2)`), whose `prog2` is exactly such a fallback. -/
  mitm : (n : ℕ) → Instance n → Bool
  /-- §7 step 1's cost (exact fallback). -/
  mitmCost : (n : ℕ) → Instance n → ℕ
  /-- **§7 step 1's program.**  The exact meet-in-the-middle of §6.3 as
  instruction text — one finite `List Instr` for every `n` and `b`, no advice, no
  dependence on `c`.  This is the field the reference package supplies: the
  verified `α = 1/2` row's `prog2` (`subsetsum-v2-snapshot`,
  `Submission/Prog2Race.lean`, `Race.bound : SolvedInTime (1/2)`) is one such
  program, proved segment by segment. -/
  mitmProg : List Instr
  /-- **The first field's agreement hypothesis** — the shape
  `fallback_agrees_iff` (`SubsetSumL25.Row.KapilaRow`) proves is *exactly* the
  D7 fallback branch: `mitmProg`, run at `mitmCost`, halts with `mitm`'s verdict.
  Supplying this field discharges `D7.agrees_fallback` verbatim (see
  `fallback_agrees_of_mitmProg`); the reference program proves a statement of
  precisely this form, so the hypothesis is already *met* in the `α = 1/2` row and
  only has to be re-instantiated here. -/
  mitm_agrees : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    run mitmProg x ρ (mitmCost n x) = some (mitm n x)
  /-- §4's preliminary search (Proposition P): `some b` means it decided.
  Core: `SubsetSumL25.prop_p_chebyshev` (B5, measured axiom-clean). -/
  prelim : (n : ℕ) → Instance n → Draws → Option Bool
  prelimCost : (n : ℕ) → Instance n → ℕ
  /-- **§4 / Proposition P's program** — a named obligation, stated not proved
  (no in-tree instruction text yet).  `LeafP` consumes exactly this segment. -/
  prelimProg : List Instr
  /-- Proposition P's segment agreement, through §7's `FAIL` → NO reading. -/
  prelim_agrees : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    (run prelimProg x ρ (prelimCost n x)).map failToNo
      = some (failToNo (prelim n x (fun r => (ρ r).toNat)))
  /-- §2.2/§7 step 2: the tie weights and the transform `c_i = Ca_i + u_i`,
  `t_s = Ct + s` (the isolation transform).  Core: `L2_1_isolation`. -/
  transform : (n : ℕ) → Instance n → Draws → List ℕ × List ℕ
  transformCost : (n : ℕ) → Instance n → ℕ
  /-- §7 step 5 / §5.2: Theorem A — the alias phase sums.  `some Â` carries the
  `nN₀ + 1` estimates `Â_s`.  Core: O5's checksum estimator + O7's alias
  extraction, assembled at the §5.8 level by `Proofs/M7.lean`
  (`thmA_part1_fail_le`, `thmA_part2`). -/
  aliasA : (n : ℕ) → Instance n → Draws → Option (List ℚ)
  aliasCost : (n : ℕ) → Instance n → ℕ
  /-- **§5.2 / Theorem A's alias-phase program** — a named obligation, stated not
  proved.  `LeafAnone` consumes exactly this segment, and `LeafTest` consumes the
  estimate list it leaves behind. -/
  aliasProg : List Instr
  /-- Theorem A's segment agreement: the segment halts, and its verdict is
  «the phase succeeded» — `some Â` reads as `true`, the paper's `FAIL` as `false`.
  This is the `Option`-free statement `LeafAnone`/`LeafTest` can consume. -/
  alias_agrees : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    run aliasProg x ρ (aliasCost n x) = some (aliasA n x (fun r => (ρ r).toNat)).isSome
  /-- §7 step 6 / §6: Theorem B — the checksum with the 43-filter family.
  `some V̂` carries the estimates `V̂_ρ`.  Core: B4's region analysis
  (`Proofs/ThmB.lean`: `region_existence`, `lem_B2_domination`,
  `row_errors_le_six_eps`). -/
  checksumB : (n : ℕ) → Instance n → Draws → Option (List ℚ)
  checksumCost : (n : ℕ) → Instance n → ℕ
  /-- **§6 / Theorem B's checksum-phase program** — a named obligation, stated not
  proved.  `LeafBnone` consumes this segment; `LeafTest` consumes the `V̂` list it
  leaves behind. -/
  checksumProg : List Instr
  /-- Theorem B's segment agreement: halt, with «the phase succeeded» as the
  verdict — the same `Option`-free shape as `alias_agrees`. -/
  checksum_agrees : ∀ (n : ℕ) (x : Instance n) (ρ : ℕ → BitVec (wordLength n x.bits)),
    run checksumProg x ρ (checksumCost n x)
      = some (checksumB n x (fun r => (ρ r).toNat)).isSome
  /-- The paper's cutoff `n_*` (§7: «a fixed cutoff n_* gives success
  probability at least 5/6»). -/
  nStar : ℕ

namespace Routines

/-- §7 step 1's guard: `n < n_* ∨ 10⁶⌈log₂(b+1)⌉ > n` sends the input to the
exact fallback. -/
def fallback (R : Routines) (n : ℕ) (x : Instance n) : Bool :=
  decide (n < R.nStar ∨ ¬ guardOk n x.bits)

/-- §7 step 7's test: some `s` has `|B̂_s| = |V̂_s − Â_s| ≥ 1/2`, read off the
two finite estimate lists. -/
def rowTest (Ahat Vhat : List ℚ) : Bool :=
  (Ahat.zipWith (fun a v => decide ((1 / 2 : ℚ) ≤ |v - a|)) Vhat).any id

/-- **§7's algorithm, executably.**  Steps 2–6 are the sub-procedures; step 7's
test is `rowTest`.  A `FAIL` from Theorem A or Theorem B returns NO, verbatim:
«If it fails, return NO». -/
def run (R : Routines) (n : ℕ) (x : Instance n) (ω : Draws) : Bool :=
  if R.fallback n x then R.mitm n x
  else
    match R.prelim n x ω with
    | some b => b
    | none =>
      match R.aliasA n x ω with
      | none => false
      | some Ahat =>
        match R.checksumB n x ω with
        | none => false
        | some Vhat => rowTest Ahat Vhat

/-- §7's «Running time» accounting: the five bullets, summed.  This is a ℕ
counter — the paper's own unit, «word operations» — so §7's composition is
arithmetic, and the two bullets we hold in-tree are consumed by name
(Theorem A's: `o8_time_bound`, re-displayed as `thmA_part2`; Proposition P's:
`prop_p_chebyshev`).  The `n³` factor is §7's prime-draw bullet («at most `n³`
candidates»), charged as `n³·poly` through the last summand's `(n + b + 2)`. -/
def cost (R : Routines) (n : ℕ) (x : Instance n) : ℕ :=
  if R.fallback n x then R.mitmCost n x
  else
    R.transformCost n x + R.prelimCost n x + R.aliasCost n x + R.checksumCost n x
      + ((n : ℕ) ^ 3) * (n + x.bits + 2)

/-- §7's «Running time» paragraph as a proposition: on inputs with `b ≤ n^c`
the total is at most `K₀ · 2^{(τ₀+20ε)n + 2n^{0.7}} · (n + b + 2)^K`.

**Which side of the accounting this speaks.**  `R.cost` counts the paper's own
unit — **word operations** (§7's bullets are word-op charges, and the trusted
statement's «a fresh independent uniform w-bit random word costs one operation»
fixes the same unit).  `WithinEnvelope` is therefore a word-operation envelope,
not a bit-cost envelope: there is no bit→step translation inside it.  That
translation is `D7`, the named seam — `D7.program` is the instruction text, and
`D7`'s agreement is what ties word-operation accounting to `Instr` steps.

The distinction is load-bearing because the concrete program is a **multi-word**
program: §6.2 carries the estimates at `n²` fractional bits while the statement's
word is `w = 4(n+b) + ⌈log₂((n+2)⁴)⌉ = O(n+b)`, so at `b = 1` the curves cross at
`n = 7` and `n²` stays ahead — an `n²`-fractional dyadic does not fit in one word.
The statement contemplates exactly this («arithmetic exceeding these limits is
implemented by multiple word operations and charged accordingly»), so every
dyadic operation costs up to `wordOpFactor n = n² + 1` word operations.  That
expansion does **not** move the row's exponent: `withinEnvelope_wordop_absorb`
below shows it is absorbed by raising the envelope's existentially quantified
polynomial exponent `K` by three, and `K` is §7's to choose. -/
def WithinEnvelope (R : Routines) (c : ℕ) : Prop :=
  ∃ K₀ K : ℕ, ∀ (n : ℕ) (x : Instance n), 2 ≤ n → x.bits ≤ n ^ c →
    (R.cost n x : ℝ)
      ≤ (K₀ : ℝ) * (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ))
        * ((n : ℝ) + (x.bits : ℝ) + 2) ^ K

end Routines

/-! ### The multi-word charge, and why it does not move the row's exponent

§6.2's estimates live at `n²` fractional bits; the statement's word is
`w = 4(n+b) + ⌈log₂((n+2)⁴)⌉`.  For `b ≤ n` and `n ≥ 10` this gives
`w ≤ 8n + 4log₂(n+2) + 1 < n²` (and at `b = 1` the curves cross as early as
`n = 7`), so there the dyadic is *wider than a word* and the concrete program
spends several word operations per arithmetic step — the case the statement
contemplates («multiple word operations and charged accordingly»).  The statement
allows `b ≤ n^c`, so the routed class also contains regimes where the word is
wider and the ratio is 1; the charge is therefore stated as the uniform bound
`⌈n²/w⌉ + 1 ≤ wordOpFactor n = n² + 1`, which covers both.  The charge is real and
polynomial: it is already inside §7's `(n + b + 2)^K` with `K` three larger. -/

/-- The multi-word expansion factor: one dyadic operation on `n²`-bit operands in
`w`-bit words costs at most `⌈n²/w⌉ + 1 ≤ n² + 1` word operations. -/
def wordOpFactor (n : ℕ) : ℕ := n ^ 2 + 1

/-- The expansion factor is inside the envelope's own polynomial factor. -/
theorem wordOpFactor_le_cube (n b : ℕ) : wordOpFactor n ≤ (n + b + 2) ^ 3 := by
  have h1 : wordOpFactor n ≤ (n + 2) ^ 3 := by
    rw [wordOpFactor]
    nlinarith [Nat.zero_le n]
  exact le_trans h1 (Nat.pow_le_pow_left (by omega) 3)

/-- **Multi-word charging is absorbed by the envelope's existential `K`.**  If
`cost` obeys §7's word-operation envelope then so does `cost` *times* the
multi-word expansion factor, with `K` raised by three — so the concrete
multi-word program needs no re-derivation of the row's exponent, only a larger
polynomial constant.  This is the statement that closes the accounting seam named
in `Routines.WithinEnvelope`'s docstring. -/
theorem withinEnvelope_wordop_absorb {R : Routines} {c : ℕ} (h : R.WithinEnvelope c) :
    ∃ K₀ K : ℕ, ∀ (n : ℕ) (x : Instance n), 2 ≤ n → x.bits ≤ n ^ c →
      ((R.cost n x * wordOpFactor n : ℕ) : ℝ)
        ≤ (K₀ : ℝ) * (2 : ℝ) ^ ((tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ))
          * ((n : ℝ) + (x.bits : ℝ) + 2) ^ K := by
  obtain ⟨K₀, K, hK⟩ := h
  refine ⟨K₀, K + 3, fun n x hn hb => ?_⟩
  set E : ℝ := (tau0 + 20 * epsPat) * (n : ℝ) + 2 * (n : ℝ) ^ (0.7 : ℝ) with hE
  set P : ℝ := (n : ℝ) + (x.bits : ℝ) + 2 with hP
  have h1 : (R.cost n x : ℝ) ≤ (K₀ : ℝ) * (2 : ℝ) ^ E * P ^ K := hK n x hn hb
  have hf : (wordOpFactor n : ℝ) ≤ P ^ 3 := by
    have hnat : (((n + x.bits + 2) ^ 3 : ℕ) : ℝ) = P ^ 3 := by
      rw [hP]; push_cast; ring
    have hc : (wordOpFactor n : ℝ) ≤ (((n + x.bits + 2) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast wordOpFactor_le_cube n x.bits
    rwa [hnat] at hc
  have hcast : ((R.cost n x * wordOpFactor n : ℕ) : ℝ) = (R.cost n x : ℝ) * (wordOpFactor n : ℝ) := by
    push_cast
    ring
  have hP0 : (0 : ℝ) ≤ P := by rw [hP]; positivity
  calc ((R.cost n x * wordOpFactor n : ℕ) : ℝ)
      = (R.cost n x : ℝ) * (wordOpFactor n : ℝ) := hcast
    _ ≤ ((K₀ : ℝ) * (2 : ℝ) ^ E * P ^ K) * P ^ 3 :=
        mul_le_mul h1 hf (by positivity) (by positivity)
    _ = (K₀ : ℝ) * (2 : ℝ) ^ E * P ^ (K + 3) := by rw [pow_add]; ring

/-! ### The routing, read from the `false` side

`Routines.fallback` is a `decide`d `Bool`, so its `false` side unfolds to a
conjunction and nothing more.  Both branches of the D7 seam read this lemma: it
is what makes `agrees_main`'s hypothesis («the guard admits this input»)
identical to «`n ≥ n_*` and `10⁶⌈log₂(b+1)⌉ ≤ n`», and it is what lets guard
coverage (`KapilaGuard.fallback_false_eventually`) pin down *where* the main
branch runs. -/
theorem fallback_eq_false_iff (R : Routines) (n : ℕ) (x : Instance n) :
    R.fallback n x = false ↔ R.nStar ≤ n ∧ guardOk n x.bits := by
  by_cases h2 : guardOk n x.bits
  · by_cases h1 : R.nStar ≤ n
    · have hlt : ¬ (n < R.nStar) := by omega
      simp [Routines.fallback, hlt, h2, h1]
    · have hlt : n < R.nStar := by omega
      simp [Routines.fallback, hlt, h2, h1]
  · simp [Routines.fallback, h2]

/-- The near side of the routing: above `n_*`, the bit-guard alone decides the
branch. -/
theorem fallback_false_of_guard {R : Routines} {n : ℕ} {x : Instance n}
    (hn : R.nStar ≤ n) (hg : guardOk n x.bits) : R.fallback n x = false :=
  (fallback_eq_false_iff R n x).mpr ⟨hn, hg⟩

end SubsetSumL25.Row
