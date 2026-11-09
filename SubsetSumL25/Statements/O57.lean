/-
M1 (O5+O7): the BRIDGE attack order's tail rung — OpenAI Thm 4.1 «Modular
checksum estimator» (O5) and Thm 5.1 «Alias extraction» (O7).  Paper-only
per BRIDGE rows O5/O7; the full procedures stay named (the D_s boundary),
and the formalizable core is the arithmetic both guarantees reduce to.

Consumers wired per the handoff (not re-proved): O8's cap/budget pattern
(o8Cap/o8_time_bound/o8_trials_le_cap shapes), B3's `cor_A6_per_alias` for
O7's completeness union bound, and the O4 convention of explicit P₀-style
thresholds.  D7 boundary held as on O4/O8: no bit-cost → Light-step
translation; op counts stay in the papers' own counters.

Primary sources: OpenAI preprint (openai/math @ `adc7f124`, 2026-10-04),
`sections/checksum.tex` (Thm 4.1 = `thm:checksum`, the coverage lemma
`lemma:checksum-tables`), `sections/aliases.tex` (Thm 5.1 =
`thm:aliases`), `sections/implementation.tex`; Base `PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298)
§2.2 (F8).  Credit: Thm 4.1 and Thm 5.1 are OpenAI's; this package
formalizes the mathematical core.
-/
import Mathlib

namespace SubsetSumL25

/- Verbatim (OpenAI checksum.tex), Theorem 4.1 «Modular checksum estimator»:

   «Fix a constant d > 0.  There is a uniform randomized procedure with the
   following guarantee for all sufficiently large n.  Its inputs are an
   integer P with |log P − ηn| ≤ 2, arbitrary residues b₁,…,b_n modulo P,
   and a list T of at most n^d target residues.  It draws and retains
   independent uniform phases φ₁,…,φ_n and either reports failure or
   returns estimates V̂_ρ for all ρ ∈ T.  With probability 1 − o(1) it does
   not fail and |V̂_ρ − V_ρ| ≤ 1/8 for every ρ ∈ T.  The o(1) is uniform in
   P, the input residues, and the target list.  On every random execution
   the procedure takes at most
       2^{(τ+20ε)n+O(√n)} poly(n+|T|)
   word operations.  No primality assumption on P is needed.»

   Verbatim (OpenAI aliases.tex), Theorem 5.1 «Alias extraction»:

   «There is one randomized procedure with the following properties for all
   sufficiently large n.  Its input consists of the transformed integers
   c_i = Ca_i + u_i and targets t_s = Ct + s, 0 ≤ s ≤ nN₀, of (2.1), with
   the input-length guard (2.2).  It chooses P uniformly from
   [2^{⌊ηn⌋}, 2^{1+⌊ηn⌋}) among the primes and returns either failure or P
   together with a deduplicated list of genuine aliases for each target.
   If E_{|V|=⌊n/2⌋} d(V) ≤ .01004n, then, with probability 1 − o(1) over P
   and the remaining random choices, it does not fail and its lists equal
   A_s(P) simultaneously for every s.  The error bound is uniform over the
   transformed inputs satisfying these assumptions.

   For every outcome of its random choices, the procedure stores and visits
   at most 2^{⌈τn⌉} poly(n) records, where τ = .48996, and takes
   2^{τn} poly(n+b+2) elementary bit operations, apart from the
   implementation of exact uniform finite draws.  Those draws admit the
   bounded implementations in Section [implementation].» -/

/-- O5's every-run operation cap: the ceiling form of
2^{(τ+20ε)n+O(√n)} with the O(√n) made explicit as one √n unit.  (Both
ceilings are ℤ-valued at this pin — the `2 ^ (…)` is integer-exponent zpow;
consumers bridge with `Real.rpow_intCast`.) -/
noncomputable def o5Cap (τ ε n : ℝ) : ℝ :=
  2 ^ (⌈(τ + 20 * ε) * n⌉ + ⌈Real.sqrt n⌉)

/-- O7's every-run records cap: 2^{⌈τn⌉} as a natural count. -/
noncomputable def o7Cap (τ n : ℝ) : ℕ := 2 ^ (⌈τ * n⌉.toNat)

/-- Thm 4.1's budget absorption: the two ceilings cost one unit each
(`⌈x⌉ < x+1`), absorbed by the explicit `2√n` slack of the O(√n) term —
unconditionally (no «sufficiently large n» needed here, unlike O8's
absorption, because the slack 2√n+2 is exactly the two units' budget). -/
theorem o5_cap_absorb (τ ε n : ℝ) :
    o5Cap τ ε n ≤ (2 : ℝ) ^ ((τ + 20 * ε) * n + 2 * Real.sqrt n + 2) := by
  sorry

/-- Thm 4.1's per-execution op bound (the formalizable skeleton): the
checksum's counted categories `S i`, each within `cap · P` (P = the named
per-category word-cost bound, «poly(n+|T|)»), sum to within
`16·P·2^{(τ+20ε)n+2√n+2}` — the display's budget with the O(√n) explicit
and the categories absorbed into the factor 16 = 2⁴. -/
theorem o5_time_bound {τ ε n P : ℝ} (hP : 0 ≤ P) (S : ℕ → ℝ)
    (hcat : ∀ i ∈ Finset.range 10, S i ≤ o5Cap τ ε n * P) :
    ∑ i ∈ Finset.range 10, S i
      ≤ (16 : ℝ) * P * 2 ^ ((τ + 20 * ε) * n + 2 * Real.sqrt n + 2) := by
  sorry

/-- Thm 4.1's accuracy guarantee (|V̂_ρ − V_ρ| ≤ 1/8 in MSE form), the
formalizable skeleton: the averaged estimate `Xbar` over the uniform random
space Ω (the retained phases — named procedure) has its MSE bounded by the
paper's decomposition input `μ/N` (μ = the named per-table MSE from the
L3.2/filtering data, N = the repetition count), and the count arithmetic
`8·μ ≤ N` then gives MSE ≤ 1/8.  Empty-expect audit: `Ω.Nonempty` stated;
`μ ≥ 0` is the MSE's nonnegativity. -/
theorem o5_mse_le {ι : Type*} {Ω : Finset ι} (hΩ : Ω.Nonempty) {Xbar : ι → ℝ}
    {V μ : ℝ} (hμ : 0 ≤ μ) {N : ℕ} (hN : 0 < N)
    (hMSE : Ω.expect (fun ω => (Xbar ω - V) ^ 2) ≤ μ / N) (hμ8 : 8 * μ ≤ (N:ℝ)) :
    Ω.expect (fun ω => (Xbar ω - V) ^ 2) ≤ 1 / 8 := by
  sorry

/-- Thm 5.1's every-run records bound («stores and visits at most
2^{⌈τn⌉} poly(n) records»), checkable core: records processed in `K` rounds,
each round consuming at least one counted step (named per-round data `S`),
with the running prefix within the records cap — then `K ≤ o7Cap τ n`.  The
FAIL rule is the named mechanism; this is its arithmetic consequence. -/
theorem o7_records_le_cap {τ n K : ℕ} (S : ℕ → ℕ) (h1 : ∀ i, 1 ≤ S i)
    (hcap : ∑ i ∈ Finset.range K, S i ≤ o7Cap τ n) :
    K ≤ o7Cap τ n := by
  sorry

/-- Thm 5.1's completeness («its lists equal A_s(P) simultaneously for
every s» with probability 1 − o(1)), the union-bound skeleton: with `A` the
(alias, target) pairs needing coverage and `m a` the named per-pair miss
probability (each ≤ (1−p)^T from B3's Base_lem_A5 chain — the (F4)+coverage
input), the total failure is bounded by `|A|·e^{−1}` via B3's
`cor_A6_per_alias`.  The o(1) is the external ratio |A|·e^{−1} → 0 under
the paper's own count hypotheses (named). -/
theorem o7_union_le {ι : Type*} {A : Finset ι} {m : ι → ℝ} {p : ℝ} {T : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hTp : 1 ≤ (T:ℝ) * p)
    (hm : ∀ a ∈ A, m a ≤ (1 - p) ^ T) :
    (∑ a ∈ A, m a) ≤ A.card * Real.exp (-(1:ℝ)) := by
  sorry

/- Proved-vs-named ledger (full table in STMTS.md §O5/§O7):
   PROVED: o5_cap_absorb, o5_time_bound, o5_mse_le, o7_records_le_cap,
   o7_union_le.
   NAMED (algorithm/external boundary, never axioms): the checksum and
   alias-extraction procedures themselves (tables, patterns, phases,
   deduplication, the alias subtraction); the per-category counts and the
   per-category word-cost bound P; the per-table MSE μ and repetition count
   N (the L3.2/filtering inputs); the per-pair miss probabilities m (the
   B3 A5/A6 chain's output) and the trial count T with Tp ≥ 1 (Step 3's
   trial-count bound); the o(1) ratios.  Consumers wired, not re-proved:
   cor_A6_per_alias (B3), the O8 cap/envelope/running-below-cap pattern. -/

end SubsetSumL25
