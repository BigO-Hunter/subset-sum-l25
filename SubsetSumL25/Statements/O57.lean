/-
M1 (O5+O7): OpenAI Thm 4.1 «Modular checksum estimator» (O5) and Thm 5.1
«Alias extraction» (O7) — verbatim quotes and pointers.  This file holds NO
declarations: the statement-of-record for everything is `Proofs/O57.lean`
(M2 proved all five).

Paper-only per BRIDGE rows O5/O7; the D7 boundary holds as on O4/O8: the
procedures stay named and no Light-step translation is imported.

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
   bounded implementations in Section [implementation].»

Declarations (all in `Proofs/O57.lean`, all proved — see STMTS.md §O5/§O7
for the proved-vs-named ledger):

* `o5Cap`, `o7Cap`       — the two caps (O5's ceiling-form budget; O7's
                           ℕ-valued records cap 2^{⌈τn⌉}).
* `o5_cap_absorb`        — the two ceilings absorb unconditionally into the
                           explicit 2√n+2 slack (no «sufficiently large n»
                           needed, unlike O8's absorption).
* `o5_time_bound`        — Thm 4.1's per-execution op bound: categories ≤
                           cap·P ⟹ total ≤ 16·P·budget (P named).
* `o5_mse_le`            — Thm 4.1's accuracy: MSE ≤ μ/N ≤ 1/8 (μ/N the
                           named decomposition input).
* `o7_records_le_cap`    — Thm 5.1's records bound, checkable core.
* `o7_union_le`          — Thm 5.1's completeness union bound, consuming
                           B3's `cor_A6_per_alias`.

Statement-hygiene notes carried from M1:

* **Empty-expect audit:** `o5_mse_le` is the only expect-touching
  statement; `Ω.Nonempty` stated.  `o5Cap`'s ℤ-ceilings bridge per the O8
  pattern (`Real.rpow_intCast`); `o7Cap`'s `.toNat` (the paper's τn ≥ 0).
* **Identifier note:** `X̄` (combining macron) is not a valid Lean
  identifier — the Lean name is `Xbar` (the `Ŝ`-class gotcha, second
  occurrence).
-/

end SubsetSumL25
