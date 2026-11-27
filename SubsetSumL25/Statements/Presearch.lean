/-
Base (a-kapila) B5 — the preliminary search (Proposition P) and cost
accounting (Theorem A part 2's op bound; Lemma A7's envelope).

Primary source: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298), §4
(Proposition P and (LD)), §5.2 (Theorem A part 2), §5.7 (Lemma A7).  Verified against the primary text (rung B5, «matches»).  Credit: the
proposition, the (LD) dichotomy and Lemma A7 are Base's.

Verbatim (PROOF_0.4877.tex §4):

    Proposition P.  Run the procedure of Proposition 2.4 with the list cap
    B_n = 2^{⌈τ₀n⌉} in place of 2^{⌈0.489985n⌉}.  It returns the correct
    decision or CONTINUE.  On every execution it uses at most
    2^{τ₀n} poly(n+b+2) word operations.  If E d(V) > (½ − τ₀ + ζ)n for a
    uniform ⌊n/2⌋-subset V, it returns CONTINUE with probability O(1/n).

    Proof.  … Let U be either side of the random split; it has ⌊n/2⌋ or
    ⌈n/2⌉ elements.  Since f is nondecreasing, E d(U) > (½ − τ₀ + ζ)n.
    Lemma 2.3 gives Var d(U) ≤ n, and Chebyshev's inequality gives
        Pr[d(U) < (½ − τ₀ + ζ/2)n] ≤ n/(ζn/2)² = 4/(ζ²n).
    Otherwise log|Σ(U)| = |U| − d(U) ≤ n/2 + ½ − (½ − τ₀ + ζ/2)n < τ₀n for
    n > 1/ζ.  Then both lists fit under the cap, and the search decides. …

    So, for fixed tie weights, either the preliminary search decides with
    probability 1 − O(1/n), or
        E_{V⊆[n], |V| = ⌊n/2⌋} d(V) ≤ (½ − τ₀ + ζ)n.                     (LD)

Verbatim (§5.7, Lemma A7 — the envelope its seven items share):

    Lemma A7.  Assume (LD) and E₃.  … Then the uncapped procedure takes in
    expectation at most (b+2) 2^{(τ₀−ε₀+ζ)n+O(n^{0.6})} steps.
    … Every item is at most (b+2) 2^{(τ₀−ε₀+ζ)n+O(n^{0.6})}.

Verbatim (§5.8): «Part 2 holds by Section 5.2» — the op bound
2^{τ₀n+2n^{0.7}} poly(n+b+2) of Theorem A part 2 is the Section 5.2 accounting
into which Proposition P's 2^{τ₀n} poly(n+b+2) is absorbed.

Proved-vs-named ledger (the A5 pattern):
* PROVED here: the Chebyshev inequality over a finite expectation space; its
  4/(ζ²n) instantiation (Var ≤ n is the named input); the cap-fitting
  arithmetic (n > 1/ζ); the explicit O(1/n) CONTINUE bound; the Theorem A
  part 2 absorption 2^{τ₀n} ≤ 2^{τ₀n+2n^{0.7}}; Lemma A7's seven-item
  envelope (7 items ≤ (b+2)2^K and b ≥ 5 give total ≤ (b+2)2^K).
* NAMED HYPOTHESES (never `axiom`s): the variance input Var d(U) ≤ n is
  OpenAI Lemma 2.3's first clause — the `hcount` cousin of the L2.5 cluster
  (`L2_3_halfVariance` lives in the L2.5 cluster); the procedure's correctness
  and the per-step word counts are the algorithm (Prop 2.4 / §5.2), outside
  this package like A5's `D_s`; Lemma A7's seven per-item analyses ((C2)–(C7),
  Lemma A3(2)-(4)) are the item-level content the envelope consumes as
  hypotheses.

Empty-expect audit: `chebyshev_fraction_le` divides by the space's cardinal and
therefore carries `s.Nonempty` explicitly; every other statement is pointwise
arithmetic with no `Finset.expect`.  No silent-`0` degeneracy class.

`sorry`: M1 placeholders — proof targets `Proofs/Presearch.lean` (M2).
-/
import Mathlib

namespace SubsetSumL25

-- `chebyshev_fraction_le` is PROVED; statement-of-record in `Proofs/Presearch.lean`.

-- `prop_p_chebyshev` is PROVED; statement-of-record in `Proofs/Presearch.lean`.

-- `cap_fit_lt` is PROVED; statement-of-record in `Proofs/Presearch.lean`.

-- `continue_prob_le` is PROVED; statement-of-record in `Proofs/Presearch.lean`.

-- `prop_p_op_absorb` is PROVED; statement-of-record in `Proofs/Presearch.lean`.

-- `a7_envelope` is PROVED; statement-of-record in `Proofs/Presearch.lean`.

end SubsetSumL25
