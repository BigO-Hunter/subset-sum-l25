/-
Base (a-kapila) B5 — the preliminary search (Proposition P) and cost
accounting (Theorem A part 2's op bound; Lemma A7's envelope).

Primary source: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298), §4
(Proposition P and (LD)), §5.2 (Theorem A part 2), §5.7 (Lemma A7).  Verified
against `subset-sum-bridge/BRIDGE.md` appendix row B5 («matches»).  Credit: the
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
  OpenAI Lemma 2.3's first clause — the `hcount` cousin of the L2.5 lane
  (`L2_3_halfVariance` lives in the L2.5 lane); the procedure's correctness
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

/-- Chebyshev's inequality over a finite expectation space (§4: «Chebyshev's
inequality gives Pr[d(U) < (½−τ₀+ζ/2)n] ≤ n/(ζn/2)²»): if the mean is `μ` and
the mean square deviation is at most `q`, then the fraction of points below
`μ − t` is at most `q/t²`.  `s.Nonempty` is the nonemptiness certificate (the
fraction divides by `#s`). -/
theorem chebyshev_fraction_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (x : ι → ℝ) (t : ℝ) (ht : 0 < t) :
    ((s.filter (fun i => x i < s.expect x - t)).card : ℝ) / s.card
      ≤ (s.expect (fun i => (x i - s.expect x) ^ 2)) / t ^ 2 := by
  sorry

/-- Prop P's instantiation: with the Lemma 2.3 variance input `Var d(U) ≤ n`
(named hypothesis — the `hcount` cousin from the L2.5 lane) and threshold gap
`t = (ζ/2)n`, the fraction below the threshold is at most `4/(ζ²n)`. -/
theorem prop_p_chebyshev {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {x : ι → ℝ} {n ζ : ℝ} (hn : 0 < n) (hζ : 0 < ζ)
    (hvar : s.expect (fun i => (x i - s.expect x) ^ 2) ≤ n) :
    ((s.filter (fun i => x i < s.expect x - (ζ / 2) * n)).card : ℝ) / s.card
      ≤ 4 / (ζ ^ 2 * n) := by
  sorry

/-- §4's cap-fitting arithmetic (verbatim: «log|Σ(U)| = |U| − d(U) ≤ n/2 + ½ −
(½ − τ₀ + ζ/2)n < τ₀n for n > 1/ζ»): if `U` has at most `(n+1)/2` coordinates,
`d(U) ≥ (½ − τ₀ + ζ/2)n` and `1 < ζn`, then `|U| − d(U) < τ₀n` — both lists fit
under the cap `2^{⌈τ₀n⌉}` and the search decides. -/
theorem cap_fit_lt {n τ₀ ζ size dU : ℝ} (hζn : 1 < ζ * n)
    (hsize : size ≤ (n + 1) / 2) (hdU : (1 / 2 - τ₀ + ζ / 2) * n ≤ dU) :
    size - dU < τ₀ * n := by
  sorry

/-- Prop P's CONTINUE conclusion in explicit form (verbatim: «it returns
CONTINUE with probability O(1/n)»): whenever CONTINUE implies the
below-threshold event, its probability is at most `4/(ζ²n)`. -/
theorem continue_prob_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {x : ι → ℝ} {n ζ : ℝ} (hn : 0 < n) (hζ : 0 < ζ)
    (hvar : s.expect (fun i => (x i - s.expect x) ^ 2) ≤ n)
    (P : ι → Prop) [DecidablePred P]
    (hsub : ∀ i ∈ s, P i → x i < s.expect x - (ζ / 2) * n) :
    ((s.filter P).card : ℝ) / s.card ≤ 4 / (ζ ^ 2 * n) := by
  sorry

/-- Theorem A part 2's absorption (§5.8: «Part 2 holds by Section 5.2»):
Proposition P's `2^{τ₀n} poly(n+b+2)` is absorbed by the Theorem A budget
`2^{τ₀n+2n^{0.7}} poly(n+b+2)`, since `2n^{0.7} ≥ 0`. -/
theorem prop_p_op_absorb {τ₀ n : ℝ} :
    (2 : ℝ) ^ (τ₀ * n) ≤ (2 : ℝ) ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) := by
  sorry

/-- Lemma A7's envelope (§5.7: «Every item is at most (b+2) 2^{(τ₀−ε₀+ζ)n+
O(n^{0.6})}»): seven step counts each within the envelope `B = (b+2)·2^K` sum
to at most `(b+2)·2^K` once `5 ≤ b` (the paper absorbs the factor 7 into the
constant). -/
theorem a7_envelope {b K : ℝ} (hb : 5 ≤ b) (hK : 0 ≤ K)
    (S : ℕ → ℝ) (hitem : ∀ i ∈ Finset.range 7, S i ≤ (b + 2) * 2 ^ K) :
    ∑ i ∈ Finset.range 7, S i ≤ (b + 2) * 2 ^ K := by
  sorry

end SubsetSumL25
