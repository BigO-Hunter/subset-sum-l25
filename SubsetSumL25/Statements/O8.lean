/-
M1 (O8): Base §5.2's word-RAM accounting — the Step-6 cap, Theorem A part 2's
bound, the Step-3 trial-count bound, and the per-execution draw bound.  This is
Base's OWN accounting (BRIDGE row O8, "paper-only"); the bit-cost → Light-step
translation is D7 (L5's) and is deliberately NOT imported — every statement
here counts word operations / elementary steps in Base's own counters.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298), §5.1 (Thm A),
§5.2 (the procedure, Step 3 and Step 6, closing accounting paragraph), §5.8
(bullet 5, «A capped execution makes at most 2^{O(n)} draws»).  Cross-checked
against `subset-sum-bridge/BRIDGE.md` rows O8 and B5.  Credit: the accounting
is Base's; this package formalizes it.
-/
import Mathlib

namespace SubsetSumL25

/- Verbatim §5.1, Theorem A part 2:
   «On every execution the procedure uses at most
   2^{τ₀ n + 2n^{0.7}} poly(n+b+2) word operations.»

   Verbatim §5.2 Step 6 (the cap):
   «Count the elementary steps of Steps 1--5: subsets enumerated, merge
   operations, masks listed, keys sorted, records formed, records visited,
   members expanded, dictionary operations, terms summed, and trial divisions.
   Return FAIL as soon as the count would exceed 2^{⌈τ₀n⌉+⌈n^{0.7}⌉}.
   Also return FAIL if a bounded sampler fails.»

   Verbatim §5.2, the closing accounting paragraph:
   «Each step costs poly(n+b) word operations.  Keys have O(b + log n) bits,
   masks have m bits, and the dictionaries are balanced search trees.  The
   finite-precision sums use n² fractional bits (Section 6.2).  With the cap,
   this proves part 2 of Theorem A.»

   Verbatim §5.2 Step 3 (the trial count):
   «… T = n⁷ 2^{e_n} ⌈1/Shat⌉ … where e_n is an integer with 2n^{0.6} ≤ e_n ≤
   2n^{0.6}+1.  Then n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂}.»  with
   F̂ = log(1/Shat) + e_n and Shat = (1/n²)∑_{j=1}^{n²} 2^{−d(V_j)}.

   Verbatim §5.8, failure bullet 5:
   «A bounded sampler fails.  A capped execution makes at most 2^{O(n)} draws,
   so this has probability 2^{O(n)}(2^{−n³} + e^{−c₀n²}) = o(1).» -/

/-- The cap of §5.2 Step 6, as a real bound. -/
noncomputable def o8Cap (τ₀ n : ℝ) : ℝ := 2 ^ (⌈τ₀ * n⌉ + ⌈n ^ (0.7 : ℝ)⌉)

/-- The Step-6 cap fits inside Thm A part 2's budget exponent: the two
ceilings cost one unit each (`⌈x⌉ ≤ x+1`), absorbed by the `+2n^{0.7}` slack.
(`n ≥ 0` keeps `n^{0.7}` non-junk; the paper's `n` is the input size.) -/
theorem o8_cap_absorb {τ₀ n : ℝ} (hn : 0 ≤ n) :
    o8Cap τ₀ n ≤ (2 : ℝ) ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) := by
  sorry

/-- §5.2 Step 6's envelope: the ten counted categories (subsets enumerated,
merge operations, masks listed, keys sorted, records formed, records visited,
members expanded, dictionary operations, terms summed, trial divisions) with
each category at most `C` sum to at most `10·C`.  Each category's own bound is
a named item-level input — the procedure's per-category analyses are the
algorithm (the A5/B5 pattern). -/
theorem o8_cap_envelope {C : ℝ} (S : ℕ → ℝ)
    (hitem : ∀ i ∈ Finset.range 10, S i ≤ C) :
    ∑ i ∈ Finset.range 10, S i ≤ (10 : ℝ) * C := by
  sorry

/-- Thm A part 2 (§5.1), the formalizable skeleton over the package's
data-as-hypotheses contract: if the ten elementary-step totals `S i` are each
within `cap · P`, where `P` is the named per-category word-cost bound («each
step costs poly(n+b)»), then the total is within `16·P·2^{τ₀n+2n^{0.7}}` —
part 2's display with the `poly(n+b+2)` slot filled by the named `P` and the
ten categories absorbed into the factor 16 = 2⁴. -/
theorem o8_time_bound {τ₀ n P : ℝ} (hn : 0 ≤ n) (hP : 0 ≤ P) (S : ℕ → ℝ)
    (hcat : ∀ i ∈ Finset.range 10, S i ≤ o8Cap τ₀ n * P) :
    ∑ i ∈ Finset.range 10, S i ≤ (16 : ℝ) * P * 2 ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) := by
  sorry

/-- §5.2 Step 3's verbatim two-sided trial-count bound.  `Shat` is the Step-3
average (`0 < Shat ≤ 1`: positivity is the well-formedness of `1/Shat`; `Shat ≤ 1`
follows in the application from L2.2's proved `d(V) ≥ 0` and the draw
structure, but the `V_j` draws are the algorithm's data, so both are carried
as hypotheses).  `F̂ = log₂(1/Shat) + e_n` with `T = n⁷ 2^{e_n} ⌈1/Shat⌉` gives
«n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂}».  (`e_n`'s integer range is Lemma A3's input, not
this bound's — the proof needs only `0 < Shat ≤ 1`.) -/
theorem o8_trial_count_bound {n Shat e T : ℝ} (hn : 0 ≤ n) (hS : 0 < Shat)
    (hS1 : Shat ≤ 1) (hT : T = n ^ 7 * 2 ^ e * ⌈1 / Shat⌉) :
    n ^ 7 * 2 ^ (Real.logb 2 (1 / Shat) + e) ≤ T
      ∧ T ≤ 2 * n ^ 7 * 2 ^ (Real.logb 2 (1 / Shat) + e) := by
  sorry

/-- «Halts every execution», checkable core: if the run reaches `K` trials,
each trial consuming at least one elementary step (the named per-trial data
`S`), and the running prefix never exceeds the cap (else Step 6 returns FAIL),
then `K` itself is within the cap.  The FAIL rule «return FAIL as soon as the
count would exceed the cap» is the named mechanism; this lemma is its
arithmetic consequence — no execution passes `cap` elementary steps. -/
theorem o8_trials_le_cap {cap K : ℕ} (S : ℕ → ℕ) (h1 : ∀ i, 1 ≤ S i)
    (hcap : ∑ i ∈ Finset.range K, S i ≤ cap) :
    K ≤ cap := by
  sorry

/-- §5.8 bullet 5's «at most 2^{O(n)} draws», with the O(n) explicit: an
execution consumes `2 + n²` draws in Steps 1 and 3 (one M-subset, one
L-subset, `n²` subsets `V_j`) and `3` per trial (`F`, `P′`, `j′`); with the
trial count within the cap, the draw count is within `(n²+5)·cap`. -/
theorem o8_draws_le {n cap K : ℕ} (hcap1 : 1 ≤ cap) (hK : K ≤ cap) :
    n ^ 2 + 2 + 3 * K ≤ (n ^ 2 + 5) * cap := by
  sorry

end SubsetSumL25
