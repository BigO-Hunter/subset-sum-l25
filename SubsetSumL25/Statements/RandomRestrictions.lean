/-
OpenAI Lemma 2.3 («Random restrictions», setup.tex lem:half-variance).

Verbatim statement (setup.tex):

    Let V_q be a uniformly random q-element subset of [n], for 0 ≤ q ≤ n.  Then
        Var d(V_q) ≤ q.
    Moreover, 𝔼 d(V_q) is nondecreasing in q.

Translation notes (details in STMTS.md):
* `V_q` uniform over the finset of q-element subsets, modeled as the average
  (`Finset.expect`) over `uniformQSubsets n q`; nonempty for `q ≤ n`.
* variance stated in the elementary form 𝔼[(d − 𝔼d)²] ≤ q.
* `sorry`: M1 placeholder — proof target Proofs/RandomRestrictions.lean (M4).
-/
import SubsetSumL25.Statements.Defs

namespace SubsetSumL25

variable {n : ℕ}

/-- The q-element subsets of `[n]`. -/
def uniformQSubsets (n q : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun V : Finset (Fin n) => V.card = q)

/-- 𝔼 d(V_q), the average deficiency over uniform q-element subsets. -/
noncomputable def expectedDeficiency (c : Fin n → ℤ) (q : ℕ) : ℝ :=
  (uniformQSubsets n q).expect (deficiency c)

/-- OpenAI L2.3, variance bound. -/
theorem L2_3_halfVariance (c : Fin n → ℤ) (q : ℕ) (hq : q ≤ n) :
    (uniformQSubsets n q).expect
        (fun V => (deficiency c V - expectedDeficiency c q) ^ 2) ≤ (q : ℝ) := by
  sorry

/-- OpenAI L2.3, monotonicity of the mean. -/
theorem L2_3_expectation_mono (c : Fin n → ℤ) (q : ℕ) (hq : q < n) :
    expectedDeficiency c q ≤ expectedDeficiency c (q + 1) := by
  sorry

end SubsetSumL25
