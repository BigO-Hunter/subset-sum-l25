/-
Base (a-kapila) Lemmas 3.1–3.3 — the combinatorial core of the averaged
small-layer argument (PROOF_0.4877.tex §3).

Primary source: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298);
statement-by-statement verification against the primary text is recorded in
`subset-sum-bridge/BRIDGE.md`, appendix «Base primary-source verification»
(rows B1).  The lemmas are Base's; this file formalizes them with attribution.

Verbatim statements (PROOF_0.4877.tex §3):

    Lemma 3.1 (covering).  Let 0 ≤ k ≤ t ≤ |V|, and let W be a uniform
    (t−k)-subset of V.  Then
        a_t(V) ≤ E_W a_k(V∖W).

    Lemma 3.2 (sampling).  Let k ≤ s ≤ |V|, and let S be a uniform s-subset of
    V.  Then
        E_S a_k(S) ≥ a_k(V).

    Lemma 3.3 (a good layer).  Some t with 2t ≤ |V| has
        |Σ(V)| ≤ (|V|+1) |Σ_t(V)|.
    In particular
        a_t(V) ≥ 2^{−d(V)}/(|V|+1).

Translation notes (details in STMTS.md):
* «W a uniform (t−k)-subset of V» is modeled as the average (`Finset.expect`)
  over the finset `V.powersetCard (t−k)` of all `(t−k)`-element subsets of `V`
  — the same house convention as `uniformQSubsets` for OpenAI L2.3.
* `|V∖W|` is Mathlib `V \ W`; the paper's sizes are recovered as
  `(V \ W).card = |V| − t + k` from `W ⊆ V`, `|W| = t − k`.
* The «in particular» clause is a separate declaration
  (`L3_3_good_layer_density`) so that each half can be proved independently.
* `sorry`: M1 placeholders — proof targets `Proofs/Layers.lean` (M2, M3).
-/
import SubsetSumL25.Statements.LayerDefs

namespace SubsetSumL25

variable {n : ℕ}

/-- Base Lemma 3.1 (covering): for `0 ≤ k ≤ t ≤ |V|` and a uniform
`(t−k)`-subset `W` of `V`, one has `a_t(V) ≤ E_W a_k(V∖W)`. -/
theorem L3_1_covering (c : Fin n → ℤ) {V : Finset (Fin n)} {k t : ℕ}
    (hkt : k ≤ t) (ht : t ≤ V.card) :
    layerDensity c V t ≤
      (V.powersetCard (t - k)).expect (fun W => layerDensity c (V \ W) k) := by
  sorry

/-- Base Lemma 3.2 (sampling): for `k ≤ s ≤ |V|` and a uniform `s`-subset `S`
of `V`, one has `E_S a_k(S) ≥ a_k(V)`. -/
theorem L3_2_sampling (c : Fin n → ℤ) {V : Finset (Fin n)} {k s : ℕ}
    (hks : k ≤ s) (hsv : s ≤ V.card) :
    layerDensity c V k ≤
      (V.powersetCard s).expect (fun S => layerDensity c S k) := by
  sorry

/-- Base Lemma 3.3 (a good layer), existence half: some layer index `t` with
`2t ≤ |V|` carries at least a `1/(|V|+1)` fraction of the whole support,
`|Σ(V)| ≤ (|V|+1) |Σ_t(V)|`. -/
theorem L3_3_good_layer (c : Fin n → ℤ) (V : Finset (Fin n)) :
    ∃ t, 2 * t ≤ V.card ∧
      (support c V).card ≤ (V.card + 1) * (layerSupport c V t).card := by
  sorry

/-- Base Lemma 3.3 (a good layer), density half («in particular»):
some `t` with `2t ≤ |V|` has `a_t(V) ≥ 2^{−d(V)}/(|V|+1)`. -/
theorem L3_3_good_layer_density (c : Fin n → ℤ) (V : Finset (Fin n)) :
    ∃ t, 2 * t ≤ V.card ∧
      (2 : ℝ) ^ (-(deficiency c V)) / ((V.card : ℝ) + 1) ≤ layerDensity c V t := by
  sorry

end SubsetSumL25
