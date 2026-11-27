/-
Base (a-kapila) Lemmas 3.1–3.3 — the combinatorial core of the averaged
small-layer argument (PROOF_0.4877.tex §3).

Primary source: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298);
statement-by-statement verification against the primary text is recorded in the B1 ledger («Base primary-source verification»).  The lemmas are Base's; this file formalizes them with attribution.

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
* M1 carried `sorry` placeholders; M2/M3 replaced them, so every lemma below is
  now PROVED in `Proofs/Layers.lean` (statement-of-record) — see PROGRESS.md.
-/
import SubsetSumL25.Statements.LayerDefs

namespace SubsetSumL25

variable {n : ℕ}

-- L3.1 (covering) is PROVED; statement-of-record lives in `Proofs/Layers.lean`
-- (house convention: one declaration per theorem).

-- L3.2 (sampling) and L3.3 (a good layer) are PROVED; statements-of-record
-- live in `Proofs/Layers.lean` (house convention: one declaration per theorem).

end SubsetSumL25
