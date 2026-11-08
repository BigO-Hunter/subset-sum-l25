/-
Base (a-kapila) Corollary D «averaged small layer» — the first consumer of the
Lemma 3.1–3.3 machinery (`Statements/Layers.lean` / `Proofs/Layers.lean`).

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` (sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298),
§3, immediately after Lemma 3.3.  Verification against the primary text is
recorded in `subset-sum-bridge/BRIDGE.md`, appendix row B2 («matches», with one
cell corrected: `S` is a uniform σ-subset of `M`; σ = m/2 only in-application).
The corollary is Base's; this file formalizes it with attribution.

Verbatim statement (PROOF_0.4877.tex §3):

    Corollary D (averaged small layer).  Let M be a finite index set with
    integer weights.  Let k, σ, v be integers with 2k ≤ σ, 2σ ≤ v + 2k,
    v ≤ |M| and C(σ,k)C(v,k) ≤ 2^v.  Let S be a uniform σ-subset and V a
    uniform v-subset of M.  Then
        E_S a_k(S) ≥ E_V 2^{−d(V)}/(v+1).

Verbatim proof (same source):

    The hypotheses give k ≤ σ ≤ v.  Fix a v-set V ⊆ M, and let S_V be a
    uniform σ-subset of V.  We show that 2^{−d(V)}/(v+1) ≤ E a_k(S_V).  Take t
    from Lemma 3.3.

    Case t ≥ k.  Lemma 3.1 gives a_t(V) ≤ E_W a_k(V∖W), where
    |V∖W| = v − t + k ≥ v/2 + k ≥ σ.  Lemma 3.2 for V∖W and s = σ gives
    a_k(V∖W) ≤ E a_k(S') for a uniform σ-subset S' of V∖W.  When W is uniform,
    S' is a uniform σ-subset of V.  Hence 2^{−d(V)}/(v+1) ≤ a_t(V) ≤ E a_k(S_V).

    Case t < k.  Then t < k ≤ v/2, so |Σ_t(V)| ≤ C(v,t) ≤ C(v,k).  Lemma 3.3
    gives 2^{v−d(V)} ≤ (v+1)C(v,k).  With the hypothesis,
    2^{−d(V)}/(v+1) ≤ C(v,k)2^{−v} ≤ 1/C(σ,k).  Every σ-set S has
    a_k(S) ≥ 1/C(σ,k), because Σ_k(S) is not empty.

    Finally average over V.  A uniform σ-subset of a uniform v-subset of M is a
    uniform σ-subset of M.

Translation notes (details in STMTS.md):
* «S uniform σ-subset of M» / «V uniform v-subset of M» are averages
  (`Finset.expect`) over `M.powersetCard σ` and `M.powersetCard v`; the Lean
  conclusion is written `E_V … ≤ E_S …` (the `≥` of the paper read right-to-left).
* **Nonemptiness (the known risk for this rung):** `Finset.expect` of an empty
  finset is `0`, so an average degenerates silently if a size hypothesis is
  dropped.  Both averaging spaces here are nonempty: `v ≤ |M|` (hypothesis)
  gives `M.powersetCard v` nonempty, `σ ≤ v` (derived) gives
  `M.powersetCard σ` nonempty, and `σ ≤ |V|` gives `V.powersetCard σ` nonempty.
  The two structural helper lemmas state their own nonemptiness hypotheses
  (`p ≤ |M|` resp. `p + q ≤ |V|`) explicitly for the same reason.
* The three `_helper` declarations below are **formalization scaffolding, not
  paper lemmas**: the paper performs these counts inline («When W is uniform,
  S' is a uniform σ-subset of V»; «A uniform σ-subset of a uniform v-subset of M
  is a uniform σ-subset of M»; «Every σ-set S has a_k(S) ≥ 1/C(σ,k)»).
* `sorry`: M1 placeholders — proof targets `Proofs/CorD.lean` (M2, M3).
-/
import SubsetSumL25.Statements.Layers

namespace SubsetSumL25

variable {n : ℕ}

/-- Base Corollary D (averaged small layer): for integers `k, σ, v` with
`2k ≤ σ`, `2σ ≤ v + 2k`, `v ≤ |M|` and `C(σ,k)C(v,k) ≤ 2^v`, averaging `a_k`
over uniform σ-subsets `S` of `M` dominates `E_V 2^{−d(V)}/(v+1)` over uniform
`v`-subsets `V` of `M`. -/
theorem Base_cor_D (c : Fin n → ℤ) (M : Finset (Fin n)) {k σ v : ℕ}
    (hk2 : 2 * k ≤ σ) (hσ2 : 2 * σ ≤ v + 2 * k) (hvM : v ≤ M.card)
    (hch : Nat.choose σ k * Nat.choose v k ≤ 2 ^ v) :
    (M.powersetCard v).expect (fun V => (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1))
      ≤ (M.powersetCard σ).expect (fun S => layerDensity c S k) := by
  sorry

/-! ### Formalization scaffolding (not paper lemmas) -/

-- `one_div_choose_le_layerDensity` (the `1/C(σ,k)` floor) is PROVED; its
-- statement-of-record lives in `Proofs/CorD.lean` (house convention: one
-- declaration per theorem).

/-- Two-level uniform sampling (containment): averaging over `p`-subsets `V` of
`M` and then over `q`-subsets `S ⊆ V` equals averaging over `q`-subsets of `M`.
(Paper: «A uniform σ-subset of a uniform v-subset of M is a uniform σ-subset of
M».) `p ≤ |M|` keeps both averaging spaces nonempty. -/
theorem expect_powersetCard_powersetCard (M : Finset (Fin n)) {p q : ℕ}
    (hp : p ≤ M.card) (hq : q ≤ p) (f : Finset (Fin n) → ℝ) :
    (M.powersetCard p).expect (fun V => (V.powersetCard q).expect f)
      = (M.powersetCard q).expect f := by
  sorry

/-- Two-level uniform sampling (disjoint): averaging over `p`-subsets `W` of `V`
and then over `q`-subsets of the complement `V∖W` equals averaging over
`q`-subsets of `V`. (Paper: «When W is uniform, S' is a uniform σ-subset of
V».) `p + q ≤ |V|` keeps every averaging space nonempty. -/
theorem expect_powersetCard_sdiff (V : Finset (Fin n)) {p q : ℕ}
    (h : p + q ≤ V.card) (f : Finset (Fin n) → ℝ) :
    (V.powersetCard p).expect (fun W => ((V \ W).powersetCard q).expect f)
      = (V.powersetCard q).expect f := by
  sorry

end SubsetSumL25
