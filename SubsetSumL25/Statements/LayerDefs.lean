/-
Copyright 2026. Campaign: subset-sum sub-1/2, Base (a-kapila) combinatorial core.

Shared definitions of Base §3 («An averaged small-layer lemma»).  Primary
source: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298),
verified against the primary text (see the B1 ledger).

Verbatim (PROOF_0.4877.tex, §3):

    Let w be integer weights on a finite index set; equal weights are allowed.
    For a finite index set V and j ≥ 0, put
        Σ_j(V) = {w(T) : T ⊆ V, |T| = j},   a_j(V) = |Σ_j(V)|/C(|V|,j),
    and Σ(V) = ⋃_j Σ_j(V), d(V) = |V| − log|Σ(V)|.

`Σ(V)` and `d(V)` are `support` and `deficiency` in `Statements.Defs` (the
OpenAI-paper names, same objects).  Verbatim quotes and translation notes:
STMTS.md at the repository root.
-/
import SubsetSumL25.Statements.Defs

namespace SubsetSumL25

/-- `Σ_j(V) = {w(T) : T ⊆ V, |T| = j}` — the `j`-th layer of the subset-sum
support (Base PROOF_0.4877.tex §3). -/
def layerSupport {n : ℕ} (c : Fin n → ℤ) (V : Finset (Fin n)) (j : ℕ) : Finset ℤ :=
  (V.powersetCard j).image (subsum c)

/-- `a_j(V) = |Σ_j(V)| / C(|V|, j)` — the layer density (Base §3).  Layers with
`j > |V|` are empty, so their density is `0`; the lemmas below only use
`j ≤ |V|`, where the denominator is positive. -/
noncomputable def layerDensity {n : ℕ} (c : Fin n → ℤ) (V : Finset (Fin n)) (j : ℕ) : ℝ :=
  ((layerSupport c V j).card : ℝ) / (Nat.choose V.card j : ℝ)

end SubsetSumL25
