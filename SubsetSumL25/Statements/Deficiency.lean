/-
OpenAI Lemma 2.2 («Properties of deficiency», setup.tex lem:deficiency).

Verbatim statement (setup.tex):

    For arbitrary fixed integer weights, d(∅)=0 and d(V)≥0.  For i∉V,
        0 ≤ d(V∪{i}) − d(V) ≤ 1.
    For disjoint U,V⊆[n],
        d(U∪V) ≥ d(U)+d(V).
    If V,V′ have equal size and differ by exchanging one index, then
        |d(V)−d(V′)| ≤ 1.

with Σ(V)={c(I):I⊆V} and d(V)=|V|−log|Σ(V)| (eq. (2), base-2 log).

The two foundational clauses (d(∅)=0, d(V)≥0) are PROVED in
`SubsetSumL25.Proofs.Deficiency` (moved there from this file at M4); the
remaining three clauses (insert bounds, superadditivity, exchange) stay
`sorry` here — M4's remaining work.
-/
import SubsetSumL25.Statements.Defs

namespace SubsetSumL25

variable {n : ℕ}

theorem L2_2_deficiency_insert (c : Fin n → ℤ) (V : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ V) :
    0 ≤ deficiency c (insert i V) - deficiency c V ∧
      deficiency c (insert i V) - deficiency c V ≤ 1 := by
  sorry

theorem L2_2_deficiency_superadd (c : Fin n → ℤ) {U V : Finset (Fin n)}
    (hUV : Disjoint U V) :
    deficiency c (U ∪ V) ≥ deficiency c U + deficiency c V := by
  sorry

theorem L2_2_deficiency_exchange (c : Fin n → ℤ) (U : Finset (Fin n))
    (i j : Fin n) (hi : i ∉ U) (hj : j ∉ U) (hij : i ≠ j) :
    |deficiency c (insert i U) - deficiency c (insert j U)| ≤ 1 := by
  sorry

end SubsetSumL25
