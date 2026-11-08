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

All five clauses are PROVED in `SubsetSumL25.Proofs.Deficiency` (moved there
from this file across M4): empty/nonneg first, then insert/superadd/exchange.
-/
import SubsetSumL25.Statements.Defs

namespace SubsetSumL25

variable {n : ℕ}

end SubsetSumL25
