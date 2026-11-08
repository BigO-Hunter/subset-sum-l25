/-
OpenAI Lemma 5.2 («Sparse distinctions», aliases.tex lem:sparse-distinction).

Verbatim statement (aliases.tex):

    With probability 1−o(1) over P, the following implication holds
    simultaneously for every v∈{−1,0,1}^n with at most m nonzero coordinates:
        ∑ᵢ vᵢcᵢ ≠ 0  ⟹  ∑ᵢ vᵢcᵢ ≢ 0 (mod P).                              (14)
    The error is uniform under (16) [`eq:bit-guard`].

Translation of «probability 1−o(1)» (details in STMTS.md): the paper's proof is
a union bound of L2.5 over the ≤ ∑_{j≤m} C(n,j)·2^j sparse sign vectors, each
carrying O(b+log n) bits, so the failure probability is bounded by
`K · sparseCount n m · B · L · 2^{−L}` whenever every sparse nonzero signed sum
has absolute value < 2^B (hypothesis `hB`, the paper's «Every nonzero integer
∑ᵢ vᵢcᵢ has O(b+log n) bits»).  The `o(1)` is the external ratio
`K·S(n,m)·B·L/2^L → 0` under the bit-guard, outside the lemma.  Same PNT
premise (`hcount`) and well-formedness (`hpos`) as L2.5.

M5b statement fix (STMTS.md note 7): the paper (and STMTS.md note 6) bound the
failure PROBABILITY — the bad-prime count divided by `#(primesInterval L)`;
the M1 statement had dropped that division, which would make the claim
degenerate (a count bound only holds past `L ≥ B`, vacuously).  The theorem now
carries the division and is PROVED in
`SubsetSumL25.Proofs.SparseDistinctions`; it moved here at M5b, as L2.5 did at
M2.
-/
import SubsetSumL25.Statements.Defs
import SubsetSumL25.Statements.PrimeCollision

namespace SubsetSumL25

open scoped Classical in
/-- The primes of `[2^L, 2^{L+1})` at which some sparse signed sum is a nonzero
multiple — the failure event of L5.2.  Classical decidability: the predicate
quantifies over the (infinite) type `Fin n → ℤ`. -/
noncomputable def badSparsePrimes (n m : ℕ) (c : Fin n → ℤ) (L : ℕ) : Finset ℕ :=
  (primesInterval L).filter (fun P =>
    ∃ v : Fin n → ℤ, isSparse n m v ∧
      (∑ i, v i * c i) ≠ 0 ∧ ((P : ℤ) ∣ ∑ i, v i * c i))

/-
`L5_2_sparse_distinctions` is PROVED in `SubsetSumL25.Proofs.SparseDistinctions`
(M5b); it lived here with a `sorry` placeholder at M1 and moved to Proofs/ at
M5b together with the probability-division fix described above.
-/

end SubsetSumL25
