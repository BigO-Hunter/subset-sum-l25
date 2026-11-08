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

`sorry`: M1 placeholder — proof target Proofs/SparseDistinctions.lean (M5).
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

/-- OpenAI L5.2: with high probability over a uniform prime P of `[2^L, 2^{L+1})`,
mod-P reduction preserves every sparse distinction. -/
theorem L5_2_sparse_distinctions (n m B : ℕ) (c : Fin n → ℤ)
    (hB : ∀ v : Fin n → ℤ, isSparse n m v → (∑ i, v i * c i) ≠ 0 →
      (((∑ i, v i * c i).natAbs : ℝ) < (2 : ℝ) ^ B))
    (c₀ : ℝ) (hc₀ : 0 < c₀) (L₀ : ℕ)
    (hcount : ∀ L, L₀ ≤ L → c₀ * (2 : ℝ) ^ L / L ≤ (primesInterval L).card)
    (hpos : ∀ L, L₀ ≤ L → 0 < (primesInterval L).card) :
    ∃ (K : ℝ) (Lstar : ℕ), 0 < K ∧ ∀ L, Lstar ≤ L →
      (badSparsePrimes n m c L).card
        ≤ K * (sparseCount n m : ℝ) * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
  sorry

end SubsetSumL25
