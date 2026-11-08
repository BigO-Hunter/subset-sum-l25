/-
Copyright 2026. Campaign: subset-sum sub-1/2, cheap OpenAI-lemma cluster.
Shared definitions for the statements of OpenAI Lemmas 2.1, 2.2, 2.3, 2.5, 5.2
(preprint «Subset-Sum in Time O(2^0.49n)», openai/math @ adc7f124, 2026-10-04,
build/sections/setup.tex and build/sections/aliases.tex).  Verbatim quotes and
translation notes: STMTS.md at the repository root.
-/
import Mathlib

namespace SubsetSumL25

/-- `a(I) = ∑_{i∈I} a_i` — the weight of a subset (paper setup.tex: «for weights
`v_1,…,v_n` write `v(I)=∑_{i∈I} v_i`; empty sums are zero»). -/
def subsum {n : ℕ} (a : Fin n → ℤ) (I : Finset (Fin n)) : ℤ := I.sum a

/-- `Σ(V) = {c(I) : I ⊆ V}` — the subset-sum support (paper eq. (2)). -/
def support {n : ℕ} (c : Fin n → ℤ) (V : Finset (Fin n)) : Finset ℤ :=
  V.powerset.image (subsum c)

/-- `d(V) = |V| − log₂|Σ(V)|` — the deficiency (paper eq. (2)); all paper
logarithms are base 2. -/
noncomputable def deficiency {n : ℕ} (c : Fin n → ℤ) (V : Finset (Fin n)) : ℝ :=
  V.card - Real.log ((support c V).card : ℝ) / Real.log 2

/-- The primes in the half-open interval `[2^L, 2^{L+1})` (paper L2.5: «p
uniform among the primes in [2^L, 2^{L+1})»). -/
def primesInterval (L : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ L) (2 ^ (L + 1))).filter Nat.Prime

/-- `v ∈ {−1,0,1}^n` with at most `m` nonzero coordinates (paper L5.2). -/
def isSparse (n m : ℕ) (v : Fin n → ℤ) : Prop :=
  (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧
    (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ m

/-- `∑_{j≤m} C(n,j)·2^j` — the count bound on sparse sign vectors used in the
paper's proof of L5.2 («There are at most ∑_{j=0}^m C(n,j) 2^j such vectors»). -/
def sparseCount (n m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m + 1), Nat.choose n j * 2 ^ j

end SubsetSumL25
