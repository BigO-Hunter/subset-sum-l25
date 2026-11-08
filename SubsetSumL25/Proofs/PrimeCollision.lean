/-
M2: PROOF of OpenAI Lemma 2.5 (random-prime collisions).

Paper proof (setup.tex): «The prime number theorem gives at least c₀·2^L/L
primes in the specified interval …  The nonzero integer D has fewer than B
distinct prime divisors, since their product is at most |D| and each is at
least 2.  Dividing this count by the number of available primes proves the
claim.  For two unequal integers, apply it to their difference.»

Split here as:
* the PNT interval-count premise stays the theorem hypothesis `hcount`
  (STMTS.md note 1: Mathlib d13f23b has no PNT; Chebyshev-grade bounds
  annihilate in the interval difference);
* the number-theory half is fully proved: `primeFactors_card_lt`
  (distinct prime divisors < B), `badPrimes_le_card`, `badPrimes_le`;
* the «absolute constants» are explicit: `K = 1/c₀`, `L* = L₀`.
-/
import Mathlib
import SubsetSumL25.Statements.PrimeCollision

namespace SubsetSumL25

/-- A natural number `n < 2^B` (with `B ≥ 1`) has fewer than `B` distinct prime
divisors: their product is at most `n` and each factor is at least 2. -/
theorem primeFactors_card_lt {n B : ℕ} (hB : 1 ≤ B) (hn : (n : ℝ) < (2 : ℝ) ^ B) :
    n.primeFactors.card < B := by
  rcases eq_or_ne n 0 with rfl | h0
  · simp; omega
  have hsup : ∀ q ∈ n.primeFactors, 1 ≤ n.factorization q := by
    intro q hq
    exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hq) h0
      ((Nat.mem_primeFactors.mp hq).right.left)
  have hcard : n.primeFactors.card ≤ ∑ q ∈ n.primeFactors, n.factorization q := by
    have h1 : (∑ q ∈ n.primeFactors, (1 : ℕ))
        ≤ ∑ q ∈ n.primeFactors, n.factorization q :=
      Finset.sum_le_sum fun q hq => hsup q hq
    simpa using h1
  have h2le : (2 : ℕ) ^ n.primeFactors.card ≤ n := by
    have h1 : (2 : ℕ) ^ n.primeFactors.card
        ≤ (2 : ℕ) ^ ∑ q ∈ n.primeFactors, n.factorization q :=
      Nat.pow_le_pow_right (by norm_num) hcard
    rw [← Finset.prod_pow_eq_pow_sum n.primeFactors (fun q => n.factorization q) 2] at h1
    calc (2 : ℕ) ^ n.primeFactors.card
        ≤ ∏ q ∈ n.primeFactors, 2 ^ n.factorization q := h1
      _ ≤ ∏ q ∈ n.primeFactors, q ^ n.factorization q :=
          Finset.prod_le_prod fun q hq =>
            Nat.pow_le_pow_left (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hq)) _
      _ = n := (Nat.prod_primeFactors_pow_factorization h0).symm
  have hnn : n < (2 : ℕ) ^ B := by exact_mod_cast hn
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h2le hnn)

/-- The interval primes dividing `|D|` are among the distinct prime divisors
of `|D|`. -/
theorem badPrimes_le_card (L : ℕ) (D : ℤ) (hD : D ≠ 0) :
    badPrimes L D ≤ D.natAbs.primeFactors.card := by
  have hsub : (primesInterval L).filter (fun p => p ∣ D.natAbs)
      ⊆ D.natAbs.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp1, hdvd⟩ := hp
    have hD' : D.natAbs ≠ 0 := by
      intro hc
      apply hD
      rw [← Int.natAbs_eq_zero]
      exact hc
    exact (Nat.mem_primeFactors).mpr ⟨(Finset.mem_filter.mp hp1).2, hdvd, hD'⟩
  calc badPrimes L D = ((primesInterval L).filter (fun p => p ∣ D.natAbs)).card := rfl
    _ ≤ D.natAbs.primeFactors.card := Finset.card_le_card hsub

/-- The paper's divisor-count bound: a nonzero `D` with `|D| < 2^B`, `B ≥ 1`,
is divisible by at most `B` of the interval primes. -/
theorem badPrimes_le (L : ℕ) (D : ℤ) (hD : D ≠ 0) (B : ℕ) (hB : 1 ≤ B)
    (habs : ((D.natAbs : ℝ) < (2 : ℝ) ^ B)) :
    (badPrimes L D : ℝ) ≤ (B : ℝ) :=
  Nat.cast_le.mpr
    (le_of_lt (lt_of_le_of_lt (badPrimes_le_card L D hD) (primeFactors_card_lt hB habs)))

/-- `primesInterval 0` is empty: the interval is `[1, 2) = {1}`, not prime. -/
private theorem primesInterval_zero_card : (primesInterval 0).card = 0 := by
  unfold primesInterval
  have hIco : (Finset.Ico 1 2 : Finset ℕ) = {1} := by decide
  simp only [pow_zero, Nat.zero_add, pow_one, hIco]
  simp [Nat.not_prime_one]

/-- OpenAI L2.5: random-prime collision bound, with explicit `K = 1/c₀`,
`L* = L₀`. -/
theorem L2_5_prime_collision (c₀ : ℝ) (hc₀ : 0 < c₀) (L₀ : ℕ)
    (hcount : ∀ L, L₀ ≤ L → c₀ * (2 : ℝ) ^ L / L ≤ (primesInterval L).card)
    (hpos : ∀ L, L₀ ≤ L → 0 < (primesInterval L).card) :
    ∃ (K : ℝ) (Lstar : ℕ), 0 < K ∧ ∀ L, Lstar ≤ L → ∀ (D : ℤ) (B : ℕ),
      D ≠ 0 → 1 ≤ B → ((D.natAbs : ℝ) < (2 : ℝ) ^ B) →
      (badPrimes L D : ℝ) / (primesInterval L).card
        ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
  refine ⟨1 / c₀, L₀, by positivity, ?_⟩
  intro L hL D B hD hB habs
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · exact absurd (hpos 0 hL) (by rw [primesInterval_zero_card]; norm_num)
  have hTpos : (0 : ℝ) < ((primesInterval L).card : ℝ) := by
    exact_mod_cast hpos L hL
  have hcnt : c₀ * (2 : ℝ) ^ L / L ≤ ((primesInterval L).card : ℝ) := hcount L hL
  have hstep : (B : ℝ) / ((primesInterval L).card : ℝ)
      ≤ (B : ℝ) * (L : ℝ) / (c₀ * (2 : ℝ) ^ L) := by
    rw [div_le_div_iff₀ hTpos (by positivity)]
    have h1 : c₀ * (2 : ℝ) ^ L ≤ (L : ℝ) * ((primesInterval L).card : ℝ) := by
      have h' : c₀ * (2 : ℝ) ^ L / (L : ℝ) * (L : ℝ)
          ≤ ((primesInterval L).card : ℝ) * (L : ℝ) :=
        mul_le_mul_of_nonneg_right hcnt (by positivity)
      rw [div_mul_cancel₀ _ (by positivity)] at h'
      exact h'.trans (le_of_eq (mul_comm _ _))
    have h2 : (B : ℝ) * (L : ℝ) * ((primesInterval L).card : ℝ)
        = (B : ℝ) * ((L : ℝ) * ((primesInterval L).card : ℝ)) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg' B)
  calc (badPrimes L D : ℝ) / (primesInterval L).card
      ≤ (B : ℝ) / (primesInterval L).card :=
        (div_le_div_iff_of_pos_right hTpos).2 (badPrimes_le L D hD B hB habs)
    _ ≤ (B : ℝ) * (L : ℝ) / (c₀ * (2 : ℝ) ^ L) := hstep
    _ = 1 / c₀ * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by field_simp

/-- OpenAI L2.5, last sentence: the two-integer collision variant — apply the
lemma to the difference. -/
theorem L2_5_prime_collision_two (c₀ : ℝ) (hc₀ : 0 < c₀) (L₀ : ℕ)
    (hcount : ∀ L, L₀ ≤ L → c₀ * (2 : ℝ) ^ L / L ≤ (primesInterval L).card)
    (hpos : ∀ L, L₀ ≤ L → 0 < (primesInterval L).card) :
    ∃ (K : ℝ) (Lstar : ℕ), 0 < K ∧ ∀ L, Lstar ≤ L → ∀ (x y : ℤ) (B : ℕ),
      x ≠ y → 1 ≤ B → ((x - y).natAbs : ℝ) < (2 : ℝ) ^ B →
      (badPrimes L (x - y) : ℝ) / (primesInterval L).card
        ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
  obtain ⟨K, Lstar, hK, hmain⟩ := L2_5_prime_collision c₀ hc₀ L₀ hcount hpos
  exact ⟨K, Lstar, hK, fun L hL x y B hxy hB habs =>
    hmain L hL (x - y) B (sub_ne_zero_of_ne hxy) hB habs⟩

end SubsetSumL25
