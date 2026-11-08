/-
M3 (partial): PROOF of OpenAI Lemma 2.1 «Isolation», first sentence — the
deterministic equivalence holds for every choice of the tie weights.

Paper proof (setup.tex): «The identity c(I)=t_s gives C(a(I)−t)=s−u(I).  Since
s,u(I)∈[0,nN₀] and C>nN₀, this forces a(I)=t and u(I)=s.»

The probabilistic half (probability ≥ 11/12, MVV minimum-tie argument) remains
`sorry` (`L2_1_isolation_prob` in Statements/) — that is M3's remaining work.
-/
import Mathlib
import SubsetSumL25.Statements.Isolation

namespace SubsetSumL25

private theorem eq_zero_of_dvd_of_abs_lt {k m : ℤ} (hk : 0 < k) (hdvd : k ∣ m)
    (hlo : -k < m) (hhi : m < k) : m = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  by_contra hne
  have hq0 : q ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hq
    exact hne hq
  rcases Int.lt_trichotomy 0 q with hqpos | hqzero | hqneg
  · have hkq : k ≤ k * q := by
      calc k = k * 1 := (mul_one k).symm
        _ ≤ k * q := Int.mul_le_mul_of_nonneg_left hqpos hk.le
    exact absurd (show m < m by linarith [hq, hkq, hhi]) (by linarith)
  · exact hq0 hqzero.symm
  · have hqle : q ≤ -1 := by linarith
    have hkq : k * q ≤ -k := by
      calc k * q ≤ k * (-1) := Int.mul_le_mul_of_nonneg_left hqle hk.le
        _ = -k := by ring
    exact absurd (show m < m by linarith [hq, hkq, hlo]) (by linarith)

/-- The sum of tie weights of a subset is at most `n·N₀`. -/
private theorem sum_u_le {n N₀ : ℕ} (u : Fin n → Fin N₀) (I : Finset (Fin n)) :
    (∑ i ∈ I, (u i : ℕ)) ≤ n * N₀ := by
  calc ∑ i ∈ I, (u i : ℕ)
      ≤ I.card • (N₀ - 1) :=
        Finset.sum_le_card_nsmul I (fun i => (u i : ℕ)) (N₀ - 1)
          (fun i _ => Nat.le_sub_one_of_lt (Fin.is_lt (u i)))
    _ = I.card * (N₀ - 1) := rfl
    _ ≤ I.card * N₀ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ n * N₀ := by
        have h1 : I.card ≤ n := by simpa using I.card_le_univ
        exact Nat.mul_le_mul_right _ h1

/-- The decomposition of a transformed sum: `c(I) = C·a(I) + u(I)`. -/
private theorem subsum_transformed {n N₀ : ℕ} (a : Fin n → ℤ)
    (u : Fin n → Fin N₀) (I : Finset (Fin n)) :
    subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) I
      = transformedC n N₀ * subsum a I
        + ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
  unfold subsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- OpenAI L2.1, first sentence: the transformed equivalence. -/
theorem L2_1_isolation (a : Fin n → ℤ) (t : ℤ) (N₀ : ℕ)
    (u : Fin n → Fin N₀) :
    ((∃ I : Finset (Fin n), subsum a I = t) ↔
      (∃ s : ℕ, s ≤ n * N₀ ∧ ∃ I : Finset (Fin n),
        subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) I
          = transformedC n N₀ * t + s)) := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨(∑ i ∈ I, (u i : ℕ)), sum_u_le u I, I, by
      rw [subsum_transformed, hI, Nat.cast_sum]⟩
  · rintro ⟨s, hs, I, hI⟩
    rw [subsum_transformed] at hI
    have hCpos : (0 : ℤ) < transformedC n N₀ := by unfold transformedC; positivity
    have hCnN₀ : (n * N₀ : ℤ) < transformedC n N₀ := by
      unfold transformedC
      have : (0 : ℤ) ≤ n * N₀ := by positivity
      linarith
    have hsumle : (∑ i ∈ I, ((u i : ℕ) : ℤ)) ≤ (n * N₀ : ℤ) :=
      mod_cast sum_u_le u I
    have hsle : ((s : ℤ)) ≤ (n * N₀ : ℤ) := by exact_mod_cast hs
    have hkey : transformedC n N₀ * (subsum a I - t)
        = (s : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) := by linarith
    have hdvd : transformedC n N₀ ∣ ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) :=
      Dvd.intro (subsum a I - t) hkey
    have hlo : -(transformedC n N₀) < ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
      have h2 : (0 : ℤ) ≤ ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_nonneg _
      linarith
    have hhi : ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) < transformedC n N₀ := by
      have h2 : (0 : ℤ) ≤ ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_nonneg _
      linarith
    have hm0 : ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) = 0 :=
      eq_zero_of_dvd_of_abs_lt hCpos hdvd hlo hhi
    have hzero : subsum a I - t = 0 := by
      rw [hm0] at hkey
      rcases mul_eq_zero.mp hkey with hC0 | hx0
      · exact absurd hC0 (by linarith)
      · exact hx0
    exact ⟨I, by linarith⟩

end SubsetSumL25
