/-
M5b: PROOF of OpenAI Lemma 5.2 (sparse distinctions), derived from the proved
L2.5 (PrimeCollision.lean) by the paper's §5 union bound.

Paper proof (setup.tex/aliases.tex via STMTS.md): «There are at most
∑_{j=0}^m C(n,j) 2^j such vectors» and «Every nonzero integer ∑ᵢ vᵢcᵢ has
O(b+log n) bits» (hypothesis `hB`), so a union bound of L2.5 over the sparse
sign vectors bounds the failure probability by S(n,m)·K·B·L·2^{−L}.

Design note (option (b), executed concretely):
`Fin n → ℤ` is infinite, so there is no `Finset.univ` of sparse vectors; the
candidate set is built explicitly as `sparseAll n m` from the finite encoding
(support `I ⊆ Fin n` with `I.card ≤ m`, sign pattern `↥I → Bool` — the paper's
own counting scheme).  Then:
* `sparseAll_card_le` — the paper's counting: #candidate ≤ ∑_{j≤m} C(n,j)·2^j
  (union by support size: `powersetCard` gives C(n,j) supports of size j,
  `Bool^j` gives the 2^j sign patterns);
* the union bound — the bad primes are covered by ⋃_{d ≠ 0 sparse sum}
  {interval primes dividing d}, each d nonzero with |d| < 2^B by `hB`, so
  L2.5's per-integer ratio K·B·L·2^{−L} (K = 1/c₀, L* = L₀ as in L2.5) sums
  to ≤ sparseCount · K·B·L·2^{−L}.
-/
import Mathlib
import SubsetSumL25.Statements.SparseDistinctions
import SubsetSumL25.Proofs.PrimeCollision

namespace SubsetSumL25

/-- Reconstruct a sign vector from a support and a sign pattern
(`true ↦ +1`, `false ↦ −1`, `0` off the support). -/
private def decode (n : ℕ) (I : Finset (Fin n)) (b : ↥I → Bool) : Fin n → ℤ :=
  fun i => if h : i ∈ I then (if b ⟨i, h⟩ then 1 else -1) else 0

private lemma decode_support {n : ℕ} {I : Finset (Fin n)} (b : ↥I → Bool) :
    ∀ i, decode n I b i ≠ 0 → i ∈ I := by
  intro i hi
  by_contra h
  apply hi
  unfold decode
  exact dite_eq_right h

private lemma decode_tri {n : ℕ} {I : Finset (Fin n)} (b : ↥I → Bool) (i : Fin n) :
    decode n I b i = -1 ∨ decode n I b i = 0 ∨ decode n I b i = 1 := by
  by_cases h : i ∈ I
  · unfold decode
    rw [dite_eq_left h]
    by_cases hb : b ⟨i, h⟩
    · right; right; simp [hb]
    · left; simp [hb]
  · right; left
    unfold decode
    exact dite_eq_right h

private lemma decode_sparse {n m : ℕ} {I : Finset (Fin n)} (hI : I.card ≤ m) (b : ↥I → Bool) :
    isSparse n m (decode n I b) := by
  refine ⟨decode_tri b, ?_⟩
  refine le_trans (Finset.card_le_card ?_) hI
  intro i hi
  exact decode_support b i (Finset.mem_filter.mp hi).2

/-- The finite set of all sparse sign vectors `v ∈ {−1,0,1}^n` with ≤ m
nonzeros, built from the encoding (support, sign pattern) — the paper's
candidate set for the union bound. -/
private def sparseAll (n m : ℕ) : Finset (Fin n → ℤ) :=
  (Finset.univ.filter (fun I : Finset (Fin n) => I.card ≤ m)).biUnion
    (fun I => (Finset.univ : Finset (↥I → Bool)).image (decode n I))

private lemma mem_sparseAll {n m : ℕ} {v : Fin n → ℤ} (hv : isSparse n m v) :
    v ∈ sparseAll n m := by
  obtain ⟨htri, hcard⟩ := hv
  simp only [sparseAll]
  refine Finset.mem_biUnion.mpr ⟨Finset.univ.filter (fun i => v i ≠ 0),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩, ?_⟩
  refine Finset.mem_image.mpr ⟨(fun x : ↥(Finset.univ.filter (fun i => v i ≠ 0)) =>
    decide (v x.val = 1)), Finset.mem_univ _, ?_⟩
  funext i
  by_cases h : i ∈ Finset.univ.filter (fun i => v i ≠ 0)
  · rcases htri i with hneg | hzero | hipos
    · simp [decode, h, hneg]
    · exact absurd hzero (Finset.mem_filter.mp h).2
    · simp [decode, h, hipos]
  · have h0 : v i = 0 := by
      by_contra hc
      exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
    simp [decode, h, h0]

private lemma sparseAll_isSparse {n m : ℕ} {v : Fin n → ℤ} (hv : v ∈ sparseAll n m) :
    isSparse n m v := by
  simp only [sparseAll, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and] at hv
  obtain ⟨I, hI, hmem⟩ := hv
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
  obtain ⟨b, rfl⟩ := hmem
  exact decode_sparse hI b

open scoped Classical in
/-- The paper's count bound for L5.2: at most `∑_{j≤m} C(n,j)·2^j` sparse sign
vectors `v ∈ {−1,0,1}^n` with ≤ m nonzeros.  Counted support-size by
support-size through the injective encoding `v ↦ (support, sign pattern)`. -/
private lemma sparseAll_card_le (n m : ℕ) : (sparseAll n m).card ≤ sparseCount n m := by
  classical
  calc (sparseAll n m).card
      ≤ ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin n) => I.card ≤ m),
          ((Finset.univ : Finset (↥I → Bool)).image (decode n I)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin n) => I.card ≤ m), (2 : ℕ) ^ I.card := by
        refine Finset.sum_le_sum fun I _ => ?_
        calc (((Finset.univ : Finset (↥I → Bool)).image (decode n I)).card : ℕ)
            ≤ (Finset.univ : Finset (↥I → Bool)).card := Finset.card_image_le
          _ = 2 ^ I.card := by
              rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
                Fintype.card_coe, Fintype.card_bool]
    _ = ∑ j ∈ Finset.range (m + 1), Nat.choose n j * 2 ^ j := by
        have hsplit : ∀ I ∈ Finset.univ.filter (fun I : Finset (Fin n) => I.card ≤ m),
            (2 : ℕ) ^ I.card =
              ∑ j ∈ Finset.range (m + 1), (if I.card = j then 2 ^ j else 0) := by
          intro I hI
          rw [Finset.sum_ite_eq (Finset.range (m + 1)) I.card (fun j => (2 : ℕ) ^ j)]
          simp only [Finset.mem_range]
          rw [ite_eq_left (Nat.lt_succ_of_le (Finset.mem_filter.mp hI).2)]
        rw [Finset.sum_congr rfl hsplit, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hFeq : (Finset.univ.filter (fun I : Finset (Fin n) => I.card ≤ m)).filter
            (fun I : Finset (Fin n) => I.card = j) = Finset.univ.powersetCard j := by
          refine Finset.ext fun I => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
            Finset.subset_univ]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨h ▸ hjm, h⟩
        rw [← Finset.sum_filter, hFeq, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin, Nat.cast_id]
    _ = sparseCount n m := rfl

/-- OpenAI L5.2: with failure probability ≤ `K·sparseCount n m·B·L·2^{−L}` over a
uniform prime P of `[2^L, 2^{L+1})`, mod-P reduction preserves every sparse
distinction.  K = 1/c₀, L* = max(L₀, 1), explicit as in L2.5. -/
theorem L5_2_sparse_distinctions (n m B : ℕ) (c : Fin n → ℤ)
    (hB : ∀ v : Fin n → ℤ, isSparse n m v → (∑ i, v i * c i) ≠ 0 →
      (((∑ i, v i * c i).natAbs : ℝ) < (2 : ℝ) ^ B))
    (c₀ : ℝ) (hc₀ : 0 < c₀) (L₀ : ℕ)
    (hcount : ∀ L, L₀ ≤ L → c₀ * (2 : ℝ) ^ L / L ≤ (primesInterval L).card)
    (hpos : ∀ L, L₀ ≤ L → 0 < (primesInterval L).card) :
    ∃ (K : ℝ) (Lstar : ℕ), 0 < K ∧ ∀ L, Lstar ≤ L →
      ((badSparsePrimes n m c L).card : ℝ) / (primesInterval L).card
        ≤ K * (sparseCount n m : ℝ) * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
  classical
  rcases Nat.eq_zero_or_pos B with rfl | hB1
  · -- B = 0: every nonzero sparse sum carries ≥ 1 bit, so `hB` leaves no bad prime.
    refine ⟨1, 0, one_pos, fun L _ => ?_⟩
    have hnotmem : ∀ P : ℕ, P ∉ badSparsePrimes n m c L := by
      intro P hP
      simp only [badSparsePrimes, Finset.mem_filter] at hP
      obtain ⟨_, v, hv1, hv2, _⟩ := hP
      have h1 : (1 : ℝ) ≤ ((∑ i, v i * c i).natAbs : ℝ) :=
        by exact_mod_cast Nat.succ_le_of_lt ((Int.natAbs_pos).mpr hv2)
      have h2 := hB v hv1 hv2
      simp only [pow_zero] at h2
      linarith
    rw [Finset.card_eq_zero.mpr ((Finset.eq_empty_iff_forall_notMem).mpr hnotmem)]
    simp
  · obtain ⟨K, Lstar, hK, hmain⟩ := L2_5_prime_collision c₀ hc₀ L₀ hcount hpos
    refine ⟨K, max Lstar L₀, hK, fun L hL => ?_⟩
    have hLstar : Lstar ≤ L := le_trans (Nat.le_max_left Lstar L₀) hL
    have hL0 : L₀ ≤ L := le_trans (Nat.le_max_right Lstar L₀) hL
    -- the set of all nonzero sums of sparse vectors (a Finset of integers)
    set D : Finset ℤ :=
      ((sparseAll n m).image (fun v => ∑ i, v i * c i)).filter (fun d => d ≠ 0) with hDdef
    -- the failure set is covered by the per-sum divisor sets
    have hsub : badSparsePrimes n m c L ⊆ D.biUnion
        (fun d => (primesInterval L).filter (fun p => p ∣ d.natAbs)) := by
      intro P hP
      simp only [badSparsePrimes, Finset.mem_filter] at hP
      obtain ⟨hPint, v, hv1, hv2, hv3⟩ := hP
      have hdv : (∑ i, v i * c i) ∈ D :=
        Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, mem_sparseAll hv1, rfl⟩, hv2⟩
      refine Finset.mem_biUnion.mpr ⟨_, hdv, Finset.mem_filter.mpr ⟨hPint, ?_⟩⟩
      obtain ⟨k, hk⟩ := hv3
      exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul, Int.natAbs_natCast]⟩
    have hTpos : (0 : ℝ) < ((primesInterval L).card : ℝ) := by exact_mod_cast hpos L hL0
    have h1 : ((badSparsePrimes n m c L).card : ℝ)
        ≤ ((D.biUnion (fun d => (primesInterval L).filter (fun p => p ∣ d.natAbs))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((D.biUnion (fun d => (primesInterval L).filter (fun p => p ∣ d.natAbs))).card : ℝ)
        ≤ ∑ d ∈ D, (((primesInterval L).filter (fun p => p ∣ d.natAbs)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hcardreal : ((badSparsePrimes n m c L).card : ℝ)
        ≤ ∑ d ∈ D, (((primesInterval L).filter (fun p => p ∣ d.natAbs)).card : ℝ) :=
      le_trans h1 h2
    -- L2.5 applied to each nonzero sum, divided by the interval size
    have hstep : ((badSparsePrimes n m c L).card : ℝ) / ((primesInterval L).card : ℝ)
        ≤ ∑ d ∈ D, (((primesInterval L).filter (fun p => p ∣ d.natAbs)).card : ℝ)
            / ((primesInterval L).card : ℝ) := by
      rw [← Finset.sum_div]
      exact (div_le_div_iff_of_pos_right hTpos).mpr hcardreal
    have hper : ∀ d ∈ D, (((primesInterval L).filter (fun p => p ∣ d.natAbs)).card : ℝ)
        / ((primesInterval L).card : ℝ) ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
      intro d hd
      obtain ⟨hDmem, hDne⟩ := Finset.mem_filter.mp hd
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hDmem
      exact hmain L hLstar _ B hDne hB1 (hB v (sparseAll_isSparse hv) hDne)
    -- the number of distinct nonzero sums is at most the number of sparse vectors
    have hDle : D.card ≤ sparseCount n m := by
      refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
      refine le_trans Finset.card_image_le ?_
      exact sparseAll_card_le n m
    have hX : (0 : ℝ) ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L :=
      div_nonneg (mul_nonneg (mul_nonneg hK.le (Nat.cast_nonneg' B)) (Nat.cast_nonneg' L))
        (pow_pos (by positivity) L).le
    calc ((badSparsePrimes n m c L).card : ℝ) / ((primesInterval L).card : ℝ)
        ≤ ∑ d ∈ D, K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by
          refine le_trans hstep ?_
          exact Finset.sum_le_sum fun d hd => hper d hd
      _ = (D.card : ℝ) * (K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (sparseCount n m : ℝ) * (K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hDle) hX
      _ = K * (sparseCount n m : ℝ) * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L := by ring

end SubsetSumL25
