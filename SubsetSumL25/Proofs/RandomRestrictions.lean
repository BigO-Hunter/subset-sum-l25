/-
M4c: OpenAI Lemma 2.3 — monotone step. STATUS: clean build.
card_uniformQSubsets + sum_eq_sum_ite_univ + erase_sum_le + hbij +
sum_erase_bij + L2_3_expectation_mono all PROVED (no sorries).
-/
import Mathlib
import SubsetSumL25.Statements.RandomRestrictions
import SubsetSumL25.Proofs.Deficiency

namespace SubsetSumL25

/-- The number of `k`-subsets of `[n]` is `C(n,k)`. -/
theorem card_uniformQSubsets (n k : ℕ) :
    (uniformQSubsets n k).card = Nat.choose n k := by
  have h1 : uniformQSubsets n k = Finset.univ.powersetCard k := by
    unfold uniformQSubsets
    rw [Finset.powersetCard_eq_filter]
    simp
  rw [h1, Finset.card_powersetCard]
  simp

/-- Restricting a finite sum to the index set itself: the indicator form. -/
private theorem sum_eq_sum_ite_univ {α : Type*} [DecidableEq α] [Fintype α] (W : Finset α)
    (f : α → ℝ) : (∑ i ∈ W, f i) = ∑ i ∈ Finset.univ, if i ∈ W then f i else 0 := by
  classical
  rw [← Finset.sum_filter (p := fun i => i ∈ W) (f := f)]
  congr 1
  ext i
  simp

/-- (A): the erase-sum is bounded by (q+1)·Σ_{q+1} d. Pointwise per-(i ∈ W):
d(W.erase i) ≤ d W (insert monotonicity), then sum_const with W.card = q+1. -/
theorem erase_sum_le (c : Fin n → ℤ) (q : ℕ) :
    ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i)
      ≤ ((q + 1 : ℕ) : ℝ) * ∑ W ∈ uniformQSubsets n (q + 1), deficiency c W := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun W hW => ?_
  have hWq : W.card = q + 1 := (Finset.mem_filter.mp hW).2
  calc ∑ i ∈ W, deficiency c (W.erase i)
      ≤ ∑ i ∈ W, deficiency c W :=
      Finset.sum_le_sum fun i hi => by
        have hm := (L2_2_deficiency_insert c (W.erase i) i (Finset.notMem_erase i W)).1
        rw [Finset.insert_erase hi] at hm
        linarith
    _ = ((W.card : ℕ) : ℝ) * deficiency c W := by rw [Finset.sum_const]; simp
    _ = ((q + 1 : ℕ) : ℝ) * deficiency c W := by rw [hWq]

/-- (B): per-fixed-i bijection: (W ∋ i, |W| = q+1) ↔ (V ∌ i, |V| = q), W ↦ W ∖ {i}.
The mem_filter And-extraction via `obtain` + `mem_filter.mp` (the `.left`/
`.right` projection chains break on the Quot/List-Mem display). -/
theorem hbij (c : Fin n → ℤ) (q : ℕ) : ∀ i : Fin n,
    ∑ W ∈ (uniformQSubsets n (q + 1)).filter (fun W => i ∈ W), deficiency c (W.erase i)
      = ∑ V ∈ (uniformQSubsets n q).filter (fun V => i ∉ V), deficiency c V := by
  intro i
  refine Finset.sum_bij (fun W _ => W.erase i) ?_ ?_ ?_ ?_
  · intro W hW
    obtain ⟨hW1, hin⟩ : W ∈ uniformQSubsets n (q + 1) ∧ i ∈ W := by simpa using hW
    obtain ⟨_, hWq⟩ : W ∈ Finset.univ ∧ W.card = q + 1 :=
      Finset.mem_filter.mp hW1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Finset.card_erase_of_mem hin, hWq]; omega⟩,
       Finset.notMem_erase i W⟩
  · intro W₁ hW₁ W₂ hW₂ heq
    have hin : i ∈ W₁ := (Finset.mem_filter.mp hW₁).2
    have hin2 : i ∈ W₂ := (Finset.mem_filter.mp hW₂).2
    have h5 : insert i (W₁.erase i) = insert i (W₂.erase i) := by rw [heq]
    rwa [Finset.insert_erase hin, Finset.insert_erase hin2] at h5
  · intro V hV
    obtain ⟨hV1, hjV⟩ := Finset.mem_filter.mp hV
    obtain ⟨_, hVq⟩ := Finset.mem_filter.mp hV1
    refine ⟨insert i V, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by rw [Finset.card_insert_of_notMem hjV, hVq]⟩,
         Finset.mem_insert_self i V⟩
    · exact Finset.erase_insert hjV
  · intro W _
    rfl

/-- (C): the pair-sum bijection. The `rw [Finset.sdiff_eq_filter]` fails inside
the file context (works standalone — see /tmp/test_sdiff.lean); the workaround
is `Finset.sum_comm'` on the `univ \ V` inner (the dependent inner index is
fine for sum_comm'). -/
theorem sum_erase_bij (c : Fin n → ℤ) (q : ℕ) :
    ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i)
      = ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V := by
  have hswap1 :
      ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i)
        = ∑ i ∈ Finset.univ,
            ∑ W ∈ (uniformQSubsets n (q + 1)).filter (fun W => i ∈ W),
              deficiency c (W.erase i) :=
    Finset.sum_comm' fun W i => by
      constructor
      · intro h
        exact ⟨Finset.mem_filter.mpr h, Finset.mem_univ _⟩
      · intro h
        exact Finset.mem_filter.mp h.1
  have hswap2 :
      ∑ i ∈ Finset.univ,
          ∑ V ∈ (uniformQSubsets n q).filter (fun V => i ∉ V), deficiency c V
        = ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V :=
    Finset.sum_comm' fun i V => by
      constructor
      · intro h
        exact ⟨Finset.mem_sdiff.mpr ⟨h.1, (Finset.mem_filter.mp h.2).2⟩,
          (Finset.mem_filter.mp h.2).1⟩
      · intro h
        exact ⟨(Finset.mem_sdiff.mp h.1).1,
          Finset.mem_filter.mpr ⟨h.2, (Finset.mem_sdiff.mp h.1).2⟩⟩
  rw [hswap1, ← hswap2]
  exact Finset.sum_congr rfl fun i _ => hbij c q i

/-- (D): monotone step. Chain: `(n-q)·Σ_q = ∑_{V∈U_q}∑_{i∈univ∖V} d V
= ∑_{W∈U_{q+1}}∑_{i∈W} d(W.erase i) ≤ (q+1)·Σ_{q+1}` (sum_erase_bij +
erase_sum_le); with `Nat.choose_succ_right_eq` this is exactly the
expectation ratio after `div_le_div_iff₀`. -/
theorem L2_3_expectation_mono (c : Fin n → ℤ) (q : ℕ) (hq : q < n) :
    expectedDeficiency c q ≤ expectedDeficiency c (q + 1) := by
  have hq1 : q + 1 ≤ n := Nat.succ_le_of_lt hq
  have hUq : (uniformQSubsets n q).card = Nat.choose n q := card_uniformQSubsets n q
  have hUq1 : (uniformQSubsets n (q + 1)).card = Nat.choose n (q + 1) :=
    card_uniformQSubsets n (q + 1)
  have hCq : (0 : ℝ) < (Nat.choose n q : ℝ) := by
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt hq))
  have hCq1 : (0 : ℝ) < (Nat.choose n (q + 1) : ℝ) := by
    exact_mod_cast (Nat.choose_pos hq1)
  have hqpos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos q)
  have hsum : ((n - q : ℕ) : ℝ) * ∑ V ∈ uniformQSubsets n q, deficiency c V
      ≤ ((q + 1 : ℕ) : ℝ) * ∑ W ∈ uniformQSubsets n (q + 1), deficiency c W := by
    have hinner : ∀ V ∈ uniformQSubsets n q,
        ∑ i ∈ Finset.univ \ V, deficiency c V = ((n - q : ℕ) : ℝ) * deficiency c V := by
      intro V hV
      have hVq : V.card = q := (Finset.mem_filter.mp hV).2
      have hsub : V ⊆ Finset.univ := Finset.subset_univ V
      rw [Finset.sum_const, Finset.card_sdiff_of_subset hsub, Finset.card_univ,
        Fintype.card_fin, hVq, nsmul_eq_mul]
    calc ((n - q : ℕ) : ℝ) * ∑ V ∈ uniformQSubsets n q, deficiency c V
        = ∑ V ∈ uniformQSubsets n q, ((n - q : ℕ) : ℝ) * deficiency c V := by
          rw [← Finset.mul_sum]
      _ = ∑ V ∈ uniformQSubsets n q, ∑ i ∈ Finset.univ \ V, deficiency c V :=
          Finset.sum_congr rfl fun V hV => (hinner V hV).symm
      _ = ∑ W ∈ uniformQSubsets n (q + 1), ∑ i ∈ W, deficiency c (W.erase i) :=
          (sum_erase_bij c q).symm
      _ ≤ ((q + 1 : ℕ) : ℝ) * ∑ W ∈ uniformQSubsets n (q + 1), deficiency c W :=
          erase_sum_le c q
  have key : (∑ V ∈ uniformQSubsets n q, deficiency c V) * (Nat.choose n (q + 1) : ℝ)
      ≤ (∑ W ∈ uniformQSubsets n (q + 1), deficiency c W) * (Nat.choose n q : ℝ) := by
    have hchoose : (Nat.choose n (q + 1) : ℝ) * ((q + 1 : ℕ) : ℝ)
        = (Nat.choose n q : ℝ) * ((n - q : ℕ) : ℝ) := by
      exact_mod_cast (Nat.choose_succ_right_eq n q)
    refine le_of_mul_le_mul_right ?_ hqpos
    have hmul := mul_le_mul_of_nonneg_right hsum (le_of_lt hCq)
    have hchoose_x : (∑ V ∈ uniformQSubsets n q, deficiency c V)
        * ((Nat.choose n (q + 1) : ℝ) * ((q + 1 : ℕ) : ℝ))
        = (∑ V ∈ uniformQSubsets n q, deficiency c V)
        * ((Nat.choose n q : ℝ) * ((n - q : ℕ) : ℝ)) := by rw [hchoose]
    nlinarith [hmul, hchoose_x]
  rw [expectedDeficiency, expectedDeficiency, Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card, hUq, hUq1, div_le_div_iff₀ hCq hCq1]
  exact key

end SubsetSumL25
