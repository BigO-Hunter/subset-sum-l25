/-
M2 (B1): PROOF of Base Lemma 3.1 «covering» (PROOF_0.4877.tex §3).

Verbatim statement (primary source, a-kapila/maths-proofs @ 44c34961,
subset-sum/PROOF_0.4877.tex, sha256 b397531c…):

    Lemma 3.1 (covering).  Let 0 ≤ k ≤ t ≤ |V|, and let W be a uniform
    (t−k)-subset of V.  Then
        a_t(V) ≤ E_W a_k(V∖W).

Verbatim proof (same source):

    For each x ∈ Σ_t(V), fix a t-set T_x ⊆ V with w(T_x) = x.  Consider the
    pairs (x,W) with W ⊆ T_x and |W| = t−k.  The map (x,W) ↦ (W, x−w(W)) is
    injective, because x = (x−w(W)) + w(W).  Its second coordinate is
    w(T_x∖W) ∈ Σ_k(V∖W).  There are C(t,k)|Σ_t(V)| pairs, so
        C(t,k)|Σ_t(V)| ≤ Σ_{W⊆V, |W|=t−k} |Σ_k(V∖W)|.
    Divide by C(|V|,t)C(t,k) = C(|V|,t−k)C(|V|−t+k,k).

Formalization of the same argument: the representative `T_x` is
`Classical.choose` of the defining existence statement; the injective map is
applied per fixed `W` (an injection is enough — the paper's inverse `(W,y) ↦
(W, y+w(W))` is exactly the reconstruction `x = w(T_x∖W) + w(W)`), and the
pair count `C(t,k)|Σ_t(V)|` is computed by exchanging the two sums over the
`(x,W)` grid (card_filter + sum_comm).  The binomial identity is
`Nat.choose_mul`.
-/
import Mathlib
import SubsetSumL25.Statements.Layers

namespace SubsetSumL25

variable {n : ℕ}

/-- Cardinal form of Base Lemma 3.1 (covering): for `0 ≤ k ≤ t ≤ |V|`,
`C(t,k)|Σ_t(V)| ≤ Σ_{W ⊆ V, |W| = t−k} |Σ_k(V∖W)|` — the counted inequality
that the paper's injection yields. -/
theorem L3_1_covering_card (c : Fin n → ℤ) {V : Finset (Fin n)} {k t : ℕ}
    (hkt : k ≤ t) (ht : t ≤ V.card) :
    (layerSupport c V t).card * Nat.choose t k ≤
      ∑ W ∈ V.powersetCard (t - k), (layerSupport c (V \ W) k).card := by
  classical
  -- (0) for each `x ∈ Σ_t(V)` fix a `t`-subset of `V` with weight `x`
  have hex_of : ∀ x ∈ layerSupport c V t, ∃ T ∈ V.powersetCard t, subsum c T = x := by
    intro x hx
    rw [layerSupport, Finset.mem_image] at hx
    obtain ⟨T, hT, hTx⟩ := hx
    exact ⟨T, hT, hTx⟩
  let rep : ℤ → Finset (Fin n) := fun x =>
    if h : ∃ T ∈ V.powersetCard t, subsum c T = x then Classical.choose h else ∅
  have hrepP : ∀ x ∈ layerSupport c V t, rep x ∈ V.powersetCard t := by
    intro x hx
    have hex := hex_of x hx
    simp only [rep]
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).1
  have hrepsum : ∀ x ∈ layerSupport c V t, subsum c (rep x) = x := by
    intro x hx
    have hex := hex_of x hx
    simp only [rep]
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).2
  have hrepsub : ∀ x ∈ layerSupport c V t, rep x ⊆ V := fun x hx =>
    (Finset.mem_powersetCard.mp (hrepP x hx)).1
  have hrepcard : ∀ x ∈ layerSupport c V t, (rep x).card = t := fun x hx =>
    (Finset.mem_powersetCard.mp (hrepP x hx)).2
  -- (1) per fixed `W`, the cover count: `x ↦ w(rep x \ W)` injects the
  --     `x` whose representative contains `W` into `Σ_k(V∖W)`
  have hfib : ∀ W ∈ V.powersetCard (t - k),
      ((layerSupport c V t).filter (fun x => W ⊆ rep x)).card
        ≤ (layerSupport c (V \ W) k).card := by
    intro W hW
    obtain ⟨hWV, hWc⟩ := Finset.mem_powersetCard.mp hW
    refine Finset.card_le_card_of_injOn (fun x => subsum c (rep x \ W)) ?_ ?_
    · intro x hx
      obtain ⟨hxL, hWrep⟩ := Finset.mem_filter.mp hx
      show subsum c (rep x \ W) ∈ layerSupport c (V \ W) k
      rw [layerSupport, Finset.mem_image]
      refine ⟨rep x \ W, ?_, rfl⟩
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro a ha
        obtain ⟨har, haW⟩ := Finset.mem_sdiff.mp ha
        exact Finset.mem_sdiff.mpr ⟨hrepsub x hxL har, haW⟩
      · rw [Finset.card_sdiff_of_subset hWrep, hrepcard x hxL, hWc]
        omega
    · intro x hx y hy hxy
      obtain ⟨hxL, hWrep⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyL, hWrep'⟩ := Finset.mem_filter.mp hy
      have hxsum : x = subsum c (rep x \ W) + subsum c W := by
        have hs : subsum c (rep x \ W) + subsum c W = subsum c (rep x) := by
          simp only [subsum]
          exact Finset.sum_sdiff hWrep
        rw [hs, hrepsum x hxL]
      have hysum : y = subsum c (rep y \ W) + subsum c W := by
        have hs : subsum c (rep y \ W) + subsum c W = subsum c (rep y) := by
          simp only [subsum]
          exact Finset.sum_sdiff hWrep'
        rw [hs, hrepsum y hyL]
      linarith [hxsum, hysum, hxy]
  -- (2) exchange the two sums over the `(x,W)` grid: exactly `C(t,k)|Σ_t(V)|`
  --     pairs `(x,W)` with `W ⊆ rep x ⊆ V`, `|W| = t−k`
  have hcount : ∑ W ∈ V.powersetCard (t - k),
      ((layerSupport c V t).filter (fun x => W ⊆ rep x)).card
        = (layerSupport c V t).card * Nat.choose t (t - k) := by
    have hstep : ∀ W : Finset (Fin n),
        ((layerSupport c V t).filter (fun x => W ⊆ rep x)).card
          = ∑ x ∈ layerSupport c V t, if W ⊆ rep x then 1 else 0 := fun W =>
      Finset.card_filter _ _
    simp only [hstep]
    rw [Finset.sum_comm]
    have hinner : ∀ x ∈ layerSupport c V t,
        ∑ W ∈ V.powersetCard (t - k), (if W ⊆ rep x then 1 else 0)
          = Nat.choose t (t - k) := by
      intro x hx
      have hfil : (V.powersetCard (t - k)).filter (fun W => W ⊆ rep x)
          = (rep x).powersetCard (t - k) := by
        ext W
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨-, hWc⟩, hWr⟩
          exact ⟨hWr, hWc⟩
        · rintro ⟨hWr, hWc⟩
          exact ⟨⟨hWr.trans (hrepsub x hx), hWc⟩, hWr⟩
      rw [← Finset.card_filter, hfil, Finset.card_powersetCard, hrepcard x hx]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  -- (3) combine: the cover count bounds the pair count
  have hmain := Finset.sum_le_sum hfib
  rw [hcount, Nat.choose_symm hkt] at hmain
  exact hmain

/-- Base Lemma 3.1 (covering): for `0 ≤ k ≤ t ≤ |V|` and a uniform
`(t−k)`-subset `W` of `V`, one has `a_t(V) ≤ E_W a_k(V∖W)`. -/
theorem L3_1_covering (c : Fin n → ℤ) {V : Finset (Fin n)} {k t : ℕ}
    (hkt : k ≤ t) (ht : t ≤ V.card) :
    layerDensity c V t ≤
      (V.powersetCard (t - k)).expect (fun W => layerDensity c (V \ W) k) := by
  classical
  have hcard := L3_1_covering_card c hkt ht
  set m := t - k with hm
  have hmle : m ≤ t := by omega
  have hmv : m ≤ V.card := le_trans hmle ht
  have htm : t - m = k := by omega
  have hCv_t : (0 : ℝ) < (Nat.choose V.card t : ℝ) := by
    exact_mod_cast Nat.choose_pos ht
  have hCv_m : (0 : ℝ) < (Nat.choose V.card m : ℝ) := by
    exact_mod_cast Nat.choose_pos hmv
  have hCk : (0 : ℝ) < (Nat.choose (V.card - m) k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  -- every `W` in the probability space satisfies `|V∖W| = |V| − (t−k)`, so the
  -- denominators `C(|V∖W|,k)` are the same constant
  have hdiff : ∀ W ∈ V.powersetCard m, (V \ W).card = V.card - m := by
    intro W hW
    rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hW).1,
      (Finset.mem_powersetCard.mp hW).2]
  have hsum : ∑ W ∈ V.powersetCard m, layerDensity c (V \ W) k
      = (∑ W ∈ V.powersetCard m, ((layerSupport c (V \ W) k).card : ℝ))
          / (Nat.choose (V.card - m) k : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro W hW
    simp only [layerDensity, hdiff W hW]
  rw [Finset.expect_eq_sum_div_card, hsum, Finset.card_powersetCard, div_div]
  simp only [layerDensity]
  rw [div_le_div_iff₀ hCv_t (mul_pos hCk hCv_m)]
  -- the binomial identity `C(|V|−m,k)·C(|V|,m) = C(|V|,t)·C(t,k)`
  have hbinom : (Nat.choose (V.card - m) k : ℝ) * (Nat.choose V.card m : ℝ)
      = (Nat.choose V.card t : ℝ) * (Nat.choose t k : ℝ) := by
    have hnat : Nat.choose (V.card - m) k * Nat.choose V.card m
        = Nat.choose V.card t * Nat.choose t k := by
      have h1 := Nat.choose_mul (n := V.card) (k := t) (s := m) hmle
      rw [← Nat.choose_symm hmle, htm] at h1
      rw [Nat.mul_comm (Nat.choose (V.card - m) k) (Nat.choose V.card m)]
      exact h1.symm
    exact_mod_cast hnat
  have hcardR : ((layerSupport c V t).card : ℝ) * (Nat.choose t k : ℝ)
      ≤ (∑ W ∈ V.powersetCard m, ((layerSupport c (V \ W) k).card : ℝ)) := by
    exact_mod_cast hcard
  calc ((layerSupport c V t).card : ℝ)
        * ((Nat.choose (V.card - m) k : ℝ) * (Nat.choose V.card m : ℝ))
      = ((layerSupport c V t).card : ℝ)
          * ((Nat.choose V.card t : ℝ) * (Nat.choose t k : ℝ)) := by rw [hbinom]
    _ = (((layerSupport c V t).card : ℝ) * (Nat.choose t k : ℝ))
          * (Nat.choose V.card t : ℝ) := by ring
    _ ≤ (∑ W ∈ V.powersetCard m, ((layerSupport c (V \ W) k).card : ℝ))
          * (Nat.choose V.card t : ℝ) :=
        mul_le_mul_of_nonneg_right hcardR (le_of_lt hCv_t)

end SubsetSumL25
