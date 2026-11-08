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

/-- Cardinal form of Base Lemma 3.2 (sampling): for `k ≤ s ≤ |V|`,
`|Σ_k(V)|·C(|V|−k, s−k) ≤ Σ_{S ⊆ V, |S| = s} |Σ_k(S)|` — the counted
inequality in the paper's proof. -/
theorem L3_2_sampling_card (c : Fin n → ℤ) {V : Finset (Fin n)} {k s : ℕ}
    (hks : k ≤ s) (hsv : s ≤ V.card) :
    (layerSupport c V k).card * Nat.choose (V.card - k) (s - k)
      ≤ ∑ S ∈ V.powersetCard s, (layerSupport c S k).card := by
  classical
  have hksv : k ≤ V.card := le_trans hks hsv
  -- (0) for each `x ∈ Σ_k(V)` fix a `k`-subset of `V` with weight `x`
  have hex_of : ∀ x ∈ layerSupport c V k, ∃ T ∈ V.powersetCard k, subsum c T = x := by
    intro x hx
    rw [layerSupport, Finset.mem_image] at hx
    obtain ⟨T, hT, hTx⟩ := hx
    exact ⟨T, hT, hTx⟩
  let rep : ℤ → Finset (Fin n) := fun x =>
    if h : ∃ T ∈ V.powersetCard k, subsum c T = x then Classical.choose h else ∅
  have hrepP : ∀ x ∈ layerSupport c V k, rep x ∈ V.powersetCard k := by
    intro x hx
    have hex := hex_of x hx
    simp only [rep]
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).1
  have hrepsum : ∀ x ∈ layerSupport c V k, subsum c (rep x) = x := by
    intro x hx
    have hex := hex_of x hx
    simp only [rep]
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).2
  have hrepsub : ∀ x ∈ layerSupport c V k, rep x ⊆ V := fun x hx =>
    (Finset.mem_powersetCard.mp (hrepP x hx)).1
  have hrepcard : ∀ x ∈ layerSupport c V k, (rep x).card = k := fun x hx =>
    (Finset.mem_powersetCard.mp (hrepP x hx)).2
  -- (1) per fixed `S`, the `x` with `rep x ⊆ S` are distinct elements of `Σ_k(S)`
  have hfib : ∀ S ∈ V.powersetCard s,
      ((layerSupport c V k).filter (fun x => rep x ⊆ S)).card
        ≤ (layerSupport c S k).card := by
    intro S hS
    refine Finset.card_le_card_of_injOn (fun x => x) ?_ ?_
    · intro x hx
      obtain ⟨hxL, hrepS⟩ := Finset.mem_filter.mp hx
      show x ∈ layerSupport c S k
      rw [layerSupport, Finset.mem_image]
      refine ⟨rep x, ?_, hrepsum x hxL⟩
      rw [Finset.mem_powersetCard]
      exact ⟨hrepS, hrepcard x hxL⟩
    · intro x _ y _ hxy
      exact hxy
  -- (2) count the `(x,S)` grid the other way: `C(|V|−k, s−k)` choices per `x`
  have hcount : ∑ x ∈ layerSupport c V k,
      ((V.powersetCard s).filter (fun S => rep x ⊆ S)).card
        = (layerSupport c V k).card * Nat.choose (V.card - k) (s - k) := by
    have hstep : ∀ x ∈ layerSupport c V k,
        ((V.powersetCard s).filter (fun S => rep x ⊆ S)).card
          = Nat.choose (V.card - k) (s - k) := by
      intro x hx
      rw [Finset.card_filter_powersetCard_subset (rep x) V s (hrepsub x hx) (by
        rw [hrepcard x hx]
        exact hks), hrepcard x hx]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  -- (3) exchange the two sums over the grid
  have hswap : ∑ S ∈ V.powersetCard s,
      ((layerSupport c V k).filter (fun x => rep x ⊆ S)).card
        = ∑ x ∈ layerSupport c V k,
          ((V.powersetCard s).filter (fun S => rep x ⊆ S)).card := by
    have key : ∀ S : Finset (Fin n),
        ((layerSupport c V k).filter (fun x => rep x ⊆ S)).card
          = ∑ x ∈ layerSupport c V k, if rep x ⊆ S then 1 else 0 := fun S =>
      Finset.card_filter _ _
    have key2 : ∀ x : ℤ,
        ((V.powersetCard s).filter (fun S => rep x ⊆ S)).card
          = ∑ S ∈ V.powersetCard s, if rep x ⊆ S then 1 else 0 := fun x =>
      Finset.card_filter _ _
    calc ∑ S ∈ V.powersetCard s,
          ((layerSupport c V k).filter (fun x => rep x ⊆ S)).card
        = ∑ S ∈ V.powersetCard s,
            ∑ x ∈ layerSupport c V k, if rep x ⊆ S then 1 else 0 := by
          simp only [key]
      _ = ∑ x ∈ layerSupport c V k,
            ∑ S ∈ V.powersetCard s, if rep x ⊆ S then 1 else 0 := Finset.sum_comm
      _ = ∑ x ∈ layerSupport c V k,
            ((V.powersetCard s).filter (fun S => rep x ⊆ S)).card := by
          simp only [key2]
  have hle := Finset.sum_le_sum hfib
  rw [hswap, hcount] at hle
  exact hle

/-- Base Lemma 3.2 (sampling): for `k ≤ s ≤ |V|` and a uniform `s`-subset `S`
of `V`, one has `E_S a_k(S) ≥ a_k(V)`. -/
theorem L3_2_sampling (c : Fin n → ℤ) {V : Finset (Fin n)} {k s : ℕ}
    (hks : k ≤ s) (hsv : s ≤ V.card) :
    layerDensity c V k ≤
      (V.powersetCard s).expect (fun S => layerDensity c S k) := by
  classical
  have hcard := L3_2_sampling_card c hks hsv
  have hksv : k ≤ V.card := le_trans hks hsv
  have hCv_s : (0 : ℝ) < (Nat.choose V.card s : ℝ) := by
    exact_mod_cast Nat.choose_pos hsv
  have hCs_k : (0 : ℝ) < (Nat.choose s k : ℝ) := by
    exact_mod_cast Nat.choose_pos hks
  have hCv_k : (0 : ℝ) < (Nat.choose V.card k : ℝ) := by
    exact_mod_cast Nat.choose_pos hksv
  have hdiff : ∀ S ∈ V.powersetCard s, S.card = s := fun S hS =>
    (Finset.mem_powersetCard.mp hS).2
  have hsum : ∑ S ∈ V.powersetCard s, layerDensity c S k
      = (∑ S ∈ V.powersetCard s, ((layerSupport c S k).card : ℝ))
          / (Nat.choose s k : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro S hS
    simp only [layerDensity, hdiff S hS]
  rw [Finset.expect_eq_sum_div_card, hsum, Finset.card_powersetCard, div_div]
  simp only [layerDensity]
  rw [div_le_div_iff₀ hCv_k (mul_pos hCs_k hCv_s)]
  -- the binomial identity `C(s,k)·C(|V|,s) = C(|V|,k)·C(|V|−k, s−k)`
  have hbinom : (Nat.choose s k : ℝ) * (Nat.choose V.card s : ℝ)
      = (Nat.choose V.card k : ℝ) * (Nat.choose (V.card - k) (s - k) : ℝ) := by
    have hnat : Nat.choose s k * Nat.choose V.card s
        = Nat.choose V.card k * Nat.choose (V.card - k) (s - k) := by
      rw [Nat.mul_comm (Nat.choose s k) (Nat.choose V.card s)]
      exact Nat.choose_mul hks
    exact_mod_cast hnat
  have hcardR : ((layerSupport c V k).card : ℝ) * (Nat.choose (V.card - k) (s - k) : ℝ)
      ≤ (∑ S ∈ V.powersetCard s, ((layerSupport c S k).card : ℝ)) := by
    exact_mod_cast hcard
  calc ((layerSupport c V k).card : ℝ) * ((Nat.choose s k : ℝ) * (Nat.choose V.card s : ℝ))
      = ((layerSupport c V k).card : ℝ)
          * ((Nat.choose V.card k : ℝ) * (Nat.choose (V.card - k) (s - k) : ℝ)) := by
        rw [hbinom]
    _ = (((layerSupport c V k).card : ℝ) * (Nat.choose (V.card - k) (s - k) : ℝ))
          * (Nat.choose V.card k : ℝ) := by ring
    _ ≤ (∑ S ∈ V.powersetCard s, ((layerSupport c S k).card : ℝ))
          * (Nat.choose V.card k : ℝ) :=
        mul_le_mul_of_nonneg_right hcardR (le_of_lt hCv_k)

/-- Complementation exchanges layer `j` with layer `|V|−j`:
`Σ_{|V|−j}(V) = (w(V) − ·)(Σ_j(V))`. (Base §3: «Complementation gives
Σ_{|V|−j}(V) = w(V) − Σ_j(V)».) -/
theorem layerSupport_compl (c : Fin n → ℤ) {V : Finset (Fin n)} {j : ℕ} (hj : j ≤ V.card) :
    layerSupport c V (V.card - j) = (layerSupport c V j).image (fun y => subsum c V - y) := by
  classical
  have hsplit : ∀ T ⊆ V, subsum c (V \ T) + subsum c T = subsum c V := by
    intro T hT
    simp only [subsum]
    exact Finset.sum_sdiff hT
  -- `w(V∖T) ∈ Σ_j(V)` when `|T| = |V| − j`
  have key1 : ∀ T ⊆ V, T.card = V.card - j → subsum c (V \ T) ∈ layerSupport c V j := by
    intro T hT hTc
    have hc : (V \ T).card = j := by
      rw [Finset.card_sdiff_of_subset hT, hTc]
      omega
    rw [layerSupport, Finset.mem_image]
    exact ⟨V \ T,
      Finset.mem_powersetCard.mpr ⟨fun a ha => (Finset.mem_sdiff.mp ha).1, hc⟩, rfl⟩
  -- `w(V) − w(T) ∈ Σ_{|V|−j}(V)` when `|T| = j`
  have key2 : ∀ T ⊆ V, T.card = j → subsum c V - subsum c T ∈ layerSupport c V (V.card - j) := by
    intro T hT hTc
    rw [layerSupport, Finset.mem_image]
    refine ⟨V \ T, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨fun a ha => (Finset.mem_sdiff.mp ha).1, by
        rw [Finset.card_sdiff_of_subset hT, hTc]⟩
    · show subsum c (V \ T) = subsum c V - subsum c T
      linarith [hsplit T hT]
  ext y
  constructor
  · intro hy
    rw [layerSupport, Finset.mem_image] at hy
    obtain ⟨T, hT, hTy⟩ := hy
    obtain ⟨hTV, hTc⟩ := Finset.mem_powersetCard.mp hT
    refine Finset.mem_image.mpr ⟨subsum c (V \ T), key1 T hTV hTc, ?_⟩
    show subsum c V - subsum c (V \ T) = y
    rw [← hTy]
    linarith [hsplit T hTV]
  · intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [layerSupport, Finset.mem_image] at hx
    obtain ⟨T, hT, hTx⟩ := hx
    obtain ⟨hTV, hTc⟩ := Finset.mem_powersetCard.mp hT
    have hy' : y = subsum c V - subsum c T := by rw [← hxy, hTx]
    rw [hy']
    exact key2 T hTV hTc

/-- Base Lemma 3.3 (a good layer), existence half: some layer index `t` with
`2t ≤ |V|` carries at least a `1/(|V|+1)` fraction of the whole support,
`|Σ(V)| ≤ (|V|+1) |Σ_t(V)|`. -/
theorem L3_3_good_layer (c : Fin n → ℤ) (V : Finset (Fin n)) :
    ∃ t, 2 * t ≤ V.card ∧
      (support c V).card ≤ (V.card + 1) * (layerSupport c V t).card := by
  classical
  -- (1) the `|V|+1` layers cover `Σ(V)`
  have hcover : support c V ⊆ (Finset.range (V.card + 1)).biUnion
      (fun j => layerSupport c V j) := by
    intro y hy
    unfold support at hy
    rw [Finset.mem_image] at hy
    obtain ⟨T, hT, rfl⟩ := hy
    rw [Finset.mem_powerset] at hT
    refine Finset.mem_biUnion.mpr ⟨T.card, Finset.mem_range.mpr (by
      have := Finset.card_le_card hT
      omega), ?_⟩
    rw [layerSupport, Finset.mem_image]
    exact ⟨T, Finset.mem_powersetCard.mpr ⟨hT, rfl⟩, rfl⟩
  have hle : (support c V).card
      ≤ ∑ j ∈ Finset.range (V.card + 1), (layerSupport c V j).card :=
    le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  -- (2) pigeonhole: the average layer is at least `|Σ(V)|/(|V|+1)`
  have hne : (Finset.range (V.card + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨j, hjmem, hmax⟩ := Finset.exists_max_image (Finset.range (V.card + 1))
    (fun j => (layerSupport c V j).card) hne
  have hsum_le : ∑ i ∈ Finset.range (V.card + 1), (layerSupport c V i).card
      ≤ (V.card + 1) * (layerSupport c V j).card := by
    have h := Finset.sum_le_card_nsmul (Finset.range (V.card + 1))
      (fun i => (layerSupport c V i).card) ((layerSupport c V j).card) hmax
    simpa using h
  have hbig : (support c V).card ≤ (V.card + 1) * (layerSupport c V j).card :=
    le_trans hle hsum_le
  have hjle : j ≤ V.card := by
    have := Finset.mem_range.mp hjmem
    omega
  -- (3) complementation moves `j` to `min j (|V|−j)` without losing cardinality
  refine ⟨min j (V.card - j), ?_, ?_⟩
  · have h1 : min j (V.card - j) ≤ j := min_le_left _ _
    have h2 : min j (V.card - j) ≤ V.card - j := min_le_right _ _
    omega
  · have heq : (layerSupport c V (min j (V.card - j))).card
        = (layerSupport c V j).card := by
      by_cases h : j ≤ V.card - j
      · rw [min_eq_left h]
      · have h' : V.card - j ≤ j := by omega
        rw [min_eq_right h', layerSupport_compl c hjle]
        exact Finset.card_image_of_injOn (fun a _ b _ hab => by linarith)
    rw [heq]
    exact hbig

/-- `2^{−d(V)} = |Σ(V)|/2^{|V|}` — the exact identity used to pass from the
cardinal form of Lemma 3.3 to its density form. -/
theorem twoPow_neg_deficiency (c : Fin n → ℤ) (V : Finset (Fin n)) :
    (2 : ℝ) ^ (-(deficiency c V)) = ((support c V).card : ℝ) / 2 ^ V.card := by
  have hmem : (0 : ℤ) ∈ support c V := by
    unfold support
    exact Finset.mem_image.mpr
      ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset V), by simp [subsum]⟩
  have hcard1 : (1 : ℕ) ≤ (support c V).card :=
    Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hmem⟩)
  have hN : (0 : ℝ) < ((support c V).card : ℝ) := by exact_mod_cast hcard1
  rw [deficiency, neg_sub, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.log_div_log,
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hN,
    Real.rpow_natCast]

/-- Base Lemma 3.3 (a good layer), density half («in particular»): some `t`
with `2t ≤ |V|` has `a_t(V) ≥ 2^{−d(V)}/(|V|+1)`. -/
theorem L3_3_good_layer_density (c : Fin n → ℤ) (V : Finset (Fin n)) :
    ∃ t, 2 * t ≤ V.card ∧
      (2 : ℝ) ^ (-(deficiency c V)) / ((V.card : ℝ) + 1) ≤ layerDensity c V t := by
  classical
  obtain ⟨t, ht2, htcard⟩ := L3_3_good_layer c V
  have htle : t ≤ V.card := by omega
  have htcardR : ((support c V).card : ℝ)
      ≤ ((V.card : ℝ) + 1) * ((layerSupport c V t).card : ℝ) := by
    have h : ((support c V).card : ℝ)
        ≤ (((V.card + 1 : ℕ)) : ℝ) * ((layerSupport c V t).card : ℝ) := by
      exact_mod_cast htcard
    rw [Nat.cast_add, Nat.cast_one] at h
    exact h
  have hp : (0 : ℝ) < (V.card : ℝ) + 1 := by positivity
  have hCpos : (0 : ℝ) < (Nat.choose V.card t : ℝ) := by
    exact_mod_cast Nat.choose_pos htle
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ V.card := by positivity
  have hCle : (Nat.choose V.card t : ℝ) ≤ (2 : ℝ) ^ V.card := by
    have h := Nat.choose_le_two_pow V.card t
    exact_mod_cast h
  have hNnonneg : (0 : ℝ) ≤ ((support c V).card : ℝ) := by positivity
  have hTnonneg : (0 : ℝ) ≤ ((layerSupport c V t).card : ℝ) := by positivity
  have step1 : ((support c V).card : ℝ) / ((V.card : ℝ) + 1)
      ≤ ((layerSupport c V t).card : ℝ) := by
    rw [div_le_iff₀ hp]
    linarith
  have step2 : ((support c V).card : ℝ) / (((V.card : ℝ) + 1) * (2 : ℝ) ^ V.card)
      ≤ ((layerSupport c V t).card : ℝ) / (2 : ℝ) ^ V.card := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right step1 (le_of_lt h2pos)
  have step3 : ((layerSupport c V t).card : ℝ) / (2 : ℝ) ^ V.card
      ≤ ((layerSupport c V t).card : ℝ) / (Nat.choose V.card t : ℝ) :=
    div_le_div_of_nonneg_left hTnonneg hCpos hCle
  refine ⟨t, ht2, ?_⟩
  rw [twoPow_neg_deficiency, div_div,
    mul_comm ((2 : ℝ) ^ V.card) ((V.card : ℝ) + 1)]
  exact le_trans step2 step3

end SubsetSumL25
