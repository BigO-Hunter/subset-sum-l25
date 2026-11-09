/-
M2 (B2): the `t < k` branch of Base Corollary D, and its floor lemma.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` §3 (sha256 b397531c…).  Verbatim proof text for
this branch:

    Case t < k.  Then t < k ≤ v/2, so |Σ_t(V)| ≤ C(v,t) ≤ C(v,k).  Lemma 3.3
    gives 2^{v−d(V)} ≤ (v+1)C(v,k).  With the hypothesis,
    2^{−d(V)}/(v+1) ≤ C(v,k)2^{−v} ≤ 1/C(σ,k).  Every σ-set S has
    a_k(S) ≥ 1/C(σ,k), because Σ_k(S) is not empty.

Each clause is one step below: `choose_le_choose_of_two_mul_le` is the
`C(v,t) ≤ C(v,k)` step (the only place the smallness of `t` matters),
`one_div_choose_le_layerDensity` is the floor, and `Base_cor_D_case_lt` is the
assembly, including the `C(σ,k)C(v,k) ≤ 2^v` hypothesis — which is used *only*
in this branch.
-/
import Mathlib
import SubsetSumL25.Statements.CorD
import SubsetSumL25.Proofs.Layers

namespace SubsetSumL25

variable {n : ℕ}

/-- Binomial coefficients are nondecreasing below the middle: for `t ≤ k` with
`2k ≤ |V|`, `C(v,t) ≤ C(v,k)`.  (Base's step «t < k ≤ v/2, so C(v,t) ≤ C(v,k)»;
Mathlib only exposes the one-step form `Nat.choose_le_succ_of_lt_half_left`.) -/
theorem choose_le_choose_of_two_mul_le {v t k : ℕ} (htk : t ≤ k) (hk : 2 * k ≤ v) :
    Nat.choose v t ≤ Nat.choose v k := by
  have hmono : ∀ d, t + d ≤ k → Nat.choose v t ≤ Nat.choose v (t + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h1 : t + d ≤ k := by omega
      refine (ih h1).trans (Nat.choose_le_succ_of_lt_half_left (r := t + d) (n := v) ?_)
      omega
  have hstep := hmono (k - t) (by omega)
  rwa [show t + (k - t) = k by omega] at hstep

/-- The floor: every `σ`-set `S` with `k ≤ σ` has `a_k(S) ≥ 1/C(σ,k)`, because
`Σ_k(S)` contains the weight of any `k`-subset of `S`, hence is nonempty.
(Paper: «Every σ-set S has a_k(S) ≥ 1/C(σ,k), because Σ_k(S) is not empty».) -/
theorem one_div_choose_le_layerDensity (c : Fin n → ℤ) {S : Finset (Fin n)} {k σ : ℕ}
    (hkσ : k ≤ σ) (hS : S.card = σ) :
    1 / (Nat.choose σ k : ℝ) ≤ layerDensity c S k := by
  classical
  have hkS : k ≤ S.card := by omega
  obtain ⟨K, hK⟩ := Finset.powersetCard_nonempty.mpr hkS
  have hmem : subsum c K ∈ layerSupport c S k := by
    rw [layerSupport, Finset.mem_image]
    exact ⟨K, hK, rfl⟩
  have hcard1 : (1 : ℕ) ≤ (layerSupport c S k).card :=
    Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨_, hmem⟩)
  have hCpos : (0 : ℝ) < (Nat.choose σ k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkσ
  have hcardR : (1 : ℝ) ≤ ((layerSupport c S k).card : ℝ) := by exact_mod_cast hcard1
  unfold layerDensity
  rw [show Nat.choose S.card k = Nat.choose σ k by rw [hS]]
  rw [div_le_div_iff₀ hCpos hCpos]
  nlinarith [hcardR, hCpos]

/-- Base Corollary D, case `t < k`: with `t` Lemma 3.3's layer index below `k`,
the floor `1/C(σ,k)` already dominates `2^{−d(V)}/(v+1)`, and every term of the
`S`-average is at least the floor. -/
theorem Base_cor_D_case_lt (c : Fin n → ℤ) {V : Finset (Fin n)} {k σ v t : ℕ}
    (hVc : V.card = v) (htk : t < k)
    (htcard : (support c V).card ≤ (v + 1) * (layerSupport c V t).card)
    (hk2 : 2 * k ≤ σ) (hσ2 : 2 * σ ≤ v + 2 * k)
    (hch : Nat.choose σ k * Nat.choose v k ≤ 2 ^ v) :
    (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1)
      ≤ (V.powersetCard σ).expect (fun S => layerDensity c S k) := by
  classical
  have hkσ : k ≤ σ := by omega
  have hσv : σ ≤ v := by omega
  have hkv2 : 2 * k ≤ v := by omega
  -- (a) `|Σ_t(V)| ≤ C(v,t) ≤ C(v,k)`
  have h1 : (layerSupport c V t).card ≤ Nat.choose v t := by
    calc (layerSupport c V t).card ≤ (V.powersetCard t).card := Finset.card_image_le
      _ = Nat.choose V.card t := Finset.card_powersetCard t V
      _ = Nat.choose v t := by rw [hVc]
  have h2 : Nat.choose v t ≤ Nat.choose v k :=
    choose_le_choose_of_two_mul_le (by omega) hkv2
  -- (b) Lemma 3.3 + (a): `|Σ(V)| ≤ (v+1) C(v,k)`
  have hbig : (support c V).card ≤ (v + 1) * Nat.choose v k := by
    calc (support c V).card ≤ (v + 1) * (layerSupport c V t).card := htcard
      _ ≤ (v + 1) * Nat.choose v t := Nat.mul_le_mul_left _ h1
      _ ≤ (v + 1) * Nat.choose v k := Nat.mul_le_mul_left _ h2
  have hNcast : ((support c V).card : ℝ) ≤ ((v : ℝ) + 1) * (Nat.choose v k : ℝ) := by
    have h : ((support c V).card : ℝ) ≤ (((v + 1 : ℕ)) : ℝ) * (Nat.choose v k : ℝ) := by
      exact_mod_cast hbig
    rw [Nat.cast_add, Nat.cast_one] at h
    exact h
  -- (c) `2^{−d(V)}/(v+1) ≤ C(v,k)/2^v`, via the exact identity `2^{−d} = |Σ(V)|/2^{|V|}`
  have hstep1 : (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1)
      ≤ (Nat.choose v k : ℝ) / 2 ^ v := by
    have h2v : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
    have hden : (0 : ℝ) < (2 : ℝ) ^ v * ((v : ℝ) + 1) := by positivity
    rw [twoPow_neg_deficiency, hVc, div_div, div_le_div_iff₀ hden h2v]
    nlinarith [hNcast, h2v, hden]
  -- (d) the hypothesis `C(σ,k)C(v,k) ≤ 2^v` gives `C(v,k)/2^v ≤ 1/C(σ,k)`
  have hCσk : (0 : ℝ) < (Nat.choose σ k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkσ
  have hchR : (Nat.choose σ k : ℝ) * (Nat.choose v k : ℝ) ≤ (2 : ℝ) ^ v := by
    exact_mod_cast hch
  have hstep2 : (Nat.choose v k : ℝ) / 2 ^ v ≤ 1 / (Nat.choose σ k : ℝ) := by
    have h2v : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
    rw [div_le_div_iff₀ h2v hCσk]
    nlinarith [hchR]
  -- (e) the floor dominates the average, every term being at least `1/C(σ,k)`
  have hne : (V.powersetCard σ).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by omega)
  have hfloor : (V.powersetCard σ).expect (fun _ => 1 / (Nat.choose σ k : ℝ))
      ≤ (V.powersetCard σ).expect (fun S => layerDensity c S k) := by
    refine Finset.expect_le_expect ?_
    intro S hS
    exact one_div_choose_le_layerDensity c hkσ (Finset.mem_powersetCard.mp hS).2
  rw [Finset.expect_const hne] at hfloor
  exact le_trans hstep1 (le_trans hstep2 hfloor)

/-- The disjoint two-level binomial identity
`C(N,a)·C(N−a,b) = C(N,b)·C(N−b,a)` (count the pairs `(A,B)` with
`A ∩ B = ∅`, `|A| = a`, `|B| = b`, in the two orders).  Mathlib's
`Nat.choose_mul` only gives the containment shape, so this is two applications
of it joined by `Nat.choose_symm`. -/
theorem choose_mul_choose_swap {N a b : ℕ} (h : a + b ≤ N) :
    Nat.choose N a * Nat.choose (N - a) b = Nat.choose N b * Nat.choose (N - b) a := by
  have ha : a ≤ a + b := Nat.le_add_right a b
  have hb : b ≤ a + b := Nat.le_add_left b a
  have h1 := Nat.choose_mul (n := N) (k := a + b) (s := a) ha
  have h2 := Nat.choose_mul (n := N) (k := a + b) (s := b) hb
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel_right] at h2
  rw [← Nat.choose_symm ha, Nat.add_sub_cancel_left] at h1
  exact h1.symm.trans h2

/-- Two-level uniform sampling (containment): averaging over `p`-subsets `V` of
`M` and then over `q`-subsets `S ⊆ V` equals averaging over `q`-subsets of `M`.
(Paper: «A uniform σ-subset of a uniform v-subset of M is a uniform σ-subset of
M».)  `p ≤ M.card` keeps both averaging spaces nonempty. -/
theorem expect_powersetCard_powersetCard (M : Finset (Fin n)) {p q : ℕ}
    (hp : p ≤ M.card) (hq : q ≤ p) (f : Finset (Fin n) → ℝ) :
    (M.powersetCard p).expect (fun V => (V.powersetCard q).expect f)
      = (M.powersetCard q).expect f := by
  classical
  have hqm : q ≤ M.card := le_trans hq hp
  have hCpq : (0 : ℝ) < (Nat.choose p q : ℝ) := by exact_mod_cast Nat.choose_pos hq
  have hCmp : (0 : ℝ) < (Nat.choose M.card p : ℝ) := by exact_mod_cast Nat.choose_pos hp
  have hCmq : (0 : ℝ) < (Nat.choose M.card q : ℝ) := by exact_mod_cast Nat.choose_pos hqm
  -- inner denominator is the constant `C(p,q)`
  have hinner : ∀ V ∈ M.powersetCard p,
      (V.powersetCard q).expect f
        = (∑ S ∈ V.powersetCard q, f S) / (Nat.choose p q : ℝ) := by
    intro V hV
    rw [Finset.expect_eq_sum_div_card, Finset.card_powersetCard,
      (Finset.mem_powersetCard.mp hV).2]
  -- the double sum, counted per `S`
  have hswap : ∑ V ∈ M.powersetCard p, ∑ S ∈ V.powersetCard q, f S
      = (Nat.choose (M.card - q) (p - q) : ℝ) * ∑ S ∈ M.powersetCard q, f S := by
    have hfil : ∀ V, V ⊆ M → (M.powersetCard q).filter (fun S => S ⊆ V) = V.powersetCard q := by
      intro V hVM
      ext S
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨-, hSc⟩, hSV⟩; exact ⟨hSV, hSc⟩
      · rintro ⟨hSV, hSc⟩; exact ⟨⟨hSV.trans hVM, hSc⟩, hSV⟩
    have hrew : ∀ V ∈ M.powersetCard p, ∑ S ∈ V.powersetCard q, f S
        = ∑ S ∈ M.powersetCard q, if S ⊆ V then f S else 0 := by
      intro V hV
      rw [← Finset.sum_filter, hfil V (Finset.mem_powersetCard.mp hV).1]
    have hinner2 : ∀ S ∈ M.powersetCard q,
        ∑ V ∈ M.powersetCard p, (if S ⊆ V then f S else 0)
          = f S * (Nat.choose (M.card - q) (p - q) : ℝ) := by
      intro S hS
      have hSM : S ⊆ M := (Finset.mem_powersetCard.mp hS).1
      have hSc : S.card = q := (Finset.mem_powersetCard.mp hS).2
      have h1 : ∑ V ∈ M.powersetCard p, (if S ⊆ V then f S else 0)
          = f S * ∑ V ∈ M.powersetCard p, (if S ⊆ V then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun V _ => by split_ifs <;> simp)
      rw [h1, Finset.sum_boole,
        Finset.card_filter_powersetCard_subset S M p hSM (by omega), hSc]
    rw [Finset.sum_congr rfl hrew, Finset.sum_comm, Finset.sum_congr rfl hinner2,
      ← Finset.sum_mul, mul_comm]
  -- binomial identity `C(p,q)·C(|M|,p) = C(|M|,q)·C(|M|−q,p−q)`
  have hbinom : (Nat.choose p q : ℝ) * (Nat.choose M.card p : ℝ)
      = (Nat.choose M.card q : ℝ) * (Nat.choose (M.card - q) (p - q) : ℝ) := by
    calc (Nat.choose p q : ℝ) * (Nat.choose M.card p : ℝ)
        = (Nat.choose M.card p : ℝ) * (Nat.choose p q : ℝ) := by rw [mul_comm]
      _ = (Nat.choose M.card q : ℝ) * (Nat.choose (M.card - q) (p - q) : ℝ) := by
          exact_mod_cast Nat.choose_mul (n := M.card) (k := p) (s := q) hq
  have hbinom' : (Nat.choose (M.card - q) (p - q) : ℝ) * (Nat.choose M.card q : ℝ)
      = (Nat.choose p q : ℝ) * (Nat.choose M.card p : ℝ) := by
    rw [mul_comm (Nat.choose (M.card - q) (p - q) : ℝ) (Nat.choose M.card q : ℝ), ← hbinom]
  rw [Finset.expect_eq_sum_div_card, Finset.sum_congr rfl hinner, ← Finset.sum_div,
    hswap, Finset.expect_eq_sum_div_card, Finset.card_powersetCard,
    Finset.card_powersetCard, div_div,
    div_eq_div_iff (ne_of_gt (mul_pos hCpq hCmp)) (ne_of_gt hCmq)]
  linear_combination (∑ S ∈ M.powersetCard q, f S) * hbinom'

/-- Two-level uniform sampling (disjoint): averaging over `p`-subsets `W` of `V`
and then over `q`-subsets of the complement `V∖W` equals averaging over
`q`-subsets of `V`.  (Paper: «When W is uniform, S' is a uniform σ-subset of
V».)  `p + q ≤ |V|` keeps every averaging space nonempty. -/
theorem expect_powersetCard_sdiff (V : Finset (Fin n)) {p q : ℕ}
    (h : p + q ≤ V.card) (f : Finset (Fin n) → ℝ) :
    (V.powersetCard p).expect (fun W => ((V \ W).powersetCard q).expect f)
      = (V.powersetCard q).expect f := by
  classical
  have hpc : p ≤ V.card := by omega
  have hqc : q ≤ V.card := by omega
  have hCvp : (0 : ℝ) < (Nat.choose V.card p : ℝ) := by exact_mod_cast Nat.choose_pos hpc
  have hCvq : (0 : ℝ) < (Nat.choose V.card q : ℝ) := by exact_mod_cast Nat.choose_pos hqc
  have hCvpq : (0 : ℝ) < (Nat.choose (V.card - p) q : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  -- inner denominator is the constant `C(|V|−p, q)`
  have hinner : ∀ W ∈ V.powersetCard p,
      ((V \ W).powersetCard q).expect f
        = (∑ S ∈ (V \ W).powersetCard q, f S) / (Nat.choose (V.card - p) q : ℝ) := by
    intro W hW
    have hWc : W.card = p := (Finset.mem_powersetCard.mp hW).2
    have hWV : W ⊆ V := (Finset.mem_powersetCard.mp hW).1
    rw [Finset.expect_eq_sum_div_card, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset hWV, hWc]
  -- the double sum, counted per `S` (now over the complement of `W`)
  have hswap : ∑ W ∈ V.powersetCard p, ∑ S ∈ (V \ W).powersetCard q, f S
      = (Nat.choose (V.card - q) p : ℝ) * ∑ S ∈ V.powersetCard q, f S := by
    have hfil : ∀ W, W ⊆ V →
        (V.powersetCard q).filter (fun S => S ⊆ V \ W) = (V \ W).powersetCard q := by
      intro W hWV
      ext S
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨-, hSc⟩, hSVW⟩; exact ⟨hSVW, hSc⟩
      · rintro ⟨hSVW, hSc⟩
        refine ⟨⟨?_, hSc⟩, hSVW⟩
        intro a ha
        exact (Finset.mem_sdiff.mp (hSVW ha)).1
    have hrew : ∀ W ∈ V.powersetCard p, ∑ S ∈ (V \ W).powersetCard q, f S
        = ∑ S ∈ V.powersetCard q, if S ⊆ V \ W then f S else 0 := by
      intro W hW
      rw [← Finset.sum_filter, hfil W (Finset.mem_powersetCard.mp hW).1]
    -- the `W` compatible with a fixed `S` are exactly the `p`-subsets of `V∖S`
    have hfil2 : ∀ S, S ⊆ V →
        (V.powersetCard p).filter (fun W => S ⊆ V \ W) = (V \ S).powersetCard p := by
      intro S hSV
      ext W
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hWV, hWc⟩, hSVW⟩
        refine ⟨fun a ha => Finset.mem_sdiff.mpr ⟨hWV ha, ?_⟩, hWc⟩
        intro haS
        exact (Finset.mem_sdiff.mp (hSVW haS)).2 ha
      · rintro ⟨hWVS, hWc⟩
        refine ⟨⟨fun a ha => (Finset.mem_sdiff.mp (hWVS ha)).1, hWc⟩, ?_⟩
        intro a haS
        exact Finset.mem_sdiff.mpr ⟨hSV haS, fun haW =>
          (Finset.mem_sdiff.mp (hWVS haW)).2 haS⟩
    have hinner2 : ∀ S ∈ V.powersetCard q,
        ∑ W ∈ V.powersetCard p, (if S ⊆ V \ W then f S else 0)
          = f S * (Nat.choose (V.card - q) p : ℝ) := by
      intro S hS
      have hSV : S ⊆ V := (Finset.mem_powersetCard.mp hS).1
      have hSc : S.card = q := (Finset.mem_powersetCard.mp hS).2
      have h1 : ∑ W ∈ V.powersetCard p, (if S ⊆ V \ W then f S else 0)
          = f S * ∑ W ∈ V.powersetCard p, (if S ⊆ V \ W then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun W _ => by split_ifs <;> simp)
      rw [h1, Finset.sum_boole, hfil2 S hSV, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset hSV, hSc]
    rw [Finset.sum_congr rfl hrew, Finset.sum_comm, Finset.sum_congr rfl hinner2,
      ← Finset.sum_mul, mul_comm]
  have hbinom : (Nat.choose V.card p : ℝ) * (Nat.choose (V.card - p) q : ℝ)
      = (Nat.choose V.card q : ℝ) * (Nat.choose (V.card - q) p : ℝ) := by
    exact_mod_cast choose_mul_choose_swap (N := V.card) (a := p) (b := q) h
  rw [Finset.expect_eq_sum_div_card, Finset.sum_congr rfl hinner, ← Finset.sum_div,
    hswap, Finset.expect_eq_sum_div_card, Finset.card_powersetCard,
    Finset.card_powersetCard, div_div,
    mul_comm (Nat.choose (V.card - p) q : ℝ) (Nat.choose V.card p : ℝ),
    div_eq_div_iff (ne_of_gt (mul_pos hCvp hCvpq)) (ne_of_gt hCvq)]
  linear_combination -((∑ S ∈ V.powersetCard q, f S)) * hbinom

/-- Base Corollary D, case `t ≥ k`: Lemma 3.1 (covering) down to `V∖W`, then
Lemma 3.2 (sampling) inside each `V∖W`, then the disjoint two-level averaging
which says a uniform σ-subset of a uniform `(t−k)`-complement is a uniform
σ-subset of `V`. -/
theorem Base_cor_D_case_ge (c : Fin n → ℤ) {V : Finset (Fin n)} {k σ v t : ℕ}
    (hVc : V.card = v) (ht2 : 2 * t ≤ v) (hkt : k ≤ t)
    (htcard : (support c V).card ≤ (v + 1) * (layerSupport c V t).card)
    (hkσ : k ≤ σ) (hσ2 : 2 * σ ≤ v + 2 * k) :
    (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1)
      ≤ (V.powersetCard σ).expect (fun S => layerDensity c S k) := by
  classical
  have htv : t ≤ V.card := by omega
  have ht2' : 2 * t ≤ V.card := by omega
  have htcard' : (support c V).card ≤ (V.card + 1) * (layerSupport c V t).card := by
    rw [hVc]; exact htcard
  -- (a) Lemma 3.3's density clause for this same `t`
  have hdens : (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1) ≤ layerDensity c V t := by
    have := layerDensity_ge_of_card c V ht2' htcard'
    rw [hVc] at this
    exact this
  -- (b) Lemma 3.1: `a_t(V) ≤ E_W a_k(V∖W)`
  have hcov : layerDensity c V t
      ≤ (V.powersetCard (t - k)).expect (fun W => layerDensity c (V \ W) k) :=
    L3_1_covering c hkt htv
  -- (c) pointwise Lemma 3.2, then the disjoint two-level averaging
  have hswap_cond : (t - k) + σ ≤ V.card := by omega
  have hstep : (V.powersetCard (t - k)).expect (fun W => layerDensity c (V \ W) k)
      ≤ (V.powersetCard σ).expect (fun S => layerDensity c S k) := by
    rw [← expect_powersetCard_sdiff V (p := t - k) (q := σ) hswap_cond
      (fun S => layerDensity c S k)]
    refine Finset.expect_le_expect ?_
    intro W hW
    have hWV : W ⊆ V := (Finset.mem_powersetCard.mp hW).1
    have hWc : W.card = t - k := (Finset.mem_powersetCard.mp hW).2
    have hcard : (V \ W).card = v - (t - k) := by
      rw [Finset.card_sdiff_of_subset hWV, hWc, hVc]
    exact L3_2_sampling c hkσ (by omega)
  exact le_trans hdens (le_trans hcov hstep)

/-- Base Corollary D (averaged small layer): for integers `k, σ, v` with
`2k ≤ σ`, `2σ ≤ v + 2k`, `v ≤ |M|` and `C(σ,k)C(v,k) ≤ 2^v`, averaging `a_k`
over uniform σ-subsets `S` of `M` dominates `E_V 2^{−d(V)}/(v+1)` over uniform
`v`-subsets `V` of `M`. -/
theorem Base_cor_D (c : Fin n → ℤ) (M : Finset (Fin n)) {k σ v : ℕ}
    (hk2 : 2 * k ≤ σ) (hσ2 : 2 * σ ≤ v + 2 * k) (hvM : v ≤ M.card)
    (hch : Nat.choose σ k * Nat.choose v k ≤ 2 ^ v) :
    (M.powersetCard v).expect (fun V => (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1))
      ≤ (M.powersetCard σ).expect (fun S => layerDensity c S k) := by
  classical
  have hkσ : k ≤ σ := by omega
  have hσv : σ ≤ v := by omega
  -- the per-`V` claim: one `t` from Lemma 3.3, dispatched on `t ≥ k`
  have hpoint : ∀ V ∈ M.powersetCard v,
      (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1)
        ≤ (V.powersetCard σ).expect (fun S => layerDensity c S k) := by
    intro V hV
    obtain ⟨-, hVc⟩ := Finset.mem_powersetCard.mp hV
    obtain ⟨t, ht2, htcard⟩ := L3_3_good_layer c V
    have ht2v : 2 * t ≤ v := by rw [← hVc]; exact ht2
    have htcardv : (support c V).card ≤ (v + 1) * (layerSupport c V t).card := by
      rw [← hVc]; exact htcard
    by_cases htk : k ≤ t
    · exact Base_cor_D_case_ge c hVc ht2v htk htcardv hkσ hσ2
    · exact Base_cor_D_case_lt c hVc (by omega) htcardv hk2 hσ2 hch
  -- average over `V`, then recognise the nested average
  calc (M.powersetCard v).expect
        (fun V => (2 : ℝ) ^ (-(deficiency c V)) / ((v : ℝ) + 1))
      ≤ (M.powersetCard v).expect
          (fun V => (V.powersetCard σ).expect (fun S => layerDensity c S k)) :=
        Finset.expect_le_expect hpoint
    _ = (M.powersetCard σ).expect (fun S => layerDensity c S k) :=
        expect_powersetCard_powersetCard M hvM hσv (fun S => layerDensity c S k)

end SubsetSumL25
