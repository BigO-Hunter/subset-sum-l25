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

end SubsetSumL25
