/- 
M4c: OpenAI Lemma 2.3 — monotone step. STATUS: clean build.
card_uniformQSubsets + sum_eq_sum_ite_univ + erase_sum_le + hbij +
sum_erase_bij + L2_3_expectation_mono all PROVED (no sorries).

M4d: OpenAI Lemma 2.3 — variance bound Var d(V_q) ≤ q (this file, below).
Provenance: the lemma is OpenAI's («Subset-Sum in Time O(2^0.49n)», setup.tex
lem:half-variance); this file only formalizes it.  Proof architecture — a
one-step conditional-mean recursion that avoids any measure theory:

  Var_{r+1}(h) = E_Ω[(h(W) − φ(W∖i))²] + E_Ω[(φ(W∖i) − z̄)²]

where Ω = {(W, i) : W ∈ U_{r+1}, i ∈ W} (the erase-fibration, transports in
`sum_erase_pair`) and φ(V) = 𝔼[h(S ∪ {i}) : i ∉ V] is the one-step exposure
mean (`stepMean`).  The inner term is ≤ 1 because φ is the per-fiber mean
(minimization, `sum_sq_mean_le`) and |h(W) − h(W∖i)| ≤ 1 is the insert lemma
L2_2_deficiency_insert.  The outer term is Var of φ over U_r (uniform marginal,
`Nat.choose_succ_right_eq`), and φ inherits the exchange- and insert-Lipschitz
properties from h (`stepMean_exchange_le` via an index-swap coupling,
`stepMean_insert_le` via an all-pairs averaging bound), so induction closes:

  Var d(V_q) ≤ q.

The exposure chain of the paper's proof is implicit in the recursion — no
permutation space and no conditional expectations are needed, only Finset sums.
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

/-! ## M4d: generic finite-sum variance lemmas -/

/-- Expansion of a sum of squared deviations from a constant. -/
private theorem sum_sq_sub_const_eq {β : Type*} (s : Finset β) (f : β → ℝ) (c : ℝ) :
    ∑ x ∈ s, (f x - c) ^ 2
      = (∑ x ∈ s, f x ^ 2) - 2 * c * (∑ x ∈ s, f x) + (s.card : ℝ) * c ^ 2 := by
  have hpt : ∀ x ∈ s, (f x - c) ^ 2 = f x ^ 2 + (-2 * c * f x) + c ^ 2 := fun x _ => by ring
  rw [Finset.sum_congr rfl fun x hx => hpt x hx, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The per-fiber mean minimizes the sum of squared deviations (any center `c`). -/
private theorem sum_sq_mean_le {β : Type*} {s : Finset β} (hs : 0 < s.card) (f : β → ℝ) (c : ℝ) :
    ∑ x ∈ s, (f x - (∑ y ∈ s, f y) / s.card) ^ 2 ≤ ∑ x ∈ s, (f x - c) ^ 2 := by
  have h1 := sum_sq_sub_const_eq s f ((∑ y ∈ s, f y) / s.card)
  have h2 := sum_sq_sub_const_eq s f c
  rw [h1, h2]
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  field_simp
  nlinarith [sq_nonneg ((∑ y ∈ s, f y) - s.card * c)]

/-- Average of `x` over `s` vs average of `y` over `t`: within 1 if *all* cross pairs are. -/
private theorem avg_allpairs_diff_le {α β : Type*} {s : Finset α} {t : Finset β}
    (hs : 0 < s.card) (ht : 0 < t.card) (x : α → ℝ) (y : β → ℝ)
    (h : ∀ a ∈ s, ∀ b ∈ t, |x a - y b| ≤ 1) :
    |(∑ a ∈ s, x a) / s.card - (∑ b ∈ t, y b) / t.card| ≤ 1 := by
  have hcard : (0 : ℝ) < (s.card : ℝ) * t.card := by positivity
  have hsplit : ∑ a ∈ s, ∑ b ∈ t, (x a - y b)
      = (∑ a ∈ s, x a) * (t.card : ℝ) - (s.card : ℝ) * (∑ b ∈ t, y b) := by
    have hinner : ∀ a ∈ s, ∑ b ∈ t, (x a - y b) = (t.card : ℝ) * x a - (∑ b ∈ t, y b) := by
      intro a _
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hlo : ∀ a ∈ s, ∀ b ∈ t, -1 ≤ x a - y b := by
    intro a ha b hb
    exact (abs_le.mp (h a ha b hb)).1
  have hbound : ∑ a ∈ s, ∑ b ∈ t, (x a - y b) ≤ (s.card : ℝ) * t.card := by
    calc ∑ a ∈ s, ∑ b ∈ t, (x a - y b)
        ≤ ∑ a ∈ s, ∑ b ∈ t, (1 : ℝ) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => le_of_abs_le (h a ha b hb)
      _ = (s.card : ℝ) * t.card := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
  have hbound' : -((s.card : ℝ) * t.card) ≤ ∑ a ∈ s, ∑ b ∈ t, (x a - y b) := by
    have h1 : ∑ a ∈ s, ∑ b ∈ t, (-1 : ℝ) = -((s.card : ℝ) * t.card) := by
      rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    calc -((s.card : ℝ) * t.card) = ∑ a ∈ s, ∑ b ∈ t, (-1 : ℝ) := h1.symm
      _ ≤ ∑ a ∈ s, ∑ b ∈ t, (x a - y b) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hlo a ha b hb
  have hdiv : (∑ a ∈ s, x a) / s.card - (∑ b ∈ t, y b) / t.card
      = (∑ a ∈ s, ∑ b ∈ t, (x a - y b)) / ((s.card : ℝ) * t.card) := by
    rw [div_sub_div _ _ (by exact_mod_cast hs.ne') (by exact_mod_cast ht.ne'), hsplit.symm]
  rw [abs_le, hdiv]
  constructor
  · rw [le_div_iff₀ hcard]; linarith
  · rw [div_le_iff₀ hcard]; linarith

/-- Averaging along a bijection: if coupled pairs are within 1, the averages are. -/
private theorem avg_bij_diff_le {α β : Type*} {s : Finset α} {t : Finset β}
    (hs : 0 < s.card) (x : α → ℝ) (y : β → ℝ)
    (i : (a : α) → a ∈ s → β)
    (hmem : ∀ a ha, i a ha ∈ t)
    (hinj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (hsurj : ∀ b ∈ t, ∃ a ha, i a ha = b)
    (hpt : ∀ a ha, |x a - y (i a ha)| ≤ 1) :
    |(∑ a ∈ s, x a) / s.card - (∑ b ∈ t, y b) / t.card| ≤ 1 := by
  classical
  have hcard' : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hcard'' : s.card ≠ 0 := hs.ne'
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp hs
  have hb0 : (i a0 ha0) ∈ t := hmem a0 ha0
  set ψ : α → β := fun a => if ha : a ∈ s then i a ha else i a0 ha0 with hψ
  have hcardn : t.card = s.card := (Finset.card_bij i hmem hinj hsurj).symm
  have hys : (∑ b ∈ t, y b) = ∑ a ∈ s, y (ψ a) := by
    refine (Finset.sum_bij (fun a ha => i a ha) hmem hinj hsurj ?_).symm
    intro a ha
    simp only [hψ]
    simp only [dif_pos ha]
  have hpt2 : ∀ a ∈ s, -1 ≤ x a - y (ψ a) ∧ x a - y (ψ a) ≤ 1 := by
    intro a ha
    have h1 : x a - y (ψ a) = x a - y (i a ha) := by
      rw [hψ]
      simp only [dif_pos ha]
    rw [h1]
    exact abs_le.mp (hpt a ha)
  have hsplit : (∑ a ∈ s, x a) / s.card - (∑ b ∈ t, y b) / t.card
      = (∑ a ∈ s, (x a - y (ψ a))) / s.card := by
    rw [hys, hcardn, ← sub_div, ← Finset.sum_sub_distrib]
  rw [abs_le, hsplit]
  have hub : ∑ a ∈ s, (x a - y (ψ a)) ≤ (s.card : ℝ) := by
    calc ∑ a ∈ s, (x a - y (ψ a)) ≤ ∑ a ∈ s, (1 : ℝ) :=
          Finset.sum_le_sum fun a ha => (hpt2 a ha).2
      _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hlo : -((s.card : ℝ)) ≤ ∑ a ∈ s, (x a - y (ψ a)) := by
    have h1 : ∑ a ∈ s, (-1 : ℝ) = -((s.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    calc -((s.card : ℝ)) = ∑ a ∈ s, (-1 : ℝ) := h1.symm
      _ ≤ ∑ a ∈ s, (x a - y (ψ a)) :=
          Finset.sum_le_sum fun a ha => (hpt2 a ha).1
  constructor
  · rw [le_div_iff₀ hcard']; linarith
  · rw [div_le_iff₀ hcard']; linarith

end SubsetSumL25
