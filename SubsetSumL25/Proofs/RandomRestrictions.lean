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
the file context (works standalone); the workaround
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

/-! ## M4d: the fiber / step-mean layer -/

/-- Finite two-level law of total variance: the squared deviation from the
global mean splits into within-fiber deviations from the fiber mean plus the
fiber-mean deviations from the global mean (exact identity, counting measure). -/
private theorem total_variance_finset {α β : Type*} [DecidableEq α] (s : Finset α)
    (t : α → Finset β) (hne : ∀ a ∈ s, (t a).Nonempty) (z : α → β → ℝ) :
    ∑ a ∈ s, ∑ b ∈ t a, (z a b - (∑ a' ∈ s, ∑ b' ∈ t a', z a' b') /
        ((∑ a' ∈ s, (t a').card : ℕ) : ℝ)) ^ 2
      = ∑ a ∈ s, ∑ b ∈ t a, (z a b - (∑ b' ∈ t a, z a b') / ((t a).card : ℝ)) ^ 2
        + ∑ a ∈ s, ((t a).card : ℝ) *
            ((∑ b' ∈ t a, z a b') / ((t a).card : ℝ) -
              (∑ a' ∈ s, ∑ b' ∈ t a', z a' b') / ((∑ a' ∈ s, (t a').card : ℕ) : ℝ)) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty s with hE | hNE
  · subst hE
    simp
  · set N : ℝ := (((∑ a ∈ s, (t a).card : ℕ)) : ℝ) with hNdef
    set Z : ℝ := ∑ a ∈ s, ∑ b ∈ t a, z a b with hZdef
    have hsumn : N = ∑ a ∈ s, ((t a).card : ℝ) := by
      rw [hNdef]; exact Nat.cast_sum s (fun a => (t a).card)
    have hNpos : 0 < N := by
      rw [hsumn]
      refine Finset.sum_pos' (fun a _ => by positivity) ⟨hNE.choose, hNE.choose_spec, ?_⟩
      have hc := (hne hNE.choose hNE.choose_spec).card_pos
      exact_mod_cast hc
    have hNa : ∀ a ∈ s, (0 : ℝ) < ((t a).card : ℝ) := by
      intro a ha
      exact_mod_cast (hne a ha).card_pos
    have e1 : ∑ a ∈ s, ∑ b ∈ t a, (z a b - Z / N) ^ 2
        = (∑ a ∈ s, ∑ b ∈ t a, (z a b) ^ 2) - Z ^ 2 / N := by
      have per : ∀ a ∈ s, ∑ b ∈ t a, (z a b - Z / N) ^ 2
          = (∑ b ∈ t a, (z a b) ^ 2) - 2 * (Z / N) * (∑ b ∈ t a, z a b)
            + ((t a).card : ℝ) * (Z / N) ^ 2 :=
        fun a _ => sum_sq_sub_const_eq (t a) (fun b => z a b) (Z / N)
      rw [Finset.sum_congr rfl per, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hZdef.symm, ← hsumn]
      have h2 : 2 * (Z / N) * Z = 2 * Z ^ 2 / N := by field_simp [hNpos.ne']
      have h3 : N * (Z / N) ^ 2 = Z ^ 2 / N := by field_simp [hNpos.ne']
      rw [h2, h3]
      ring
    have e2 : ∑ a ∈ s, ∑ b ∈ t a, (z a b - (∑ b' ∈ t a, z a b') / ((t a).card : ℝ)) ^ 2
        = (∑ a ∈ s, ∑ b ∈ t a, (z a b) ^ 2)
          - ∑ a ∈ s, ((∑ b' ∈ t a, z a b') ^ 2 / ((t a).card : ℝ)) := by
      have per : ∀ a ∈ s, ∑ b ∈ t a, (z a b - (∑ b' ∈ t a, z a b') / ((t a).card : ℝ)) ^ 2
          = (∑ b ∈ t a, (z a b) ^ 2) - ((∑ b' ∈ t a, z a b') ^ 2 / ((t a).card : ℝ)) := by
        intro a ha
        have h := sum_sq_sub_const_eq (t a) (fun b => z a b)
          ((∑ b' ∈ t a, z a b') / ((t a).card : ℝ))
        rw [h]
        field_simp
        ring
      rw [Finset.sum_congr rfl per, Finset.sum_sub_distrib]
    have e3 : ∑ a ∈ s, ((t a).card : ℝ) *
        ((∑ b' ∈ t a, z a b') / ((t a).card : ℝ) - Z / N) ^ 2
        = ∑ a ∈ s, ((∑ b' ∈ t a, z a b') ^ 2 / ((t a).card : ℝ)) - Z ^ 2 / N := by
      have per : ∀ a ∈ s, ((t a).card : ℝ) *
          ((∑ b' ∈ t a, z a b') / ((t a).card : ℝ) - Z / N) ^ 2
          = ((∑ b' ∈ t a, z a b') ^ 2 / ((t a).card : ℝ))
            - 2 * (Z / N) * (∑ b' ∈ t a, z a b') + ((t a).card : ℝ) * (Z / N) ^ 2 := by
        intro a ha
        have hc := hNa a ha
        field_simp
        ring
      rw [Finset.sum_congr rfl per, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hZdef.symm, ← hsumn]
      have h2 : 2 * (Z / N) * Z = 2 * Z ^ 2 / N := by field_simp [hNpos.ne']
      have h3 : N * (Z / N) ^ 2 = Z ^ 2 / N := by field_simp [hNpos.ne']
      rw [h2, h3]
      ring
    rw [e1, e2, e3]
    ring

/-- One-step exposure mean: the average of `h (S ∪ {i})` over uniform `i ∉ S`. -/
private noncomputable def stepMean {n : ℕ} (h : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  (Finset.univ \ S).expect (fun i => h (insert i S))

private theorem stepMean_eq_div {n : ℕ} (h : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    stepMean h S = (∑ i ∈ Finset.univ \ S, h (insert i S)) / ((n - S.card : ℕ) : ℝ) := by
  rw [stepMean, Finset.expect_eq_sum_div_card,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

/-- Leave-one-out averaging bound: if each `a k` is within 1 of both `b k` and
the extra value `c`, then the average of `a` and the augmented average of `b`
with the extra term `c` differ by at most 1. -/
private theorem avg_augment_le_one {β : Type*} {s : Finset β} (hs : 0 < s.card)
    (a b : β → ℝ) (c : ℝ)
    (h1 : ∀ k ∈ s, |a k - b k| ≤ 1) (h2 : ∀ k ∈ s, |a k - c| ≤ 1) :
    |(∑ k ∈ s, a k) / s.card - (c + ∑ k ∈ s, b k) / ((s.card : ℝ) + 1)| ≤ 1 := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hkey : ((s.card : ℝ) * ((s.card : ℝ) + 1)) *
      ((∑ k ∈ s, a k) / s.card - (c + ∑ k ∈ s, b k) / ((s.card : ℝ) + 1))
      = (s.card : ℝ) * (∑ k ∈ s, (a k - b k)) + ∑ k ∈ s, (a k - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring
  have hb1 : |∑ k ∈ s, (a k - b k)| ≤ (s.card : ℝ) := by
    have hub : ∑ k ∈ s, (a k - b k) ≤ (s.card : ℝ) := by
      calc ∑ k ∈ s, (a k - b k) ≤ ∑ k ∈ s, (1 : ℝ) :=
            Finset.sum_le_sum fun k hk => (abs_le.mp (h1 k hk)).2
        _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hlb : -((s.card : ℝ)) ≤ ∑ k ∈ s, (a k - b k) := by
      have hone : ∑ k ∈ s, (-1 : ℝ) = -((s.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      calc -((s.card : ℝ)) = ∑ k ∈ s, (-1 : ℝ) := hone.symm
        _ ≤ ∑ k ∈ s, (a k - b k) :=
            Finset.sum_le_sum fun k hk => (abs_le.mp (h1 k hk)).1
    rw [abs_le]; exact ⟨hlb, hub⟩
  have hb2 : |∑ k ∈ s, (a k - c)| ≤ (s.card : ℝ) := by
    have hub : ∑ k ∈ s, (a k - c) ≤ (s.card : ℝ) := by
      calc ∑ k ∈ s, (a k - c) ≤ ∑ k ∈ s, (1 : ℝ) :=
            Finset.sum_le_sum fun k hk => (abs_le.mp (h2 k hk)).2
        _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hlb : -((s.card : ℝ)) ≤ ∑ k ∈ s, (a k - c) := by
      have hone : ∑ k ∈ s, (-1 : ℝ) = -((s.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      calc -((s.card : ℝ)) = ∑ k ∈ s, (-1 : ℝ) := hone.symm
        _ ≤ ∑ k ∈ s, (a k - c) :=
            Finset.sum_le_sum fun k hk => (abs_le.mp (h2 k hk)).1
    rw [abs_le]; exact ⟨hlb, hub⟩
  have hpos : (0 : ℝ) < (s.card : ℝ) * ((s.card : ℝ) + 1) := by positivity
  have hmul : |(∑ k ∈ s, a k) / s.card - (c + ∑ k ∈ s, b k) / ((s.card : ℝ) + 1)|
      * ((s.card : ℝ) * ((s.card : ℝ) + 1)) ≤ 1 * ((s.card : ℝ) * ((s.card : ℝ) + 1)) := by
    have habs : |((s.card : ℝ) * ((s.card : ℝ) + 1)) *
        ((∑ k ∈ s, a k) / s.card - (c + ∑ k ∈ s, b k) / ((s.card : ℝ) + 1))|
        = |(∑ k ∈ s, a k) / s.card - (c + ∑ k ∈ s, b k) / ((s.card : ℝ) + 1)|
          * ((s.card : ℝ) * ((s.card : ℝ) + 1)) := by
      rw [abs_mul, abs_of_pos hpos, mul_comm]
    rw [← habs, hkey]
    calc |(s.card : ℝ) * (∑ k ∈ s, (a k - b k)) + ∑ k ∈ s, (a k - c)|
        ≤ |(s.card : ℝ) * (∑ k ∈ s, (a k - b k))| + |∑ k ∈ s, (a k - c)| := abs_add_le _ _
      _ = (s.card : ℝ) * |∑ k ∈ s, (a k - b k)| + |∑ k ∈ s, (a k - c)| := by
            rw [abs_mul, abs_of_pos hn]
      _ ≤ (s.card : ℝ) * s.card + s.card :=
            add_le_add (mul_le_mul_of_nonneg_left hb1 (le_of_lt hn)) hb2
      _ = 1 * ((s.card : ℝ) * ((s.card : ℝ) + 1)) := by ring
  exact le_of_mul_le_mul_right hmul hpos

/-- The one-step mean inherits the exchange-Lipschitz property. -/
private theorem stepMean_exchange_le {n : ℕ} (h : Finset (Fin n) → ℝ)
    (hEL : ∀ S : Finset (Fin n), S.card + 2 ≤ n → ∀ i j : Fin n, i ∉ S → j ∉ S → i ≠ j →
      |h (insert i S) - h (insert j S)| ≤ 1) :
    ∀ S : Finset (Fin n), S.card + 2 ≤ n → ∀ i j : Fin n, i ∉ S → j ∉ S → i ≠ j →
      |stepMean h (insert i S) - stepMean h (insert j S)| ≤ 1 := by
  intro S hS i j hi hj hij
  have hcard_i : (Finset.univ \ insert i S).card = n - (S.card + 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hi]
  have hcard_j : (Finset.univ \ insert j S).card = n - (S.card + 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hj]
  have hne_i : 0 < (Finset.univ \ insert i S).card := by
    rw [hcard_i]; omega
  have hden_i : ((n - (insert i S).card : ℕ) : ℝ) = (((Finset.univ \ insert i S).card : ℕ) : ℝ) := by
    rw [Finset.card_insert_of_notMem hi]
    exact congrArg _ hcard_i.symm
  have hden_j : ((n - (insert j S).card : ℕ) : ℝ) = (((Finset.univ \ insert j S).card : ℕ) : ℝ) := by
    rw [Finset.card_insert_of_notMem hj]
    exact congrArg _ hcard_j.symm
  rw [stepMean_eq_div, stepMean_eq_div, hden_i, hden_j]
  refine avg_bij_diff_le hne_i (fun k => h (insert k (insert i S)))
    (fun k' => h (insert k' (insert j S))) (fun k _ => if k = j then i else k) ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨_, hknot⟩ := Finset.mem_sdiff.mp hk
    rw [Finset.mem_insert] at hknot
    have hkS : k ∉ S := fun h => hknot (Or.inr h)
    by_cases hkj : k = j
    · rw [if_pos hkj, Finset.mem_sdiff, Finset.mem_insert]
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro (h | h)
      · exact hij h
      · exact hi h
    · rw [if_neg hkj, Finset.mem_sdiff, Finset.mem_insert]
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro (h | h)
      · exact hkj h
      · exact hkS h
  · intro k₁ hk₁ k₂ hk₂ heq
    have hk₁' : k₁ ∉ insert i S := (Finset.mem_sdiff.mp hk₁).2
    have hk₂' : k₂ ∉ insert i S := (Finset.mem_sdiff.mp hk₂).2
    by_cases h1 : k₁ = j
    · by_cases h2 : k₂ = j
      · rw [h1, h2]
      · rw [if_pos h1, if_neg h2] at heq
        exact absurd (heq.symm ▸ Finset.mem_insert_self i S) hk₂'
    · by_cases h2 : k₂ = j
      · rw [if_neg h1, if_pos h2] at heq
        exact absurd (heq ▸ Finset.mem_insert_self i S) hk₁'
      · rw [if_neg h1, if_neg h2] at heq
        exact heq
  · intro k' hk'
    obtain ⟨_, hk'not⟩ := Finset.mem_sdiff.mp hk'
    rw [Finset.mem_insert] at hk'not
    have hk'S : k' ∉ S := fun h => hk'not (Or.inr h)
    have hk'j : k' ≠ j := fun h => hk'not (Or.inl h)
    by_cases hk'i : k' = i
    · refine ⟨j, ?_, ?_⟩
      · rw [Finset.mem_sdiff, Finset.mem_insert]
        refine ⟨Finset.mem_univ _, ?_⟩
        rintro (h | h)
        · exact hij h.symm
        · exact hj h
      · rw [if_pos rfl]
        exact hk'i.symm
    · refine ⟨k', ?_, ?_⟩
      · rw [Finset.mem_sdiff, Finset.mem_insert]
        refine ⟨Finset.mem_univ _, ?_⟩
        rintro (h | h)
        · exact hk'i h
        · exact hk'S h
      · rw [if_neg hk'j]
  · intro k hk
    obtain ⟨_, hknot⟩ := Finset.mem_sdiff.mp hk
    rw [Finset.mem_insert] at hknot
    have hkS : k ∉ S := fun h => hknot (Or.inr h)
    have hki : k ≠ i := fun h => hknot (Or.inl h)
    by_cases hkj : k = j
    · rw [if_pos hkj]
      have heqset : insert k (insert i S) = insert i (insert j S) := by
        rw [hkj]; exact Finset.insert_comm j i S
      rw [heqset, sub_self, abs_zero]
      norm_num
    · rw [if_neg hkj]
      have hkk : S.card + 3 ≤ n := by
        by_contra hcon
        have h2 : S.card + 2 = n := by omega
        have hSset : (Finset.univ \ insert i S).card = 1 := by rw [hcard_i]; omega
        have hjmem : j ∈ Finset.univ \ insert i S := by
          rw [Finset.mem_sdiff, Finset.mem_insert]
          refine ⟨Finset.mem_univ _, ?_⟩
          rintro (h | h)
          · exact hij h.symm
          · exact hj h
        exact hkj (Finset.card_le_one_iff.mp (le_of_eq hSset) hk hjmem)
      have hkk' : (insert k S).card + 2 ≤ n := by
        rw [Finset.card_insert_of_notMem hkS]; omega
      have hEL' := hEL (insert k S) hkk' i j ?_ ?_ hij
      · have h1 : insert k (insert i S) = insert i (insert k S) :=
          (Finset.insert_comm i k S).symm
        have h2 : insert k (insert j S) = insert j (insert k S) :=
          (Finset.insert_comm j k S).symm
        rwa [h1, h2]
      · rw [Finset.mem_insert]
        rintro (h | h)
        · exact hki h.symm
        · exact hi h
      · rw [Finset.mem_insert]
        rintro (h | h)
        · exact hkj h.symm
        · exact hj h

/-- The one-step mean inherits the insert-Lipschitz property, with the depth
`d` decremented by one (the exposure recursion consumes one level). -/
private theorem stepMean_insert_le {n : ℕ} (h : Finset (Fin n) → ℝ) (d : ℕ) (hd : d ≤ n)
    (hIL : ∀ S : Finset (Fin n), S.card + 1 ≤ d → ∀ i : Fin n, i ∉ S →
      |h (insert i S) - h S| ≤ 1) :
    ∀ S : Finset (Fin n), S.card + 1 ≤ d - 1 → ∀ i : Fin n, i ∉ S →
      |stepMean h (insert i S) - stepMean h S| ≤ 1 := by
  intro S hS i hi
  have hcardA : (Finset.univ \ insert i S).card = n - (S.card + 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hi]
  have hn1 : 0 < (Finset.univ \ insert i S).card := by rw [hcardA]; omega
  have hia : i ∉ Finset.univ \ insert i S := fun h =>
    (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self i S)
  have hsplit : Finset.univ \ S = insert i (Finset.univ \ insert i S) :=
    (Finset.sdiff_insert_insert_of_mem_of_notMem (Finset.mem_univ i) hi).symm
  have hdeni : ((n - (insert i S).card : ℕ) : ℝ) = (((Finset.univ \ insert i S).card : ℕ) : ℝ) := by
    rw [Finset.card_insert_of_notMem hi]
    exact congrArg _ hcardA.symm
  have hdenS : ((n - S.card : ℕ) : ℝ) = (((Finset.univ \ S).card : ℕ) : ℝ) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  rw [stepMean_eq_div, stepMean_eq_div, hdeni, hdenS, hsplit,
    Finset.sum_insert hia, Finset.card_insert_of_notMem hia, Nat.cast_add, Nat.cast_one]
  refine avg_augment_le_one hn1 (fun k => h (insert k (insert i S))) (fun k => h (insert k S))
    (h (insert i S)) ?_ ?_
  · intro k hk
    obtain ⟨_, hknot⟩ := Finset.mem_sdiff.mp hk
    rw [Finset.mem_insert] at hknot
    have hki : k ≠ i := fun h => hknot (Or.inl h)
    have hkS : k ∉ S := fun h => hknot (Or.inr h)
    have hci : (insert k S).card + 1 ≤ d := by
      rw [Finset.card_insert_of_notMem hkS]; omega
    have hh := hIL (insert k S) hci i ?_
    · have h1 : insert k (insert i S) = insert i (insert k S) :=
        (Finset.insert_comm i k S).symm
      rwa [h1]
    · rw [Finset.mem_insert]
      rintro (h | h)
      · exact hki h.symm
      · exact hi h
  · intro k hk
    have hkk : k ∉ insert i S := (Finset.mem_sdiff.mp hk).2
    have hci : (insert i S).card + 1 ≤ d := by
      rw [Finset.card_insert_of_notMem hi]; omega
    exact hIL (insert i S) hci k hkk

/-! ## M4d: the erase-fibration transport and the variance recursion -/

/-- Pair-level transport `(W, i ∈ W) ↔ (V, i ∉ V)` with `V = W ∖ {i}`. -/
private theorem sum_erase_pair {n : ℕ} (F : Finset (Fin n) → Fin n → ℝ) (r : ℕ) :
    ∑ W ∈ uniformQSubsets n (r + 1), ∑ i ∈ W, F W i
      = ∑ V ∈ uniformQSubsets n r, ∑ i ∈ Finset.univ \ V, F (insert i V) i := by
  have hswap1 : ∑ W ∈ uniformQSubsets n (r + 1), ∑ i ∈ W, F W i
      = ∑ i ∈ Finset.univ,
          ∑ W ∈ (uniformQSubsets n (r + 1)).filter (fun W => i ∈ W), F W i :=
    Finset.sum_comm' fun W i => by
      constructor
      · intro h
        exact ⟨Finset.mem_filter.mpr h, Finset.mem_univ _⟩
      · intro h
        exact Finset.mem_filter.mp h.1
  have hswap2 : ∑ i ∈ Finset.univ,
        ∑ V ∈ (uniformQSubsets n r).filter (fun V => i ∉ V), F (insert i V) i
      = ∑ V ∈ uniformQSubsets n r, ∑ i ∈ Finset.univ \ V, F (insert i V) i :=
    Finset.sum_comm' fun i V => by
      constructor
      · intro h
        exact ⟨Finset.mem_sdiff.mpr ⟨h.1, (Finset.mem_filter.mp h.2).2⟩,
          (Finset.mem_filter.mp h.2).1⟩
      · intro h
        exact ⟨(Finset.mem_sdiff.mp h.1).1,
          Finset.mem_filter.mpr ⟨h.2, (Finset.mem_sdiff.mp h.1).2⟩⟩
  rw [hswap1, ← hswap2]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_bij (fun W _ => W.erase i) ?_ ?_ ?_ ?_
  · intro W hW
    obtain ⟨hW1, hin⟩ := Finset.mem_filter.mp hW
    obtain ⟨_, hWq⟩ := Finset.mem_filter.mp hW1
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.notMem_erase i W⟩
    rw [Finset.card_erase_of_mem hin, hWq]
    omega
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
          by rw [Finset.card_insert_of_notMem hjV, hVq]⟩, Finset.mem_insert_self i V⟩
    · exact Finset.erase_insert hjV
  · intro W hW
    show F W i = F (insert i (W.erase i)) i
    rw [Finset.insert_erase (Finset.mem_filter.mp hW).2]

/-- One exhaustion step of the exposure recursion: the variance at level
`r + 1` is at most 1 plus the variance of the one-step mean at level `r`. -/
private theorem var_step {n : ℕ} (h : Finset (Fin n) → ℝ) (r : ℕ) (hr : r + 2 ≤ n)
    (hEL : ∀ S : Finset (Fin n), S.card + 2 ≤ n → ∀ i j : Fin n, i ∉ S → j ∉ S → i ≠ j →
      |h (insert i S) - h (insert j S)| ≤ 1)
    (hIL : ∀ S : Finset (Fin n), S.card + 1 ≤ r + 1 → ∀ i : Fin n, i ∉ S →
      |h (insert i S) - h S| ≤ 1)
    (hind : (uniformQSubsets n r).expect
        (fun V => (stepMean h V - (uniformQSubsets n r).expect (stepMean h)) ^ 2) ≤ (r : ℝ)) :
    (uniformQSubsets n (r + 1)).expect
        (fun W => (h W - (uniformQSubsets n (r + 1)).expect h) ^ 2) ≤ ((r + 1 : ℕ) : ℝ) := by
  classical
  set U1 := uniformQSubsets n (r + 1) with hU1
  set U0 := uniformQSubsets n r with hU0
  have hc1 : U1.card = Nat.choose n (r + 1) := card_uniformQSubsets n (r + 1)
  have hc0 : U0.card = Nat.choose n r := card_uniformQSubsets n r
  have hc1r : (0 : ℝ) < (U1.card : ℝ) := by
    rw [hc1]; exact_mod_cast Nat.choose_pos (by omega)
  have hc0r : (0 : ℝ) < (U0.card : ℝ) := by
    rw [hc0]; exact_mod_cast Nat.choose_pos (by omega)
  have hne : ∀ V ∈ U0, (Finset.univ \ V).Nonempty := by
    intro V hV
    refine Finset.card_pos.mp ?_
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      (Finset.mem_filter.mp hV).2]
    omega
  have hcardV : ∀ V ∈ U0, (Finset.univ \ V).card = n - r := by
    intro V hV
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      (Finset.mem_filter.mp hV).2]
  -- the counting identity ∑_V #(univ∖V) = (r+1)·#U1 = (n−r)·#U0
  set Ntot : ℝ := ((∑ V ∈ U0, (Finset.univ \ V).card : ℕ) : ℝ) with hNtotdef
  have hNtot2 : Ntot = ((n - r : ℕ) : ℝ) * ((U0.card : ℕ) : ℝ) := by
    rw [hNtotdef]
    rw [Finset.sum_congr rfl (fun V hV => hcardV V hV), Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  have hchr : ((Nat.choose n (r + 1) : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ)
      = ((Nat.choose n r : ℕ) : ℝ) * ((n - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n r
  have hNtot1 : Ntot = ((r + 1 : ℕ) : ℝ) * ((U1.card : ℕ) : ℝ) := by
    rw [hNtot2, hc0, hc1]
    nlinarith [hchr]
  have hNtotpos : 0 < Ntot := by
    rw [hNtot1]
    exact mul_pos (by positivity) hc1r
  set μ : ℝ := (∑ W ∈ U1, h W) / ((U1.card : ℕ) : ℝ) with hμdef
  set zbar : ℝ := (∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, h (insert i V))
    / ((∑ V ∈ U0, (Finset.univ \ V).card : ℕ) : ℝ) with hzdef
  -- T2: level-(r+1) sum against the pair sum
  have hT2gen : ∀ x : Finset (Fin n) → ℝ,
      ∑ W ∈ U1, ∑ i ∈ W, x W = ((r + 1 : ℕ) : ℝ) * ∑ W ∈ U1, x W := by
    intro x
    have per : ∀ W ∈ U1, ∑ i ∈ W, x W = ((W.card : ℕ) : ℝ) * x W := by
      intro W _
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl per]
    have hcard : ∀ W ∈ U1, W.card = r + 1 := fun W hW => (Finset.mem_filter.mp hW).2
    rw [Finset.sum_congr rfl (fun W hW => by rw [hcard W hW]), ← Finset.mul_sum]
  have hnum : ∀ c : ℝ, ∑ W ∈ U1, (h W - c) ^ 2
      = (1 / ((r + 1 : ℕ) : ℝ)) *
          ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - c) ^ 2 := by
    intro c
    have h2 := hT2gen (fun W => (h W - c) ^ 2)
    have h3 := sum_erase_pair (fun W _ => (h W - c) ^ 2) r
    rw [h3] at h2
    rw [h2]
    field_simp
  -- variance in transport form
  have hVar : U1.expect (fun W => (h W - U1.expect h) ^ 2)
      = (∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - μ) ^ 2) / Ntot := by
    rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
    rw [hnum μ, hNtot1]
    have hr1 : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hc1r.ne', hr1]
  -- the fiber mean is stepMean
  have hfiber : ∀ V ∈ U0, (∑ i ∈ Finset.univ \ V, h (insert i V))
      / ((Finset.univ \ V).card : ℝ) = stepMean h V := by
    intro V hV
    rw [stepMean, Finset.expect_eq_sum_div_card]
  -- zbar = μ, and μ is the U0-mean of the fiber means
  have hzbar_μ : zbar = μ := by
    have hnum2 : ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, h (insert i V)
        = ((r + 1 : ℕ) : ℝ) * ∑ W ∈ U1, h W := by
      rw [← sum_erase_pair (fun W _ => h W) r, hT2gen h]
    rw [hzdef, hμdef, hnum2, ← hNtotdef, hNtot1]
    have hr1 : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hc1r.ne', hr1]
  have hphi_mean : μ = (∑ V ∈ U0, stepMean h V) / ((U0.card : ℕ) : ℝ) := by
    have hsum_phi : ∑ V ∈ U0, stepMean h V
        = (∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, h (insert i V)) / ((n - r : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun V hV => ?_
      rw [stepMean, Finset.expect_eq_sum_div_card, hcardV V hV]
    have hnum2 : ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, h (insert i V)
        = ((r + 1 : ℕ) : ℝ) * ∑ W ∈ U1, h W := by
      rw [← sum_erase_pair (fun W _ => h W) r, hT2gen h]
    have hnr : ((n - r : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n - r := by omega
      exact_mod_cast this.ne'
    have hrel : ((r + 1 : ℕ) : ℝ) * ((U1.card : ℕ) : ℝ)
        = ((n - r : ℕ) : ℝ) * ((U0.card : ℕ) : ℝ) := by
      rw [← hNtot1, ← hNtot2]
    rw [hsum_phi, hnum2, hμdef, div_div]
    refine (div_eq_div_iff hc1r.ne' (mul_ne_zero hnr hc0r.ne')).mpr ?_
    calc (∑ W ∈ U1, h W) * (((n - r : ℕ) : ℝ) * ((U0.card : ℕ) : ℝ))
        = (∑ W ∈ U1, h W) * (((r + 1 : ℕ) : ℝ) * ((U1.card : ℕ) : ℝ)) := by rw [hrel]
      _ = ((r + 1 : ℕ) : ℝ) * (∑ W ∈ U1, h W) * ((U1.card : ℕ) : ℝ) := by ring
  -- total-variance identity with the two pieces
  have hG2 := total_variance_finset U0 (fun V => Finset.univ \ V) hne
    (fun V i => h (insert i V))
  have hconv : ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V,
        (h (insert i V) - (∑ i' ∈ Finset.univ \ V, h (insert i' V))
          / ((Finset.univ \ V).card : ℝ)) ^ 2
      = ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - stepMean h V) ^ 2 := by
    refine Finset.sum_congr rfl fun V hV => Finset.sum_congr rfl fun i _ => ?_
    rw [hfiber V hV]
  rw [hconv] at hG2
  have hconv2 : ∑ a ∈ U0, ((Finset.univ \ a).card : ℝ) *
        ((∑ b' ∈ Finset.univ \ a, h (insert b' a)) / ((Finset.univ \ a).card : ℝ) - zbar) ^ 2
      = ∑ a ∈ U0, ((Finset.univ \ a).card : ℝ) * (stepMean h a - zbar) ^ 2 := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hfiber a ha]
  rw [hconv2] at hG2
  -- inner bound
  have hInner : ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - stepMean h V) ^ 2
      ≤ Ntot := by
    have per : ∀ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - stepMean h V) ^ 2
        ≤ ((Finset.univ \ V).card : ℝ) := by
      intro V hV
      have hneV : 0 < (Finset.univ \ V).card := Finset.card_pos.mpr (hne V hV)
      have h1 := sum_sq_mean_le hneV (fun i => h (insert i V)) (h V)
      rw [hfiber V hV] at h1
      have h2 : ∑ i ∈ Finset.univ \ V, (h (insert i V) - h V) ^ 2
          ≤ ((Finset.univ \ V).card : ℝ) := by
        calc ∑ i ∈ Finset.univ \ V, (h (insert i V) - h V) ^ 2
            ≤ ∑ i ∈ Finset.univ \ V, (1 : ℝ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hb := hIL V (by rw [(Finset.mem_filter.mp hV).2]) i
                (Finset.mem_sdiff.mp hi).2
              nlinarith [abs_le.mp hb]
          _ = ((Finset.univ \ V).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact le_trans h1 h2
    calc ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - stepMean h V) ^ 2
        ≤ ∑ V ∈ U0, ((Finset.univ \ V).card : ℝ) := Finset.sum_le_sum per
      _ = Ntot := by rw [hNtotdef, ← Nat.cast_sum]
  -- outer bound
  have hOuter : ∑ V ∈ U0, ((Finset.univ \ V).card : ℝ) * (stepMean h V - zbar) ^ 2
      ≤ (r : ℝ) * Ntot := by
    have hzbar_mean : zbar = (∑ V ∈ U0, stepMean h V) / ((U0.card : ℕ) : ℝ) :=
      hzbar_μ.trans hphi_mean
    have hvard : ∑ V ∈ U0, (stepMean h V - zbar) ^ 2 ≤ (r : ℝ) * ((U0.card : ℕ) : ℝ) := by
      rw [hzbar_mean]
      have hv := hind
      rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
        div_le_iff₀ hc0r] at hv
      exact hv
    have huniform : ∀ V ∈ U0, ((Finset.univ \ V).card : ℝ) = ((n - r : ℕ) : ℝ) :=
      fun V hV => by rw [hcardV V hV]
    rw [Finset.sum_congr rfl (fun V hV => by rw [huniform V hV]), ← Finset.mul_sum]
    calc ((n - r : ℕ) : ℝ) * ∑ V ∈ U0, (stepMean h V - zbar) ^ 2
        ≤ ((n - r : ℕ) : ℝ) * ((r : ℝ) * ((U0.card : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hvard (by positivity)
      _ = (r : ℝ) * Ntot := by
          rw [hNtot2]
          ring
  -- assemble
  have hnum_bound : ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - μ) ^ 2
      ≤ ((r + 1 : ℕ) : ℝ) * Ntot := by
    have hZ : ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - μ) ^ 2
        = ∑ V ∈ U0, ∑ i ∈ Finset.univ \ V, (h (insert i V) - zbar) ^ 2 := by
      rw [hzbar_μ]
    rw [hZ, hG2]
    have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    nlinarith [hInner, hOuter, hcast]
  rw [hVar, div_le_iff₀ hNtotpos]
  exact hnum_bound

/-- OpenAI L2.3 exposure recursion: if `h` is exchange-Lipschitz and
insert-Lipschitz to depth `d`, then the variance of `h` over uniform
`r`-subsets is at most `r`, for every `r ≤ n, r ≤ d`. -/
private theorem martingale_var {n : ℕ} (h : Finset (Fin n) → ℝ) (d : ℕ)
    (hEL : ∀ S : Finset (Fin n), S.card + 2 ≤ n → ∀ i j : Fin n, i ∉ S → j ∉ S → i ≠ j →
      |h (insert i S) - h (insert j S)| ≤ 1)
    (hIL : ∀ S : Finset (Fin n), S.card + 1 ≤ d → ∀ i : Fin n, i ∉ S →
      |h (insert i S) - h S| ≤ 1) :
    ∀ r : ℕ, r ≤ n → r ≤ d →
      (uniformQSubsets n r).expect
        (fun V => (h V - (uniformQSubsets n r).expect h) ^ 2) ≤ (r : ℝ) := by
  have key : ∀ r : ℕ, r ≤ n → ∀ (g : Finset (Fin n) → ℝ) (e : ℕ), r ≤ e →
      (∀ S : Finset (Fin n), S.card + 2 ≤ n → ∀ i j : Fin n, i ∉ S → j ∉ S → i ≠ j →
        |g (insert i S) - g (insert j S)| ≤ 1) →
      (∀ S : Finset (Fin n), S.card + 1 ≤ e → ∀ i : Fin n, i ∉ S →
        |g (insert i S) - g S| ≤ 1) →
      (uniformQSubsets n r).expect
        (fun V => (g V - (uniformQSubsets n r).expect g) ^ 2) ≤ (r : ℝ) := by
    intro r
    induction r with
    | zero =>
      intro _ g _ _ _ _
      have hzero : uniformQSubsets n 0 = {∅} := by
        unfold uniformQSubsets
        ext V
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => Finset.card_eq_zero.mp h, fun h => by rw [h]; simp⟩
      rw [hzero, Finset.expect_singleton, Finset.expect_singleton]
      simp
    | succ r ih =>
      intro hrn g e hre hELg hILg
      rcases Nat.lt_or_ge (r + 1) n with hlt | hge
      · apply var_step g r (by omega) hELg
        · intro S hS i hi
          exact hILg S (by omega) i hi
        · exact ih (by omega) (stepMean g) r (le_refl r)
            (stepMean_exchange_le g hELg)
            (stepMean_insert_le g (r + 1) (by omega) (fun S hS i hi => hILg S (by omega) i hi))
      · have heq : r + 1 = n := by omega
        have hsing : uniformQSubsets n (r + 1) = {Finset.univ} := by
          unfold uniformQSubsets
          ext V
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h
            exact Finset.eq_univ_of_card V (by rw [h, Fintype.card_fin]; omega)
          · intro h
            rw [h, Finset.card_univ, Fintype.card_fin]
            omega
        rw [hsing, Finset.expect_singleton, Finset.expect_singleton, sub_self,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        positivity
  intro r hrn hrd
  exact key r hrn h d hrd hEL hIL

/-! ## M4d: OpenAI Lemma 2.3, the variance bound -/

/-- OpenAI L2.3 (`lem:half-variance`): `Var d(V_q) ≤ q` for the uniform
`q`-element random subset.  Provenance: OpenAI preprint «Subset-Sum in Time
O(2^0.49n)»; the proof here is the one-step conditional-mean recursion. -/
theorem L2_3_halfVariance {n : ℕ} (c : Fin n → ℤ) (q : ℕ) (hq : q ≤ n) :
    (uniformQSubsets n q).expect
        (fun V => (deficiency c V - expectedDeficiency c q) ^ 2) ≤ (q : ℝ) := by
  have hEL : ∀ S : Finset (Fin n), S.card + 2 ≤ n → ∀ i j : Fin n, i ∉ S → j ∉ S → i ≠ j →
      |deficiency c (insert i S) - deficiency c (insert j S)| ≤ 1 :=
    fun S _ i j hi hj hij => L2_2_deficiency_exchange c S i j hi hj hij
  have hIL : ∀ S : Finset (Fin n), S.card + 1 ≤ q → ∀ i : Fin n, i ∉ S →
      |deficiency c (insert i S) - deficiency c S| ≤ 1 := by
    intro S _ i hi
    have h := L2_2_deficiency_insert c S i hi
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  rw [expectedDeficiency]
  exact martingale_var (deficiency c) q hEL hIL q hq (le_refl q)

end SubsetSumL25
