/-
M7 (DS): Theorem A assembly — §5.8's five failure events, Markov on the cap,
and the 1/16 finite-precision bound.  This file is the statement-of-record for
what is proved; the verbatim source and the milestone ladder live in
`Statements/DS.lean`.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` §5.8 (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298).

DS-M7 §5.8 — verbatim:
    «Part 2 holds by Section 5.2. For part 1, consider these failure events.
    • E_3 fails: probability o(1), by Lemma A3.
    • The event of Lemma A4 fails: probability o(1). Here M is independent of P.
    • Some alias class is missed, given the two events above: probability
      o(1), by Corollary A6.
    • The cap is reached. By Markov's inequality and Lemma A7, this has
      probability at most
        o(1) + (b+2) 2^{(τ₀ − ε₀ + ζ)n + O(n^{0.6})} / 2^{τ₀ n + n^{0.7}}.
      The guard gives b + 2 ≤ 2^{n/10^6 + 1}, and 10^{-6} + ζ < ε₀. So this
      is o(1).
    • A bounded sampler fails. A capped execution makes at most 2^{O(n)}
      draws, so this has probability 2^{O(n)}(2^{−n³} + e^{−c₀n²}) = o(1).
    Outside these events, D_s contains every alias class of t_s (Corollary A6)
    and nothing else (Lemma A1). Then the exact output sum is
    Σ_{I∈A_s(P)} χ(I). The evaluation of Section 6.2 computes each phase to
    error 2^{−2n²} and rounds each term to n² fractional bits. The sums Φ_L
    and Φ_R have at most 2^n terms, each dictionary has at most 2^n keys, and
    every modulus is at most 2^n. So the total error is 2^{−n²+O(n)} ≤ 1/16
    for large n.»

Structure (the O8 op-bound style): each display line of §5.8 gets its own
theorem; the assembly consumes the banked upstream statements BY NAME.

  * `thmA_markov_cap` — the generic Markov tail on the package's
    fraction-of-Finset model (the M2 `expect_tail_prob_le` shape, stated for
    an abstract upper bound μ on the mean rather than the mean itself);
  * `thmA_cap_fail_le` — Markov on the cap, consuming M6's proved
    `a7_expected_work` for the expectation display.  The per-trial
    expectation transfer `E[W] ≤ ∑ S i` is the D7-named seam (hlin), per the
    ledger — not re-litigated here;
  * `thmA_cap_fail_guard_le` — the guard substitution `b+2 ≤ 2^{n/10^6+1}`
    collapsing the Markov display to the explicit exponent
    `2^{(ζ−ε₀)n + n/10^6 + δ+4 − n^{0.7}}`.  The «So this is o(1)» is the
    asymptotic reading (with `10^{-6} + ζ < ε₀` the coefficient of n is
    negative and n^{0.7} dominates δ's O(n^{0.6})); the o(1) limit itself is
    named, exactly as B5's `continue_prob_le` treats its O(·);
  * `thmA_union_range` / `thmA_sampler_fail_le` — the sampler-failure leg:
    union bound over the draw events, consuming O8's proved
    `o8_trials_le_cap` (K ≤ cap from the per-trial step ledger) and
    `o8_draws_le` (draws `2 + n² + 3K ≤ (n²+5)·cap`).  The per-draw failure
    bound `q` is named data — §5.8's `2^{−n³} + e^{−c₀n²}` per draw (the
    sampler's distribution is the algorithm boundary);
  * `thmA_union_five` / `thmA_part1_fail_le` — the five-event union bound.
    The first three legs (`E₁ E₂ E₃`: E_3 fails / Lemma A4's event fails /
    an alias class missed) enter as named probability displays `p₁ p₂ p₃` —
    their o(1) content lives in the upstream algorithm statements (Lemma A3,
    Lemma A4, Corollary A6); the identification of the sample space with the
    exec run is the boundary.  The correctness implication outside the events
    (D_s contains every alias class and nothing else, so the output equals
    the exact sum) is the named algorithm content per the DS.lean ledger;
  * `thmA_err_triangle` / `thmA_err_le_16` / `thmA_total_err_le` — the 1/16
    finite-precision leg: the triangle skeleton over the terms, then the
    explicit numeric discharge `2^{3n+1−n²} ≤ 2^{−4}` at `n ≥ 5`.  The
    exec-side counts (`NL NK NM ≤ 2^n`: Φ_L/Φ_R terms, dictionary keys,
    moduli) and the per-term Section-6.2 precision display
    (`2^{−2n²}` phase error + `2^{−n²}` rounding) are named hypotheses —
    the checksum procedure is the algorithm;
  * `thmA_part2` — §5.8's opening line «Part 2 holds by Section 5.2»:
    re-displays O8's proved `o8_time_bound` as Theorem A part 2.

Cast-discipline: ℝ for the exponent arithmetic, ℕ for the draw/trial counts;
`Nat.cast_*` / `exact_mod_cast` at the ℕ↔ℝ boundary only.  Proof-body rpow
bases are ascribed `(2 : ℝ)`; same-base monotonicity goes through the pin's
`Real.rpow_le_rpow_left_iff` (`Real.rpow_le_rpow_left` as a name does not
exist at this pin) via the `two_rpow_mono` helper; rpow joins reuse M6's
`a7_two_pow_add`.

Credit chain: Base → Bills → us.  The §5.8 assembly is Base's; this package
formalizes its probability skeleton and numeric discharges with attribution.
-/
import Mathlib
import SubsetSumL25.Statements.DS
import SubsetSumL25.Proofs.M6
import SubsetSumL25.Proofs.O8

namespace SubsetSumL25

/-! ### Small machinery -/

/-- rpow positivity for the base 2 (positivity does not close symbolic ℝ rpow
at this pin — the M2 `Real.rpow_pos_of_pos` form, banked M6). -/
theorem two_rpow_pos (x : ℝ) : 0 < (2 : ℝ) ^ x :=
  Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x

/-- Same-base rpow monotonicity through the pin's iff form (`rpow_le_rpow_left`
is not a lemma name at this pin; `rpow_le_rpow_left_iff` is @[simp]). -/
theorem two_rpow_mono {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr h

/-! ### Markov on the cap — §5.8 bullet 4 -/

/-- The generic Markov tail on the fraction-of-Finset model, for an upper
bound μ on the mean: nonnegative f with mean at most μ hits `cap` on at most
a `μ/cap` fraction of the space.  Empty space: both the junk fraction `0/0`
and the mean `0` make the display hold (the M2 empty-audit). -/
theorem thmA_markov_cap {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) {μ : ℝ} (hμ : s.expect f ≤ μ) {cap : ℝ}
    (hcap : 0 < cap) :
    ((s.filter (fun a => cap ≤ f a)).card : ℝ) / s.card ≤ μ / cap := by
  classical
  by_cases hs : s.card = 0
  · have hse : s = ∅ := Finset.card_eq_zero.mp hs
    subst hse
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div]
    have h0 : (0 : ℝ) ≤ μ := by simpa using hμ
    exact div_nonneg (by norm_num) (div_nonneg h0 hcap.le)
  · have hcard : (0 : ℝ) < s.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    set bad := s.filter (fun a => cap ≤ f a)
    have hbadsub : bad ⊆ s := Finset.filter_subset _ s
    -- each bad outcome costs at least the cap
    have hlow : cap * bad.card ≤ ∑ a ∈ bad, f a := by
      have h1 : (∑ a ∈ bad, (cap : ℝ)) = cap * bad.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
      calc cap * bad.card = ∑ a ∈ bad, (cap : ℝ) := h1.symm
        _ ≤ ∑ a ∈ bad, f a := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
    -- bad is a sub-measure (f ≥ 0 off bad): the M2 hbig if-decomposition
    have hbig : ∑ a ∈ bad, f a ≤ ∑ a ∈ s, f a := by
      have hdecomp : ∀ a ∈ s, f a = (if a ∈ bad then f a else 0) +
          (if a ∈ bad then 0 else f a) := by
        intro a ha
        by_cases h : a ∈ bad <;> simp [h]
      have hfeq : s.filter (fun a => a ∈ bad) = bad := by
        ext a
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hbadsub h, h⟩⟩
      have hind1 : (∑ a ∈ s, (if a ∈ bad then f a else 0)) = ∑ a ∈ bad, f a := by
        rw [← Finset.sum_filter, hfeq]
      calc ∑ a ∈ bad, f a = ∑ a ∈ s, (if a ∈ bad then f a else 0) := hind1.symm
        _ ≤ ∑ a ∈ s, ((if a ∈ bad then f a else 0) + (if a ∈ bad then 0 else f a)) :=
            Finset.sum_le_sum fun a ha => by
              rw [hdecomp a ha]
              by_cases h : a ∈ bad <;> simp [h, hf a ha]
        _ = ∑ a ∈ s, f a := by
            refine Finset.sum_congr rfl fun a ha => ?_
            by_cases h : a ∈ bad <;> simp [h]
    have hexp : ∑ a ∈ s, f a ≤ s.card * μ := by
      have he2 := hμ
      rw [Finset.expect_eq_sum_div_card, div_le_iff₀ hcard] at he2
      rwa [mul_comm] at he2
    have hkey : cap * bad.card ≤ s.card * μ := le_trans (le_trans hlow hbig) hexp
    refine div_le_div_iff₀ hcard hcap |>.mpr ?_
    rwa [mul_comm cap bad.card, mul_comm s.card μ] at hkey

/-- §5.8 bullet 4's Markov display: the capped execution's work `Wt` has mean
at most Lemma A7's ledger bound (consumed by name via `a7_expected_work`, with
the per-trial expectation transfer `hlin` as the D7-named seam), so the cap
`2^{τ₀ n + n^{0.7}}` is reached with probability at most
`(b+2)·2^{(τ₀−ε₀+ζ)n+δ+3} / 2^{τ₀n+n^{0.7}}` — the paper's
«o(1) + (b+2) 2^{(τ₀ − ε₀ + ζ)n + O(n^{0.6})} / 2^{τ₀ n + n^{0.7}}» with the
O(n^{0.6}) explicit as δ+3. -/
theorem thmA_cap_fail_le {α : Type*} (s : Finset α) (Wt : α → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ Wt ω)
    {b τ₀ ε₀ ζ n δ : ℝ} (hb : 0 ≤ b)
    (hK : 0 ≤ (τ₀ - ε₀ + ζ) * n + δ)
    (S : ℕ → ℝ)
    (hitem : ∀ i ∈ Finset.range 7, S i ≤ (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + δ))
    (hlin : s.expect Wt ≤ ∑ i ∈ Finset.range 7, S i) :
    ((s.filter (fun ω => (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) ≤ Wt ω)).card : ℝ)
        / s.card
      ≤ (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3))
          / (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) := by
  have hμ : s.expect Wt
      ≤ (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3)) :=
    a7_expected_work hb hK S hitem
  exact thmA_markov_cap s Wt hw (le_trans hlin hμ) (two_rpow_pos _)

/-- §5.8 bullet 4's guard collapse: «The guard gives b + 2 ≤ 2^{n/10^6 + 1}»
substituted into the Markov display gives the explicit exponent
`2^{(ζ−ε₀)n + n/10^6 + δ+4 − n^{0.7}}`.  With the paper's
`10^{-6} + ζ < ε₀` (not consumed here — it is the o(1) reading's input) the
coefficient `(ζ − ε₀) + 10^{-6}` of n is negative and the exponent tends
to −∞: the asymptotic reading is named, as in `continue_prob_le`. -/
theorem thmA_cap_fail_guard_le {α : Type*} (s : Finset α) (Wt : α → ℝ)
    (hw : ∀ ω ∈ s, 0 ≤ Wt ω)
    {b τ₀ ε₀ ζ n δ : ℝ} (hb : 0 ≤ b)
    (hK : 0 ≤ (τ₀ - ε₀ + ζ) * n + δ)
    (S : ℕ → ℝ)
    (hitem : ∀ i ∈ Finset.range 7, S i ≤ (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + δ))
    (hlin : s.expect Wt ≤ ∑ i ∈ Finset.range 7, S i)
    (hguard : b + 2 ≤ (2 : ℝ) ^ (n / (10 : ℝ) ^ 6 + 1)) :
    ((s.filter (fun ω => (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) ≤ Wt ω)).card : ℝ)
        / s.card
      ≤ (2 : ℝ) ^ ((ζ - ε₀) * n + n / (10 : ℝ) ^ 6 + (δ + 4) - n ^ (0.7 : ℝ)) := by
  have hcap := thmA_cap_fail_le s Wt hw hb hK S hitem hlin
  have hpA : 0 < (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3)) := two_rpow_pos _
  have hpC : 0 < (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) := two_rpow_pos _
  have hnum : (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3))
      ≤ (2 : ℝ) ^ (n / (10 : ℝ) ^ 6 + 1) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3)) :=
    a7_right hguard hpA.le
  have hnum2 : (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3))
        * (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ))
      ≤ (2 : ℝ) ^ (n / (10 : ℝ) ^ 6 + 1) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3))
          * (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) := a7_right hnum hpC.le
  have hexp : (n / (10 : ℝ) ^ 6 + 1 + ((τ₀ - ε₀ + ζ) * n + (δ + 3)))
        - (τ₀ * n + n ^ (0.7 : ℝ))
      = ((ζ - ε₀) * n + n / (10 : ℝ) ^ 6 + (δ + 4) - n ^ (0.7 : ℝ)) := by ring
  calc ((s.filter (fun ω => (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) ≤ Wt ω)).card : ℝ)
        / s.card
      ≤ (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3))
          / (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) := hcap
    _ ≤ (2 : ℝ) ^ (n / (10 : ℝ) ^ 6 + 1 + ((τ₀ - ε₀ + ζ) * n + (δ + 3)))
          / (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) :=
          div_le_div_iff₀ hpC hpC |>.mpr hnum2
    _ = (2 : ℝ) ^ (n / (10 : ℝ) ^ 6 + 1 + ((τ₀ - ε₀ + ζ) * n + (δ + 3))
          - (τ₀ * n + n ^ (0.7 : ℝ))) :=
          (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ = (2 : ℝ) ^ ((ζ - ε₀) * n + n / (10 : ℝ) ^ 6 + (δ + 4) - n ^ (0.7 : ℝ)) := by
          rw [hexp]

/-! ### The sampler-failure leg — §5.8 bullet 5 -/

/-- The union bound over a family of `K` draw-events on the fraction model:
`K` events each of fraction ≤ q cover at most a `K·q` fraction. -/
theorem thmA_union_range {α : Type*} (s : Finset α) (hs : 0 < s.card)
    (F : ℕ → Finset α) (K : ℕ) {q : ℝ}
    (hq : ∀ i ∈ Finset.range K, ((F i).card : ℝ) ≤ q * s.card) :
    ((Finset.biUnion (Finset.range K) F).card : ℝ) / s.card ≤ K * q := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hbu : (Finset.biUnion (Finset.range K) F).card
      ≤ ∑ i ∈ Finset.range K, (F i).card := Finset.card_biUnion_le _
  have hstep1 : ((Finset.biUnion (Finset.range K) F).card : ℝ)
      ≤ ((∑ i ∈ Finset.range K, (F i).card : ℕ) : ℝ) := by exact_mod_cast hbu
  have hstep2 : ((Finset.biUnion (Finset.range K) F).card : ℝ) * s.card
      ≤ ((∑ i ∈ Finset.range K, (F i).card : ℕ) : ℝ) * s.card := a7_right hstep1 hs.le
  have hsum : (((∑ i ∈ Finset.range K, (F i).card : ℕ) : ℝ)) ≤ K * (q * s.card) := by
    have h1 : ((∑ i ∈ Finset.range K, (F i).card : ℕ) : ℝ)
        = ∑ i ∈ Finset.range K, ((F i).card : ℝ) := by
      push_cast
      ring
    rw [h1]
    calc ∑ i ∈ Finset.range K, ((F i).card : ℝ)
        ≤ (∑ _i ∈ Finset.range K, q * s.card : ℝ) := Finset.sum_le_sum hq
      _ = K * (q * s.card) := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ((Finset.biUnion (Finset.range K) F).card : ℝ) / s.card
      ≤ ((∑ i ∈ Finset.range K, (F i).card : ℕ) : ℝ) / s.card :=
          div_le_div_iff₀ hcard hcard |>.mpr hstep2
    _ ≤ K * q := by
        have hne0 : s.card ≠ 0 := hcard.ne
        have h : ((∑ i ∈ Finset.range K, (F i).card : ℕ) : ℝ) / s.card
            ≤ K * (q * s.card) / s.card := div_le_div_iff₀ hcard hcard |>.mpr hsum
        field_simp at h ⊢
        linarith

/-- §5.8 bullet 5: «A capped execution makes at most 2^{O(n)} draws, so this
has probability 2^{O(n)}(2^{−n³} + e^{−c₀n²})» — the explicit form.  The draw
count is O8's proved ledger: `K ≤ cap` via `o8_trials_le_cap` (each trial
consumes ≥ 1 counted step, named data `S`) and draws `2 + n² + 3K ≤ (n²+5)·cap`
via `o8_draws_le`.  The per-draw failure bound `q` — §5.8's
`2^{−n³} + e^{−c₀n²}` — is named data (the sampler's distribution is the
algorithm boundary). -/
theorem thmA_sampler_fail_le {α : Type*} (s : Finset α) (hs : 0 < s.card)
    (F : ℕ → Finset α)
    {cap K : ℕ} (S : ℕ → ℕ) (h1 : ∀ i, 1 ≤ S i)
    (hcapN : ∑ i ∈ Finset.range K, S i ≤ cap) (hcap1 : 1 ≤ cap)
    {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ i ∈ Finset.range (n ^ 2 + 2 + 3 * K), ((F i).card : ℝ) ≤ q * s.card) :
    ((Finset.biUnion (Finset.range (n ^ 2 + 2 + 3 * K)) F).card : ℝ) / s.card
      ≤ (↑(n ^ 2 + 5) * ↑cap) * q := by
  have hK : K ≤ cap := o8_trials_le_cap S h1 hcapN
  have hD : n ^ 2 + 2 + 3 * K ≤ (n ^ 2 + 5) * cap := o8_draws_le hcap1 hK
  have hDc : (((n ^ 2 + 2 + 3 * K : ℕ) : ℝ)) ≤ (↑(n ^ 2 + 5) * ↑cap : ℝ) :=
    by exact_mod_cast hD
  have hunion := thmA_union_range s hs F (n ^ 2 + 2 + 3 * K) hq
  calc ((Finset.biUnion (Finset.range (n ^ 2 + 2 + 3 * K)) F).card : ℝ) / s.card
      ≤ (((n ^ 2 + 2 + 3 * K : ℕ) : ℝ)) * q := hunion
    _ ≤ (↑(n ^ 2 + 5) * ↑cap) * q := a7_right hDc hq0

/-! ### The five-event union — §5.8 part 1 -/

/-- The union bound over five events: the events cover at most the sum of
their probabilities. -/
theorem thmA_union_five {α : Type*} (s : Finset α) (hs : 0 < s.card)
    (E₁ E₂ E₃ E₄ E₅ : Finset α) {p₁ p₂ p₃ p₄ p₅ : ℝ}
    (h₁ : ((E₁.card : ℝ)) ≤ p₁ * s.card) (h₂ : ((E₂.card : ℝ)) ≤ p₂ * s.card)
    (h₃ : ((E₃.card : ℝ)) ≤ p₃ * s.card) (h₄ : ((E₄.card : ℝ)) ≤ p₄ * s.card)
    (h₅ : ((E₅.card : ℝ)) ≤ p₅ * s.card) :
    (((E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅).card : ℝ)) / s.card
      ≤ p₁ + p₂ + p₃ + p₄ + p₅ := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hle : (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅).card
      ≤ E₁.card + E₂.card + E₃.card + E₄.card + E₅.card := by
    have a : (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := Finset.card_union_le E₁ E₂
    have b : ((E₁ ∪ E₂) ∪ E₃).card ≤ (E₁ ∪ E₂).card + E₃.card :=
      Finset.card_union_le (E₁ ∪ E₂) E₃
    have c : (((E₁ ∪ E₂) ∪ E₃) ∪ E₄).card ≤ ((E₁ ∪ E₂) ∪ E₃).card + E₄.card :=
      Finset.card_union_le ((E₁ ∪ E₂) ∪ E₃) E₄
    have d : ((((E₁ ∪ E₂) ∪ E₃) ∪ E₄) ∪ E₅).card
        ≤ (((E₁ ∪ E₂) ∪ E₃) ∪ E₄).card + E₅.card :=
      Finset.card_union_le (((E₁ ∪ E₂) ∪ E₃) ∪ E₄) E₅
    omega
  have hprod : ((E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅).card : ℝ)
      ≤ (p₁ + p₂ + p₃ + p₄ + p₅) * s.card := by
    have hcast : (((E₁.card + E₂.card + E₃.card + E₄.card + E₅.card : ℕ) : ℝ))
        = (E₁.card : ℝ) + (E₂.card : ℝ) + (E₃.card : ℝ) + (E₄.card : ℝ)
          + (E₅.card : ℝ) := by
      push_cast
      ring
    calc ((E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅).card : ℝ)
        ≤ ((E₁.card + E₂.card + E₃.card + E₄.card + E₅.card : ℕ) : ℝ) :=
          by exact_mod_cast hle
      _ ≤ (p₁ + p₂ + p₃ + p₄ + p₅) * s.card := by
          have e₁ : (p₁ + p₂ + p₃ + p₄ + p₅) * s.card
              = p₁ * s.card + p₂ * s.card + p₃ * s.card + p₄ * s.card
                + p₅ * s.card := by ring
          rw [hcast, e₁]
          linarith
  exact div_le_iff₀ hcard |>.mpr hprod

/-- §5.8's part-1 probability display, all five legs assembled: the three
named o(1) events (`E₁` = E_3 fails, `E₂` = Lemma A4's event fails, `E₃` = an
alias class missed — their bounds `p₁ p₂ p₃` are the upstream algorithm
statements' displays), the cap leg (`thmA_cap_fail_guard_le`, consuming M6's
`a7_expected_work` through the named per-trial expectation transfer), and the
sampler leg (`thmA_sampler_fail_le`, consuming O8's `o8_trials_le_cap` and
`o8_draws_le`, with `q` the named per-draw failure bound).  Outside these
events the output is the exact sum within the §6.2 precision — the correctness
implication is the named algorithm content per the DS.lean ledger.  Note the
cap leg's `n` is the ℝ input size and the sampler leg's `nS` its ℕ
counterpart; the identification is the exec boundary. -/
theorem thmA_part1_fail_le {α : Type*} (s : Finset α) (hs : 0 < s.card)
    (E₁ E₂ E₃ : Finset α) {p₁ p₂ p₃ : ℝ}
    (h₁ : ((E₁.card : ℝ)) ≤ p₁ * s.card) (h₂ : ((E₂.card : ℝ)) ≤ p₂ * s.card)
    (h₃ : ((E₃.card : ℝ)) ≤ p₃ * s.card)
    (Wt : α → ℝ) (hw : ∀ ω ∈ s, 0 ≤ Wt ω)
    {b τ₀ ε₀ ζ n δ : ℝ} (hb : 0 ≤ b)
    (hK : 0 ≤ (τ₀ - ε₀ + ζ) * n + δ)
    (S : ℕ → ℝ)
    (hitem : ∀ i ∈ Finset.range 7, S i ≤ (b + 2) * (2 : ℝ) ^ ((τ₀ - ε₀ + ζ) * n + δ))
    (hlin : s.expect Wt ≤ ∑ i ∈ Finset.range 7, S i)
    (hguard : b + 2 ≤ (2 : ℝ) ^ (n / (10 : ℝ) ^ 6 + 1))
    (F : ℕ → Finset α)
    {cap K nS : ℕ} (St : ℕ → ℕ) (h1 : ∀ i, 1 ≤ St i)
    (hcapN : ∑ i ∈ Finset.range K, St i ≤ cap) (hcap1 : 1 ≤ cap)
    {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ i ∈ Finset.range (nS ^ 2 + 2 + 3 * K), ((F i).card : ℝ) / s.card ≤ q) :
    ((((E₁ ∪ E₂ ∪ E₃
          ∪ (s.filter (fun ω => (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) ≤ Wt ω))
          ∪ (Finset.biUnion (Finset.range (nS ^ 2 + 2 + 3 * K)) F)).card : ℝ)))
        / s.card
      ≤ p₁ + p₂ + p₃
        + (2 : ℝ) ^ ((ζ - ε₀) * n + n / (10 : ℝ) ^ 6 + (δ + 4) - n ^ (0.7 : ℝ))
        + (↑(nS ^ 2 + 5) * ↑cap) * q := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hqc : ∀ i ∈ Finset.range (nS ^ 2 + 2 + 3 * K),
      ((F i).card : ℝ) ≤ q * s.card := fun i hi =>
    div_le_iff₀ hcard |>.mp (hq i hi)
  refine thmA_union_five s hs E₁ E₂ E₃
    (s.filter (fun ω => (2 : ℝ) ^ (τ₀ * n + n ^ (0.7 : ℝ)) ≤ Wt ω))
    (Finset.biUnion (Finset.range (nS ^ 2 + 2 + 3 * K)) F) ?_ ?_ ?_ ?_ ?_
  · exact h₁
  · exact h₂
  · exact h₃
  · exact thmA_cap_fail_guard_le s Wt hw hb hK S hitem hlin hguard
  · exact div_le_iff₀ hcard |>.mpr
      (thmA_sampler_fail_le s hs F St h1 hcapN hcap1 hq0 hqc)

/-! ### The 1/16 finite-precision bound — §5.8's closing -/

/-- The triangle skeleton: with every term's evaluation error at most `e`
(Section 6.2's per-term display is the named input), the total error of the
sum is at most `#t · e`. -/
theorem thmA_err_triangle {α : Type*} (t : Finset α) (err exact : α → ℝ)
    {e : ℝ} (he : ∀ i ∈ t, |err i - exact i| ≤ e) :
    |(∑ i ∈ t, err i) - ∑ i ∈ t, exact i| ≤ (t.card : ℝ) * e := by
  have hsplit : (∑ i ∈ t, err i) - ∑ i ∈ t, exact i
      = ∑ i ∈ t, (err i - exact i) := by
    rw [← Finset.sum_sub_distrib]
  rw [hsplit]
  have htri : |∑ i ∈ t, (err i - exact i)| ≤ ∑ i ∈ t, |err i - exact i| := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        calc |(∑ i ∈ t, (err i - exact i)) + (err a - exact a)|
            ≤ |∑ i ∈ t, (err i - exact i)| + |err a - exact a| := abs_add _ _
          _ ≤ (∑ i ∈ t, |err i - exact i|) + |err a - exact a| :=
              add_le_add ih (le_refl _)
          _ = ∑ i ∈ insert a t, |err i - exact i| := by rw [Finset.sum_insert ha]
  calc |∑ i ∈ t, (err i - exact i)| ≤ ∑ i ∈ t, |err i - exact i| := htri
    _ ≤ (∑ _i ∈ t, e : ℝ) := Finset.sum_le_sum fun i hi => he i hi
    _ = (t.card : ℝ) * e := by rw [Finset.sum_const, nsmul_eq_mul]

/-- §5.8's closing numeric: the total error `NL·NK·NM·e` — Φ_L/Φ_R term count
× dictionary keys × moduli, each ≤ 2^n (the exec counts are named hypotheses,
per the D7 boundary) — with per-term error ≤ the §6.2 display
`2^{−2n²} + 2^{−n²}` (phase + n²-fractional-bit rounding), is at most 1/16
once `5 ≤ n` («for large n» made explicit: the paper's
`2^{−n²+O(n)} ≤ 1/16` with O(n) = 3n+1). -/
theorem thmA_err_le_16 {n NL NK NM e : ℝ} (hn : (5 : ℝ) ≤ n)
    (hNL : NL ≤ (2 : ℝ) ^ n) (hNK : NK ≤ (2 : ℝ) ^ n) (hNM : NM ≤ (2 : ℝ) ^ n)
    (hNK0 : 0 ≤ NK) (hNM0 : 0 ≤ NM) (he0 : 0 ≤ e)
    (he : e ≤ (2 : ℝ) ^ (-(2 * n * n)) + (2 : ℝ) ^ (-(n * n))) :
    NL * NK * NM * e ≤ 1 / 16 := by
  have h25 : (25 : ℝ) ≤ n * n := by nlinarith
  have hnn : (0 : ℝ) ≤ n := le_trans (by norm_num) hn
  have hnn2 : (0 : ℝ) ≤ n * n := mul_nonneg hnn hnn
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := two_rpow_pos n
  have hpownn : (0 : ℝ) ≤ (2 : ℝ) ^ n := hpow.le
  have hAB1 : NL * NK ≤ (2 : ℝ) ^ n * NK := a7_right hNL hNK0
  have hAB2 : (2 : ℝ) ^ n * NK ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := a7_left hNK hpownn
  have hAB : NL * NK ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := le_trans hAB1 hAB2
  have hA2nn : (0 : ℝ) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := mul_nonneg hpownn hpownn
  have hABC1 : NL * NK * NM ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * NM := a7_right hAB hNM0
  have hABC2 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * NM
      ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n := a7_left hNM hA2nn
  have hABC : NL * NK * NM ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n :=
    le_trans hABC1 hABC2
  have hA3nn : (0 : ℝ) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n :=
    mul_nonneg (mul_nonneg hpownn hpownn) hpownn
  have hAB3 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n = (2 : ℝ) ^ (3 * n) := by
    rw [a7_two_pow_add, a7_two_pow_add]
    congr 1
    ring
  have h2le : (2 : ℝ) ^ (-(2 * n * n)) ≤ (2 : ℝ) ^ (-(n * n)) :=
    two_rpow_mono (by linarith)
  have hjoin : (((2 : ℝ) ^ (1 : ℝ)) * (2 : ℝ) ^ (-(n * n)))
      = (2 : ℝ) ^ (1 - n * n) := by
    rw [a7_two_pow_add]
    congr 1
    ring
  have hB : (2 : ℝ) * (2 : ℝ) ^ (-(n * n)) = (2 : ℝ) ^ (1 - n * n) := by
    calc (2 : ℝ) * (2 : ℝ) ^ (-(n * n))
        = (2 : ℝ) ^ ((1 : ℝ)) * (2 : ℝ) ^ (-(n * n)) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (1 - n * n) := hjoin
  have he2 : e ≤ (2 : ℝ) * (2 : ℝ) ^ (-(n * n)) := by
    have h1 : (2 : ℝ) ^ (-(2 * n * n)) + (2 : ℝ) ^ (-(n * n))
        ≤ (2 : ℝ) ^ (-(n * n)) + (2 : ℝ) ^ (-(n * n)) := by
      refine add_le_add_right h2le _
    linarith [he, h1]
  have hstep1 : NL * NK * NM * e
      ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n * e := a7_right hABC he0
  calc NL * NK * NM * e
      ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n * e := hstep1
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 : ℝ) ^ n
          * ((2 : ℝ) * (2 : ℝ) ^ (-(n * n))) := a7_left he2 hA3nn
    _ = (2 : ℝ) ^ (3 * n) * ((2 : ℝ) * (2 : ℝ) ^ (-(n * n))) := by rw [hAB3]
    _ = (2 : ℝ) ^ (3 * n) * (2 : ℝ) ^ (1 - n * n) := by rw [hB]
    _ = (2 : ℝ) ^ (3 * n + (1 - n * n)) := a7_two_pow_add _ _
    _ ≤ (2 : ℝ) ^ ((-4 : ℝ)) := two_rpow_mono (by nlinarith)
    _ = 1 / 16 := by norm_num

/-- §5.8's closing line assembled: `#t ≤ NL·NK·NM` terms each within the §6.2
per-term display give a total error ≤ 1/16 — the paper's «So the total error
is 2^{−n²+O(n)} ≤ 1/16 for large n».  (The identification of `t` with the
algorithm's actual summation tree is the named exec boundary.) -/
theorem thmA_total_err_le {α : Type*} (t : Finset α) (err exact : α → ℝ)
    {n NL NK NM e : ℝ} (hn : (5 : ℝ) ≤ n)
    (hcard : ((t.card : ℝ)) ≤ NL * NK * NM)
    (hNL : NL ≤ (2 : ℝ) ^ n) (hNK : NK ≤ (2 : ℝ) ^ n) (hNM : NM ≤ (2 : ℝ) ^ n)
    (hNK0 : 0 ≤ NK) (hNM0 : 0 ≤ NM)
    (he : ∀ i ∈ t, |err i - exact i| ≤ e)
    (heT : e ≤ (2 : ℝ) ^ (-(2 * n * n)) + (2 : ℝ) ^ (-(n * n))) :
    |(∑ i ∈ t, err i) - ∑ i ∈ t, exact i| ≤ 1 / 16 := by
  by_cases h0 : t = ∅
  · subst h0
    rw [Finset.sum_empty, Finset.sum_empty, sub_zero, abs_zero]
    norm_num
  · have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    obtain ⟨i, hi⟩ := hne
    have he0 : 0 ≤ e := le_trans (abs_nonneg _) (he i hi)
    calc |(∑ j ∈ t, err j) - ∑ j ∈ t, exact j|
        ≤ (t.card : ℝ) * e := thmA_err_triangle t err exact he
      _ ≤ (NL * NK * NM) * e := a7_right hcard he0
      _ ≤ 1 / 16 := thmA_err_le_16 hn hNL hNK hNM hNK0 hNM0 he0 heT

/-! ### Part 2 — §5.8's opening line -/

/-- «Part 2 holds by Section 5.2»: Theorem A part 2 is O8's word-RAM
accounting, consumed by name (`o8_time_bound` — the ten elementary-step
categories within `cap·P` sum to `16·P·2^{τ₀n+2n^{0.7}}`). -/
theorem thmA_part2 {τ₀ n P : ℝ} (hn07 : 2 ≤ n ^ (0.7 : ℝ)) (hP : 0 ≤ P)
    (S : ℕ → ℝ) (hcat : ∀ i ∈ Finset.range 10, S i ≤ o8Cap τ₀ n * P) :
    ∑ i ∈ Finset.range 10, S i
      ≤ (16 : ℝ) * P * 2 ^ (τ₀ * n + 2 * n ^ (0.7 : ℝ)) :=
  o8_time_bound hn07 hP S hcat

end SubsetSumL25
