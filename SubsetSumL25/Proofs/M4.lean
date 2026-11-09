/-
M4 (DS): Lemma A5 Steps 4–5 — the small-prime residues ((F4) dispatch) and
the recovery walk, in the alias-class setting.  This file is the
statement-of-record for what is proved; the verbatim source and the milestone
ladder live in `Statements/DS.lean`.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` §5.6 (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298).

DS-M4 Step 4 (the small prime keeps many residues) — verbatim:
    «Fix a good S.  The set W_S depends on P, M, L, I and S, but not on P' or
    j'.  Its elements lie in (−nP, nP), so differences have at most
    ηn + log n + 3 bits.  For distinct x, x' ∈ W_S, (F4) with L' = ⌊γm⌋ gives
    Pr[P' | x − x'] ≤ K₀n²2^{−γm}, for an absolute constant K₀ ≥ 1.  Let z_y
    be the number of elements of W_S in the residue class y modulo P'.  Then
    E_{P'} Σ_y z_y² ≤ B_S + K₀n²B_S²2^{−γm}.  … By Markov's inequality, with
    probability at least 1/2 over P', Σ_y z_y² is at most twice that bound.
    Then the Cauchy–Schwarz inequality (Σ_y z_y)² ≤ #{y : z_y > 0} · Σ_y z_y²
    shows that at least min(B_S, 2^{γm})/(4K₀n²) residues are occupied.»

DS-M4 Step 5 (a hit is recovered) — verbatim:
    «Suppose j' ≡ b(A) + b^F(X) (mod P') for some X ⊆ S with |X| = k.  Then
    the left record (κ(A), X) is listed.  Put Y = S \ X; so |Y| = σ − k and
    X ∩ Y = ∅.  Since S ∆ F = I ∩ M, (5.1) gives
    b(A) + b^F(X) + b(B) + b^F(Y) = b(A) + b(B) + b(I ∩ M) − b(F) =
    T_{s,q} − b(F) = T^F.  So the class record (κ(B), λ(Y)) has the residue
    T^F − j'.  … The expansion reaches its member Y and inserts
    (κ(A), κ(B), (X ∪ Y) ∆ F) = (κ(A), κ(B), I ∩ M), unless the key is
    already there.»

Here `W` is the abstract value set of the walk (the paper's `W_S` — its
instantiation `W := layerSupport (sgnW b F) S k` is the consumer's); the
(F4) dispatch consumes our proved `L2_5_prime_collision_two` (the per-pair
form of OpenAI L2.5), through the A5 lane's `pair_collision_le` /
`collisionPairs_expect_le` spine.  The bit bound enters as the hypothesis
`hbits` (the paper's «differences have at most ηn + log n + 3 bits» is
instance data, not package mathematics).

Cast-discipline: ℝ for the probabilities, ℕ for the counts; `exact_mod_cast`
at the ℕ↔ℝ boundary only.
-/
import Mathlib
import SubsetSumL25.Statements.Defs
import SubsetSumL25.Proofs.PrimeCollision
import SubsetSumL25.Proofs.DS
import SubsetSumL25.Proofs.A5
import SubsetSumL25.Proofs.M2
import SubsetSumL25.Proofs.M3

open scoped symmDiff

namespace SubsetSumL25

/-! ### DS-M4 Step 4 — the (F4) dispatch -/

/-- Step 4's (F4) instance, per pair, in expectation form: composing our
proved `L2_5_prime_collision_two` (the per-pair form of OpenAI L2.5) with the
A5 lane's `pair_collision_le`.  This is the exact place the paper writes
«(F4) with L' = ⌊γm⌋ gives Pr[P' | x − x'] ≤ …».  The constant `K` is uniform
in `L'` (it is `L2_5_prime_collision_two`'s witness), which is what lets the
second moment below use one `K` for every pair. -/
theorem pair_expect_le_L25 {c₀ : ℝ} (hc₀ : 0 < c₀) (L₀ : ℕ)
    (hcount : ∀ L, L₀ ≤ L → c₀ * (2 : ℝ) ^ L / L ≤ (primesInterval L).card)
    (hpos : ∀ L, L₀ ≤ L → 0 < (primesInterval L).card)
    {x x' : ℤ} (hne : x ≠ x') {B : ℕ} (hB : 1 ≤ B)
    (hbits : ((x - x').natAbs : ℝ) < (2 : ℝ) ^ B) :
    ∃ (K : ℝ) (Lstar : ℕ), 0 < K ∧ ∀ L' : ℕ, Lstar ≤ L' →
      (primesInterval L').expect (fun (q : ℕ) => if (↑q : ℤ) ∣ (x - x') then (1 : ℝ) else 0)
        ≤ K * (B : ℝ) * (L' : ℝ) / (2 : ℝ) ^ L' := by
  obtain ⟨K, Lstar, hK, hmain⟩ := L2_5_prime_collision_two c₀ hc₀ L₀ hcount hpos
  exact ⟨K, Lstar, hK, fun L' hL' => pair_collision_le (hmain L' hL' x x' B hne hB hbits)⟩

/-- Step 4's second moment in collision form, with the (F4) dispatch applied
uniformly over the pairs of `W`: `E_{P'} #{colliding pairs} ≤ |W|²·K·B·L/2^L`
(the A5 lane's `collisionPairs_expect_le` with `K₀ := K·B·L`, the explicit
`(F4)` constant). -/
theorem collisionPairs_expect_le_L25 (W : Finset ℤ) {L B : ℕ} {K : ℝ}
    (hK : 0 < K)
    (hbits : ∀ x ∈ W, ∀ x' ∈ W, x ≠ x' → ((x - x').natAbs : ℝ) < (2 : ℝ) ^ B)
    (hF4 : ∀ x ∈ W, ∀ x' ∈ W, x ≠ x' → ((x - x').natAbs : ℝ) < (2 : ℝ) ^ B →
      (primesInterval L).expect (fun (q : ℕ) => if (↑q : ℤ) ∣ (x - x') then (1 : ℝ) else 0)
        ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L) :
    (primesInterval L).expect (fun q => (collisionPairs W q : ℝ))
      ≤ (W.card : ℝ) ^ 2 * (K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L) := by
  have hK₀ : (0 : ℝ) ≤ K * (B : ℝ) * (L : ℝ) :=
    mul_nonneg (mul_nonneg (le_of_lt hK) (Nat.cast_nonneg B)) (Nat.cast_nonneg L)
  exact collisionPairs_expect_le W hK₀
    (fun x hx x' hx' hne => hF4 x hx x' hx' hne (hbits x hx x' hx' hne))

/-! ### DS-M4 Step 4 — the second moment `Σ_y z_y²` -/

/-- Step 4's pointwise identity: `Σ_y z_y² = |W| + #{ordered colliding pairs}`
(the paper's second moment), for every modulus `p ≥ 1` — each element of `W`
contributes its diagonal `1`, and the off-diagonal terms are exactly the
ordered pairs `P′ ∣ x − x'`. -/
theorem sum_sq_classes_eq_card_add_collisionPairs (W : Finset ℤ) {p : ℕ} (_hp : 0 < p) :
    ∑ y ∈ W.image (fun x => x % (p : ℤ)),
        (W.filter (fun x => x % (p : ℤ) = y)).card ^ 2
      = W.card + collisionPairs W p := by
  classical
  have hmem : ∀ x ∈ W, x % (p : ℤ) ∈ W.image (fun x => x % (p : ℤ)) := fun x hx =>
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  -- step 1: z y ^ 2 = ∑ x' ∈ class y, z y  (the sum over a class of the class count)
  have hstep1 : ∀ y ∈ W.image (fun x => x % (p : ℤ)),
      (W.filter (fun x => x % (p : ℤ) = y)).card ^ 2
        = ∑ x' ∈ W.filter (fun x => x % (p : ℤ) = y),
            (W.filter (fun x => x % (p : ℤ) = y)).card := by
    intro y _
    calc (W.filter (fun x => x % (p : ℤ) = y)).card ^ 2
        = (W.filter (fun x => x % (p : ℤ) = y)).card
            * (W.filter (fun x => x % (p : ℤ) = y)).card := pow_two _
      _ = (∑ _x' ∈ W.filter (fun x => x % (p : ℤ) = y), (1 : ℕ))
            * (W.filter (fun x => x % (p : ℤ) = y)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
      _ = ∑ x' ∈ W.filter (fun x => x % (p : ℤ) = y),
            (W.filter (fun x => x % (p : ℤ) = y)).card := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => one_mul _
  -- step 2: swap the sums, with the class-membership filter as an indicator
  have hstep2 : (∑ y ∈ W.image (fun x => x % (p : ℤ)),
        ∑ x' ∈ W.filter (fun x => x % (p : ℤ) = y),
          (W.filter (fun x => x % (p : ℤ) = y)).card)
      = ∑ x' ∈ W, ∑ y ∈ W.image (fun x => x % (p : ℤ)),
          (if x' % (p : ℤ) = y then (W.filter (fun x => x % (p : ℤ) = y)).card else 0) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  -- step 3: the inner sum collapses to the count of the class of x'
  have hstep3 : ∀ x' ∈ W,
      (∑ y ∈ W.image (fun x => x % (p : ℤ)),
          (if x' % (p : ℤ) = y then (W.filter (fun x => x % (p : ℤ) = y)).card else 0))
        = (W.filter (fun x => x % (p : ℤ) = x' % (p : ℤ))).card := by
    intro x' hx'
    rw [Finset.sum_ite_eq, ite_eq_left (hmem x' hx')]
  -- step 4: the class of x' is the ≡-fiber, and the ≡-indicator splits into the
  -- diagonal (one per x') plus the ordered colliding pairs (= collisionPairs;
  -- the colliding condition is stated (outer, inner)-oriented so that
  -- `Finset.sum_product'` reproduces `collisionPairs`'s filter shape)
  have hsplit : ∀ x' ∈ W, ∀ x ∈ W,
      ((if (p : ℤ) ∣ x - x' then (1 : ℕ) else 0) : ℕ)
        = (if x = x' then 1 else 0)
          + (if x' ≠ x ∧ (p : ℤ) ∣ x' - x then 1 else 0) := by
    intro x' _ x _
    by_cases hxx : x = x'
    · subst hxx
      simp
    · by_cases hdvd : (p : ℤ) ∣ x - x'
      · have hrev : (p : ℤ) ∣ x' - x := by
          rw [← neg_sub x x']; exact Int.dvd_neg.mpr hdvd
        rw [ite_eq_left hdvd, ite_eq_right hxx, ite_eq_left ⟨Ne.symm hxx, hrev⟩]
      · have hrev : ¬((p : ℤ) ∣ x' - x) := fun hc => hdvd (by
            rw [← neg_sub x x'] at hc; exact Int.dvd_neg.mp hc)
        rw [ite_eq_right hdvd, ite_eq_right hxx, ite_eq_right (fun h => hrev h.2)]
  have hcong : ∀ x' ∈ W, (W.filter (fun x => x % (p : ℤ) = x' % (p : ℤ))).card
      = ∑ x ∈ W, (if (p : ℤ) ∣ x - x' then (1 : ℕ) else 0) := by
    intro x' _
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hiff : (x % (p : ℤ) = x' % (p : ℤ)) ↔ ((p : ℤ) ∣ x - x') := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]
    by_cases hd : x % (p : ℤ) = x' % (p : ℤ)
    · rw [ite_eq_left hd, ite_eq_left (hiff.mp hd)]
    · rw [ite_eq_right hd, ite_eq_right (fun hc => hd (hiff.mpr hc))]
  have hsingleton : ∀ x' ∈ W, (W.filter (fun x => x = x')).card = 1 := by
    intro x' hx'
    have h : W.filter (fun x => x = x') = {x'} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun hz => hz.2, fun hz => ?_⟩
      exact ⟨hz ▸ hx', hz⟩
    rw [h, Finset.card_singleton]
  have hcoll : ∑ x' ∈ W, ∑ x ∈ W,
      (if x' ≠ x ∧ (p : ℤ) ∣ x' - x then (1 : ℕ) else 0) = collisionPairs W p := by
    rw [collisionPairs, Finset.card_filter, finset_product_eq_sprod,
      ← Finset.sum_product']
  calc ∑ y ∈ W.image (fun x => x % (p : ℤ)),
        (W.filter (fun x => x % (p : ℤ) = y)).card ^ 2
      = ∑ y ∈ W.image (fun x => x % (p : ℤ)),
          ∑ x' ∈ W.filter (fun x => x % (p : ℤ) = y),
            (W.filter (fun x => x % (p : ℤ) = y)).card :=
        Finset.sum_congr rfl hstep1
    _ = ∑ x' ∈ W, ∑ y ∈ W.image (fun x => x % (p : ℤ)),
          (if x' % (p : ℤ) = y then (W.filter (fun x => x % (p : ℤ) = y)).card else 0) :=
        hstep2
    _ = ∑ x' ∈ W, (W.filter (fun x => x % (p : ℤ) = x' % (p : ℤ))).card :=
        Finset.sum_congr rfl hstep3
    _ = ∑ x' ∈ W, ∑ x ∈ W, (if (p : ℤ) ∣ x - x' then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl hcong
    _ = ∑ x' ∈ W, ((W.filter (fun x => x = x')).card
          + ∑ x ∈ W, (if x' ≠ x ∧ (p : ℤ) ∣ x' - x then (1 : ℕ) else 0)) := by
        refine Finset.sum_congr rfl fun x' hx' => ?_
        rw [Finset.sum_congr rfl fun x hx => hsplit x' hx' x hx,
          Finset.sum_add_distrib,
          ← Finset.card_filter (fun x : ℤ => x = x') W]
    _ = W.card + collisionPairs W p := by
        rw [Finset.sum_add_distrib, hcoll]
        have hcard : ∑ x' ∈ W, (W.filter (fun x => x = x')).card = W.card := by
          rw [Finset.sum_congr rfl fun x' hx' => hsingleton x' hx',
            Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
        rw [hcard]

/-- The class-count sum is the total: `Σ_y z_y = |W|` (each element of `W`
lies in exactly one residue class). -/
theorem sum_classes_eq_card (W : Finset ℤ) {p : ℕ} (_hp : 0 < p) :
    ∑ y ∈ W.image (fun x => x % (p : ℤ)),
        (W.filter (fun x => x % (p : ℤ) = y)).card
      = W.card := by
  classical
  have hmem : ∀ x ∈ W, x % (p : ℤ) ∈ W.image (fun x => x % (p : ℤ)) := fun x hx =>
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hstep2 : (∑ y ∈ W.image (fun x => x % (p : ℤ)),
        ∑ x' ∈ W.filter (fun x => x % (p : ℤ) = y), (1 : ℕ))
      = ∑ x' ∈ W, ∑ y ∈ W.image (fun x => x % (p : ℤ)),
          (if x' % (p : ℤ) = y then (1 : ℕ) else 0) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  have hstep3 : ∀ x' ∈ W,
      (∑ y ∈ W.image (fun x => x % (p : ℤ)),
          (if x' % (p : ℤ) = y then (1 : ℕ) else 0)) = 1 := by
    intro x' hx'
    rw [Finset.sum_ite_eq, ite_eq_left (hmem x' hx')]
  calc ∑ y ∈ W.image (fun x => x % (p : ℤ)),
        (W.filter (fun x => x % (p : ℤ) = y)).card
      = ∑ y ∈ W.image (fun x => x % (p : ℤ)),
          ∑ x' ∈ W.filter (fun x => x % (p : ℤ) = y), (1 : ℕ) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
    _ = ∑ x' ∈ W, ∑ y ∈ W.image (fun x => x % (p : ℤ)),
          (if x' % (p : ℤ) = y then (1 : ℕ) else 0) := hstep2
    _ = ∑ _x' ∈ W, (1 : ℕ) := Finset.sum_congr rfl hstep3
    _ = W.card := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]

/-- Step 4's second moment in expectation form with the (F4) dispatch:
`E_{P'} Σ_y z_y² ≤ |W| + |W|²·K·B·L/2^L` — the paper's
«E_{P'} Σ_y z_y² ≤ B_S + K₀n²B_S²2^{−γm}» with the constant explicit. -/
theorem expect_sum_sq_le_L25 (W : Finset ℤ) {L B : ℕ} {K : ℝ}
    (hK : 0 < K)
    (hbits : ∀ x ∈ W, ∀ x' ∈ W, x ≠ x' → ((x - x').natAbs : ℝ) < (2 : ℝ) ^ B)
    (hF4 : ∀ x ∈ W, ∀ x' ∈ W, x ≠ x' → ((x - x').natAbs : ℝ) < (2 : ℝ) ^ B →
      (primesInterval L).expect (fun (q : ℕ) => if (↑q : ℤ) ∣ (x - x') then (1 : ℝ) else 0)
        ≤ K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L) :
    (primesInterval L).expect
        (fun q => (((∑ y ∈ W.image (fun x => x % (q : ℤ)),
            (W.filter (fun x => x % (q : ℤ) = y)).card ^ 2 : ℕ) : ℝ)))
      ≤ (W.card : ℝ) + (W.card : ℝ) ^ 2 * (K * (B : ℝ) * (L : ℝ) / (2 : ℝ) ^ L) := by
  classical
  have hpoint : ∀ q ∈ primesInterval L,
      (((∑ y ∈ W.image (fun x => x % (q : ℤ)),
          (W.filter (fun x => x % (q : ℤ) = y)).card ^ 2 : ℕ) : ℝ))
        = (W.card : ℝ) + (collisionPairs W q : ℝ) := by
    intro q hq
    have hq1 : 0 < q := by
      rcases Finset.mem_filter.mp hq with ⟨hqI, -⟩
      have hlo : (2 : ℕ) ^ L ≤ q := (Finset.mem_Ico.mp hqI).1
      have hpos2 : 0 < (2 : ℕ) ^ L := pow_pos (by norm_num) L
      omega
    rw [sum_sq_classes_eq_card_add_collisionPairs W hq1, Nat.cast_add]
  rw [Finset.expect_congr rfl hpoint]
  have hcp := collisionPairs_expect_le_L25 W hK hbits hF4
  by_cases hP : (primesInterval L).card = 0
  · -- empty interval: the expectation is 0, and the bound holds outright
    have hE : (primesInterval L) = ∅ := Finset.card_eq_zero.mp hP
    rw [hE, Finset.expect_empty]
    have hq : (0 : ℝ) ≤ K * ↑B * ↑L / 2 ^ ↑L :=
      div_nonneg (mul_nonneg (mul_nonneg (le_of_lt hK) (Nat.cast_nonneg B))
        (Nat.cast_nonneg L)) (by positivity)
    exact add_nonneg (Nat.cast_nonneg W.card) (mul_nonneg (sq_nonneg (W.card : ℝ)) hq)
  · -- nonempty: the add-a-constant shift of the expectation + the collision bound
    have hcard : (0 : ℝ) < (primesInterval L).card := by
      exact_mod_cast Nat.pos_of_ne_zero hP
    have hshift : (primesInterval L).expect
          (fun q => (W.card : ℝ) + (collisionPairs W q : ℝ))
        = (W.card : ℝ)
          + (primesInterval L).expect (fun q => (collisionPairs W q : ℝ)) := by
      rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, add_div,
        mul_div_cancel_left₀ (W.card : ℝ) (ne_of_gt hcard)]
    rw [hshift]
    linarith

/-! ### DS-M4 Step 4 — Markov over P′ -/

/-- The below-twice-the-mean event has probability at least `1/2` — the
generic form of the paper's «By Markov's inequality, with probability at
least 1/2 over P', Σ_y z_y² is at most twice that bound» (our DS-M2
`expect_tail_prob_le` is the ≤-tail; this is its complement).  Needs `s`
nonempty: an empty average is `0/0 = 0` junk. -/
theorem prob_le_twice_mean_ge_half {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) (hs : 0 < s.card) :
    (1 : ℝ) / 2 ≤
      ((s.filter (fun a => f a ≤ 2 * s.expect f)).card : ℝ) / s.card := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs
  by_cases hμ : s.expect f = 0
  · -- mean 0 with nonneg entries forces f = 0 pointwise, so the filter is all of s
    have hsum0 : ∑ a ∈ s, f a = 0 := by
      rw [Finset.expect_eq_sum_div_card] at hμ
      rcases div_eq_zero_iff.mp hμ with h | h
      · exact h
      · exact absurd (Nat.cast_eq_zero.mp h) (ne_of_gt hs)
    have hzero : ∀ a ∈ s, f a = 0 :=
      fun a ha => (Finset.sum_eq_zero_iff_of_nonneg hf).mp hsum0 a ha
    have hall : s.filter (fun a => f a ≤ 2 * s.expect f) = s := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro ha
        exact ⟨ha, by rw [hzero a ha, hμ]; norm_num⟩
    rw [hall, div_self (ne_of_gt hcard)]
    norm_num
  · have hμpos : 0 < s.expect f :=
      lt_of_le_of_ne (Finset.expect_nonneg hf) (Ne.symm hμ)
    -- the ≤-tail has probability ≤ 1/2 (DS-M2's Markov step)
    have htail := expect_tail_prob_le s f hf rfl hμpos (t := 2) (by norm_num)
    -- {2μ < f} ⊆ {2μ ≤ f}
    have hsub : (s.filter (fun a => 2 * s.expect f < f a)) ⊆
        s.filter (fun a => 2 * s.expect f ≤ f a) := by
      intro a ha
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp ha).1, le_of_lt (Finset.mem_filter.mp ha).2⟩
    -- complement: {f ≤ 2μ} = s ∖ {2μ < f}
    have hcomp := Finset.card_filter_add_card_filter_not
      (p := fun a => f a ≤ 2 * s.expect f) (s := s)
    have hnot : s.filter (fun a => ¬ (f a ≤ 2 * s.expect f))
        = s.filter (fun a => 2 * s.expect f < f a) :=
      Finset.filter_congr fun a _ => by rw [not_le]
    rw [hnot] at hcomp
    have hcardle : ((s.filter (fun a => 2 * s.expect f < f a)).card : ℝ)
        ≤ ((s.filter (fun a => 2 * s.expect f ≤ f a)).card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hsub
    have h2 : ((s.filter (fun a => 2 * s.expect f < f a)).card : ℝ) / s.card ≤ 1 / 2 :=
      le_trans (div_le_div_of_nonneg_right hcardle (le_of_lt hcard)) htail
    have h3 : ((s.filter (fun a => f a ≤ 2 * s.expect f)).card : ℝ) / s.card
        + ((s.filter (fun a => 2 * s.expect f < f a)).card : ℝ) / s.card = 1 := by
      have hcast : (((s.filter (fun a => f a ≤ 2 * s.expect f)).card
          + (s.filter (fun a => 2 * s.expect f < f a)).card : ℕ) : ℝ) = s.card := by
        exact_mod_cast hcomp
      rw [Nat.cast_add] at hcast
      rw [← add_div, hcast, div_self (ne_of_gt hcard)]
    linarith

/-! ### DS-M4 Step 4 — Cauchy–Schwarz occupancy and the hit probability -/

/-- Step 4's Cauchy–Schwarz occupancy: `|W|² ≤ Σ_y z_y² · #{occupied residues}`
(the paper's `(Σ_y z_y)² ≤ #{y : z_y > 0} · Σ_y z_y²`, with `Σ_y z_y = |W|`). -/
theorem card_sq_le_sum_sq_mul_occupied (W : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    (W.card : ℕ) ^ 2
      ≤ (∑ y ∈ W.image (fun x => x % (p : ℤ)),
            (W.filter (fun x => x % (p : ℤ) = y)).card ^ 2)
          * (W.image (fun x => x % (p : ℤ))).card := by
  classical
  have hsumz := sum_classes_eq_card W hp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ)
    (W.image (fun x => x % (p : ℤ)))
    (fun y => (W.filter (fun x => x % (p : ℤ) = y)).card) (fun _ => 1)
  have h1 : ∀ y ∈ W.image (fun x => x % (p : ℤ)),
      (W.filter (fun x => x % (p : ℤ) = y)).card * 1
        = (W.filter (fun x => x % (p : ℤ) = y)).card := fun _ _ => mul_one _
  have h2 : (∑ _y ∈ W.image (fun x => x % (p : ℤ)), (1 : ℕ) ^ 2)
      = (W.image (fun x => x % (p : ℤ))).card := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, one_pow, mul_one]
  rw [Finset.sum_congr rfl h1, h2, pow_two, hsumz] at hcs
  rw [pow_two]
  exact hcs

/-- Step 4, per-prime conclusion: on the good-prime event `Σ_y z_y² ≤ C`, a
uniform `j′` hits an occupied residue of `W` with probability at least
`|W|²/(P′·C)` — C–S occupancy times the residue bijection
(`hit_prob_eq_occupied`). -/
theorem hit_prob_ge_of_sum_sq_le (W : Finset ℤ) {p : ℕ} (hp : 0 < p) {C : ℕ}
    (hC : 0 < C)
    (hsq : ∑ y ∈ W.image (fun x => x % (p : ℤ)),
        (W.filter (fun x => x % (p : ℤ) = y)).card ^ 2 ≤ C) :
    (W.card : ℝ) ^ 2 / ((p : ℝ) * (C : ℝ)) ≤
      (Finset.range p).expect
        (fun (j : ℕ) => if ∃ x ∈ W, x % (p : ℤ) = (↑j : ℤ) then (1 : ℝ) else 0) := by
  classical
  rw [hit_prob_eq_occupied W hp]
  have hocc := card_sq_le_sum_sq_mul_occupied W hp
  have hoccC : ((W.card : ℕ) ^ 2 : ℝ) ≤ (C : ℝ)
      * ((W.image (fun x => x % (p : ℤ))).card : ℝ) := by
    have hle := Nat.mul_le_mul_right (W.image (fun x => x % (p : ℤ))).card hsq
    exact_mod_cast le_trans hocc hle
  have hpP : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpC : (0 : ℝ) < (p : ℝ) * (C : ℝ) := by
    exact mul_pos hpP (by exact_mod_cast hC)
  rw [div_le_div_iff₀ hpC hpP]
  calc (W.card : ℝ) ^ 2 * (p : ℝ)
      ≤ ((C : ℝ) * ((W.image (fun x => x % (p : ℤ))).card : ℝ)) * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hoccC (by exact_mod_cast (Nat.zero_le p))
    _ = ((W.image (fun x => x % (p : ℤ))).card : ℝ) * ((p : ℝ) * (C : ℝ)) := by ring

/-! ### DS-M4 Step 5 — the recovery walk -/

/-- The right-involutive companion of M3's `symmDiff_left_involutive`:
`(Z ∆ F) ∆ F = Z` (Step 5's «Since S ∆ F = I ∩ M», with S = (I ∩ M) ∆ F). -/
theorem symmDiff_right_involutive (Z F : Finset (Fin n)) : (Z ∆ F) ∆ F = Z := by
  rw [symmDiff_comm', symmDiff_comm' Z F, symmDiff_left_involutive]

/-- The partition of a sum over a covered triple: with `I ⊆ A₁ ∪ A₂ ∪ A₃`
and the three parts pairwise disjoint, `w(I)` splits over `I ∩ A₁, I ∩ A₂,
I ∩ A₃` — the paper's `b(A) + b(Z) + b(B) = b(I)` with `A = I ∩ L`,
`Z = I ∩ M`, `B = I ∩ R`. -/
theorem subsum_eq_sum_of_union_cover {w : Fin n → ℤ} {A₁ A₂ A₃ I : Finset (Fin n)}
    (hcover : I ⊆ A₁ ∪ A₂ ∪ A₃)
    (h12 : Disjoint A₁ A₂) (h13 : Disjoint A₁ A₃) (h23 : Disjoint A₂ A₃) :
    subsum w I = subsum w (I ∩ A₁) + subsum w (I ∩ A₂) + subsum w (I ∩ A₃) := by
  classical
  have hd12 : Disjoint (I ∩ A₁) (I ∩ A₂) :=
    h12.mono Finset.inter_subset_right Finset.inter_subset_right
  have hd13 : Disjoint (I ∩ A₁) (I ∩ A₃) :=
    h13.mono Finset.inter_subset_right Finset.inter_subset_right
  have hd23 : Disjoint (I ∩ A₂) (I ∩ A₃) :=
    h23.mono Finset.inter_subset_right Finset.inter_subset_right
  have hd : Disjoint (I ∩ A₁ ∪ I ∩ A₂) (I ∩ A₃) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    rcases Finset.mem_union.mp h1 with h | h
    · exact Finset.disjoint_left.mp hd13 h h2
    · exact Finset.disjoint_left.mp hd23 h h2
  have hunion : I ∩ A₁ ∪ I ∩ A₂ ∪ I ∩ A₃ = I := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ((⟨hI, _⟩ | ⟨hI, _⟩) | ⟨hI, _⟩)
      · exact hI
      · exact hI
      · exact hI
    · intro hI
      rcases Finset.mem_union.mp (hcover hI) with h | h
      · rcases Finset.mem_union.mp h with h' | h'
        · exact Or.inl (Or.inl ⟨hI, h'⟩)
        · exact Or.inl (Or.inr ⟨hI, h'⟩)
      · exact Or.inr ⟨hI, h⟩
  show I.sum w = (I ∩ A₁).sum w + (I ∩ A₂).sum w + (I ∩ A₃).sum w
  conv_lhs => rw [← hunion]
  rw [Finset.sum_union hd, Finset.sum_union hd12]

/-- Step 5's walk identity («(5.1) gives b(A) + b^F(X) + b(B) + b^F(Y) =
b(A) + b(B) + b(I ∩ M) − b(F) = T_{s,q} − b(F)»): with `S = (I ∩ M) ∆ F`,
`X ⊆ S` and `Y = S \ X`, the four walked values add up to `w(I) − w(F)` —
the unreduced sum.  The (5.1) identity `subsum_sgnW_eq` (DS-M1) and the
right involution turn the signed sums into the unreduced `w(I ∩ M) − w(F)` -/
theorem recovery_walk_eq (w : Fin n → ℤ) {L M R I X F : Finset (Fin n)}
    (hcover : I ⊆ L ∪ M ∪ R) (hlm : Disjoint L M) (hlr : Disjoint L R)
    (hmr : Disjoint M R) (hX : X ⊆ (I ∩ M) ∆ F) :
    subsum w (I ∩ L) + ∑ i ∈ X, sgnW w F i
        + (subsum w (I ∩ R) + ∑ i ∈ ((I ∩ M) ∆ F) \ X, sgnW w F i)
      = subsum w I - subsum w F := by
  classical
  have hpart := subsum_eq_sum_of_union_cover (w := w) hcover hlm hlr hmr
  have hsumS := subsum_sgnW_eq w F ((I ∩ M) ∆ F)
  rw [symmDiff_right_involutive] at hsumS
  have hsplit := Finset.sum_sdiff (f := fun i => sgnW w F i) hX
  linarith

/-- Step 5's residue form («So the class record (κ(B), λ(Y)) has the residue
T^F − j′»): a hit `j′ ≡ b(A) + b^F(X) (mod P′)` forces the complementary
record `b(B) + b^F(Y)` to the residue `T − b(F) − j′`, where `T = b(I)` is
the alias's `b`-sum (the paper's `T_{s,q}`). -/
theorem complement_record_residue_eq {b : Fin n → ℤ} {L M R I X F : Finset (Fin n)}
    {_P T _ts : ℤ} (hcover : I ⊆ L ∪ M ∪ R) (hlm : Disjoint L M) (hlr : Disjoint L R)
    (hmr : Disjoint M R) (hX : X ⊆ (I ∩ M) ∆ F) (hbI : subsum b I = T)
    {p' : ℕ} (j' : ℤ)
    (hhit : (subsum b (I ∩ L) + ∑ i ∈ X, sgnW b F i) % (p' : ℤ) = j' % (p' : ℤ)) :
    (subsum b (I ∩ R) + ∑ i ∈ ((I ∩ M) ∆ F) \ X, sgnW b F i) % (p' : ℤ)
      = (T - subsum b F - j') % (p' : ℤ) := by
  have hw := recovery_walk_eq (w := b) hcover hlm hlr hmr hX
  rw [hbI] at hw
  have hkey : subsum b (I ∩ R) + ∑ i ∈ ((I ∩ M) ∆ F) \ X, sgnW b F i
      = T - subsum b F - (subsum b (I ∩ L) + ∑ i ∈ X, sgnW b F i) := by linarith
  rw [hkey]
  exact Int.ModEq.sub_left _ hhit

/-- Step 5's insertion content («The expansion … inserts (κ(A), κ(B),
(X ∪ Y) ∆ F) = (κ(A), κ(B), I ∩ M)»): the key-triple the trial's expansion
inserts is exactly the class key of `I` itself — `I` lies in its own class,
unconditionally (the hit is the algorithmic trigger; by
`mem_cls_key_unique` the triple is THE key of `I`'s class). -/
theorem mem_cls_self (c b : Fin n → ℤ) {L M R I : Finset (Fin n)}
    (hcover : I ⊆ L ∪ M ∪ R) (_hlm : Disjoint L M) (_hlr : Disjoint L R)
    (_hmr : Disjoint M R) :
    I ∈ cls c b L R (keyOf c b (I ∩ L)) (keyOf c b (I ∩ R)) (I ∩ M) := by
  rw [cls, Finset.mem_image]
  refine ⟨(I ∩ L, I ∩ R), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, rfl⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, rfl⟩
  · ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ((⟨hI, _⟩ | ⟨hI, _⟩) | ⟨hI, _⟩)
      · exact hI
      · exact hI
      · exact hI
    · intro hI
      rcases Finset.mem_union.mp (hcover hI) with h | h
      · rcases Finset.mem_union.mp h with h' | h'
        · exact Or.inl (Or.inl ⟨hI, h'⟩)
        · exact Or.inl (Or.inr ⟨hI, h'⟩)
      · exact Or.inr ⟨hI, h⟩

/-- Step 5's «not in the skipped interval» core: the unreduced `c`-walk sum
`c(I) − c(F)` differs from the target's `t_s − c(F)`, because `I` is an
alias (`c(I) ≠ t_s`). -/
theorem c_walk_differs_from_target {c : Fin n → ℤ} {I F : Finset (Fin n)}
    {ts : ℤ} (hcI : subsum c I ≠ ts) :
    subsum c I - subsum c F ≠ ts - subsum c F := by
  intro h
  exact hcI (by linarith)

end SubsetSumL25
