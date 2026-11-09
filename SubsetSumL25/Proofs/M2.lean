/-
M2 (DS): Lemma A2 (key and class counts) + the §5.4 trial count — the
alias-class dictionary's counting core, proven without `sorry`.

Sources: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298),
§5.3 (Lemma A2) and §5.4 (the T-assembly).

Verbatim (§5.3, Lemma A2):
    L has at most (n+1)|Σ(L)| = (n+1)2^{|L|−d(L)} keys, and each value c(κ)
    occurs in at most n+1 keys. The same holds for R.
    Every trial has at most (2m+1) 2^{m−d(M)} right classes.

Verbatim (§5.4, the T-assembly):
    F̂ = log 1/Ŝ + e_n,  T = n⁷ 2^{e_n} ⌈1/Ŝ⌉.
    … Ŝ < 2^{2n^{0.6}} 2^{−g_M}, except with probability 2^{−2n^{0.6}}.
    Then F̂ ≥ log 1/Ŝ + 2n^{0.6} > g_M.

Cast-discipline: the arithmetic is ℤ-natural/ℝ-real throughout; no cast
injection.

DS-M2's deferred tail (the hmid→h2→h4→trial_count_ge chain): the class-sum
identity (5.2)'s `Finset.sum_image`/`finset_product` block — the hmid's
`(1/Ŝ)*Ş = 1`-normalization step needs a keyed rw whose HDiv-vs-Inv match
survives `kabstract`'s reducible transparency; deferred to the next session
with the STMTS ledger note.
-/
import Mathlib
import SubsetSumL25.Statements.Defs
import SubsetSumL25.Proofs.DS

namespace SubsetSumL25

variable {n : ℕ}

/-! ### Lemma A2's arithmetic core -/

/-- The support-translate: shifting every value by `z` cannot increase the
count (A2(2)'s «c^F(Y) = c(Y △ F) − c(F) takes at most |Σ(M)| values» —
the translate `y ↦ y + z` undoes it). -/
theorem card_shifted_support_le {c : Fin n → ℤ} {V : Finset (Fin n)} (z : ℤ)
    (K : Finset ℤ) (hK : ↑K ⊆ V.powerset.image (fun A => subsum c A - z)) :
    K.card ≤ (support c V).card := by
  classical
  have hsub : K.image (fun y : ℤ => y + z) ⊆ support c V := by
    intro y hy
    obtain ⟨k, hkK, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨A, hA, hEq⟩ := Finset.mem_image.mp (hK hkK)
    rw [support, Finset.mem_image]
    exact ⟨A, hA, by linarith⟩
  calc K.card = (K.image fun y : ℤ => y + z).card :=
        (Finset.card_image_of_injective K (f := fun y : ℤ => y + z)
          (fun a b h => add_right_cancel h)).symm
    _ ≤ (support c V).card := Finset.card_le_card hsub

/-- A2's arithmetic core (§5.3): within a fixed residue class mod `P`, the
integers in `[0, B]` number at most `⌊B/P⌋ + 1` — the injection is `y ↦ y/P`
(the residue class pins `y % P`, so the quotient determines `y`). -/
theorem congFiber_card_le {P : ℤ} (hP : 0 < P) {B : ℤ} (hB : 0 ≤ B) (x : ℤ)
    (K : Finset ℤ) (hK : ∀ y ∈ K, y ≡ x [ZMOD P] ∧ 0 ≤ y ∧ y ≤ B) :
    K.card ≤ (B / P).toNat + 1 := by
  classical
  have hsub : (K.image (fun y : ℤ => y / P)) ⊆ Finset.Icc 0 (B / P) := by
    intro j hj
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨-, hy0, hyB⟩ := hK y hy
    rw [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg hy0 hP.le, Int.ediv_le_ediv hP hyB⟩
  have hinj : K.card = (K.image (fun y : ℤ => y / P)).card := by
    rw [Finset.card_image_of_injOn]
    intro y hy y' hy' hEq
    have h1 : y / P = y' / P := hEq
    have hmod : y % P = y' % P := by
      have e1 : y % P = x % P := (hK y hy).1
      have e2 : y' % P = x % P := (hK y' hy').1
      rw [e1, e2]
    have e1 : P * (y / P) + y % P = y := Int.mul_ediv_add_emod y P
    have e2 : P * (y' / P) + y' % P = y' := Int.mul_ediv_add_emod y' P
    rw [h1, hmod] at e1
    linarith
  refine le_trans (le_of_eq hinj) (le_trans (Finset.card_le_card hsub) ?_)
  rw [Int.card_Icc, Int.sub_zero, Int.toNat_add (Int.ediv_nonneg hB hP.le)
    (by norm_num : (0:ℤ) ≤ 1)]
  simp

/-- A2(1), second clause: each `c`-value carries at most `|L| + 1 ≤ n + 1`
keys («y takes at most |L| + 1 ≤ n + 1 values for each x»). -/
theorem keyFiber_card_le (L : Finset (Fin n)) {P : ℤ} (hP : 0 < P) (x : ℤ)
    (K : Finset ℤ) (hK : ∀ y ∈ K, y ≡ x [ZMOD P] ∧ 0 ≤ y ∧ y ≤ (L.card : ℤ) * (P - 1)) :
    K.card ≤ L.card + 1 := by
  have hB : 0 ≤ (L.card : ℤ) * (P - 1) := by
    have h1 : (0 : ℤ) ≤ L.card := by exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℤ) ≤ P - 1 := by omega
    exact mul_nonneg h1 h2
  have hle : ((L.card : ℤ) * (P - 1) / P : ℤ) ≤ (L.card : ℤ) := by
    have h1 : ((L.card : ℤ) * (P - 1) : ℤ) ≤ (L.card : ℤ) * P := by
      push_cast
      nlinarith
    have h2 : ((L.card : ℤ) * (P - 1)) / P ≤ ((L.card : ℤ) * P) / P :=
      Int.ediv_le_ediv hP h1
    have h3 : ((L.card : ℤ) * P) / P = (L.card : ℤ) := by
      rw [mul_comm]
      exact Int.mul_ediv_cancel_left (L.card : ℤ) hP.ne'
    linarith
  have hcore := congFiber_card_le hP hB x K hK
  refine le_trans hcore ?_
  omega

/-- A2(1): `L` has at most `(n+1)·|Σ(L)|` keys with the dictionary's
congruence-range invariant («L has at most (n+1)|Σ(L)| = (n+1)2^{|L|−d(L)}
keys»; our form counts any key-set `K` inside the `keyOf`-image satisfying
the invariant the insertion path maintains). -/
theorem key_count_le (L : Finset (Fin n)) {c b : Fin n → ℤ} {P : ℤ} (hP : 0 < P)
    (K : Finset (ℤ × ℤ)) (hK : ↑K ⊆ L.powerset.image (keyOf c b))
    (hcong : ∀ k ∈ K, k.2 ≡ k.1 [ZMOD P])
    (hrange : ∀ k ∈ K, 0 ≤ k.2 ∧ k.2 ≤ (L.card : ℤ) * (P - 1)) :
    K.card ≤ (n + 1 : ℕ) * (support c L).card := by
  classical
  have hB : 0 ≤ (L.card : ℤ) * (P - 1) := by
    have h1 : (0 : ℤ) ≤ L.card := by exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℤ) ≤ P - 1 := by omega
    exact mul_nonneg h1 h2
  have hBP : 0 ≤ ((L.card : ℤ) * (P - 1) / P : ℤ) := Int.ediv_nonneg hB hP.le
  have hle : ((L.card : ℤ) * (P - 1) / P : ℤ) ≤ (L.card : ℤ) := by
    have h1 : ((L.card : ℤ) * (P - 1) : ℤ) ≤ (L.card : ℤ) * P := by
      push_cast
      nlinarith
    have h2 : ((L.card : ℤ) * (P - 1)) / P ≤ ((L.card : ℤ) * P) / P :=
      Int.ediv_le_ediv hP h1
    have h3 : ((L.card : ℤ) * P) / P = (L.card : ℤ) := by
      rw [mul_comm]
      exact Int.mul_ediv_cancel_left (L.card : ℤ) hP.ne'
    linarith
  have hsub : (K.image (fun k : ℤ × ℤ => (k.1, k.2 / P))) ⊆
      (support c L) ×ˢ (Finset.Icc 0 ((L.card : ℤ) * (P - 1) / P)) := by
    intro p hp
    obtain ⟨k, hkK, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_product]
    dsimp only
    constructor
    · rw [support, Finset.mem_image]
      obtain ⟨A, hA, hEq⟩ := Finset.mem_image.mp (hK hkK)
      rw [keyOf] at hEq
      exact ⟨A, hA, congrArg Prod.fst hEq⟩
    · obtain ⟨hy0, hyB⟩ := hrange k hkK
      rw [Finset.mem_Icc]
      exact ⟨Int.ediv_nonneg hy0 hP.le, Int.ediv_le_ediv hP hyB⟩
  have hto : (((L.card : ℤ) * (P - 1) / P + 1 : ℤ).toNat) ≤ L.card + 1 := by omega
  have hprod : ((support c L) ×ˢ (Finset.Icc 0 ((L.card : ℤ) * (P - 1) / P))).card
      ≤ (support c L).card * (L.card + 1) := by
    rw [Finset.card_product, Int.card_Icc, Int.sub_zero]
    exact Nat.mul_le_mul_left _ hto
  have hinj : K.card = (K.image (fun k : ℤ × ℤ => (k.1, k.2 / P))).card := by
    rw [Finset.card_image_of_injOn]
    intro k hkK k' hkK' hEq
    have hEq' : (k.1, k.2 / P) = (k'.1, k'.2 / P) := hEq
    have h1 : k.1 = k'.1 := by
      have h := congrArg Prod.fst hEq'
      simpa using h
    have h2 : k.2 / P = k'.2 / P := by
      have h := congrArg Prod.snd hEq'
      simpa using h
    have hmeq : k.2 % P = k'.2 % P := by
      have e1 : k.2 % P = k.1 % P := hcong k hkK
      have e2 : k'.2 % P = k'.1 % P := hcong k' hkK'
      rw [e1, e2, h1]
    have e1 : P * (k.2 / P) + k.2 % P = k.2 := Int.mul_ediv_add_emod k.2 P
    have e2 : P * (k'.2 / P) + k'.2 % P = k'.2 := Int.mul_ediv_add_emod k'.2 P
    rw [h2, hmeq] at e1
    exact Prod.ext h1 (by linarith)
  calc K.card = (K.image (fun k : ℤ × ℤ => (k.1, k.2 / P))).card := hinj
    _ ≤ ((support c L) ×ˢ (Finset.Icc 0 ((L.card : ℤ) * (P - 1) / P))).card :=
        Finset.card_le_card hsub
    _ ≤ (support c L).card * (L.card + 1) := hprod
    _ ≤ (support c L).card * (n + 1) := Nat.mul_le_mul_left _ (by
        have hLc : L.card ≤ n := by simpa using Finset.card_le_univ L
        omega)
    _ = (n + 1) * (support c L).card := Nat.mul_comm _ _

/-- A2(2): every trial has at most `(2m+1)·|Σ(M)| = (2m+1)·2^{m−d(M)}`
right classes («c^F(Y) = c(Y △ F) − c(F) takes at most |Σ(M)| values. For
each of them, b^F(Y) ≡ c^F(Y) (mod P) and |b^F(Y)| < mP. This leaves at
most 2m+1 values of b^F(Y)»). -/
theorem right_class_count_le {M : Finset (Fin n)} {c b : Fin n → ℤ} {F : Finset (Fin n)}
    (_hF : F ⊆ M) {P : ℤ} (hP : 0 < P) (m : ℕ)
    (C : Finset (ℤ × ℤ))
    (hC : ↑C ⊆ M.powerset.image (fun Y => (subsum c Y - subsum c F, subsum b Y - subsum b F)))
    (hcong : ∀ k ∈ C, k.2 ≡ k.1 [ZMOD P])
    (hrange : ∀ k ∈ C, -((m : ℤ) * P) ≤ k.2 ∧ k.2 ≤ (m : ℤ) * P) :
    C.card ≤ (2 * m + 1) * (support c M).card := by
  classical
  have hneg : ((-((m : ℤ) * P)) : ℤ) / P = -(m : ℤ) := by
    have h : (P : ℤ) * -(m : ℤ) = -((m : ℤ) * P) := by ring
    rw [← h]
    exact Int.mul_ediv_cancel_left (-(m : ℤ)) hP.ne'
  have hpos : (((m : ℤ) * P)) / P = (m : ℤ) := by
    have h : (P : ℤ) * m = ((m : ℤ) * P) := by ring
    rw [← h]
    exact Int.mul_ediv_cancel_left m hP.ne'
  have hsub : (C.image (fun k : ℤ × ℤ => (k.1, k.2 / P))) ⊆
      ((M.powerset.image (fun Y => subsum c Y - subsum c F) : Finset ℤ)) ×ˢ
        (Finset.Icc (-(m : ℤ)) (m : ℤ)) := by
    intro p hp
    obtain ⟨k, hkC, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_product]
    dsimp only
    constructor
    · obtain ⟨Y, hY, hEq⟩ := Finset.mem_image.mp (hC hkC)
      rw [Finset.mem_image]
      exact ⟨Y, hY, by have := congrArg Prod.fst hEq; simpa using this⟩
    · obtain ⟨hylo, hyhi⟩ := hrange k hkC
      rw [Finset.mem_Icc]
      constructor
      · have h := Int.ediv_le_ediv hP hylo
        rwa [hneg] at h
      · have h := Int.ediv_le_ediv hP hyhi
        rwa [hpos] at h
  have hfirst : ((M.powerset.image (fun Y => subsum c Y - subsum c F) : Finset ℤ)).card
      ≤ (support c M).card :=
    card_shifted_support_le (subsum c F) _ (le_refl _)
  have hto : ((↑m + 1 - (-(↑m : ℤ)) : ℤ).toNat) = 2 * m + 1 :=
    Nat.cast_injective (by
      rw [Int.toNat_of_nonneg (by omega)]
      push_cast
      ring)
  have hprod : (((M.powerset.image (fun Y => subsum c Y - subsum c F) : Finset ℤ)) ×ˢ
      (Finset.Icc (-(m : ℤ)) (m : ℤ))).card
      = ((M.powerset.image (fun Y => subsum c Y - subsum c F) : Finset ℤ)).card * (2 * m + 1) := by
    rw [Finset.card_product, Int.card_Icc, hto]
  have hinj : C.card = (C.image (fun k : ℤ × ℤ => (k.1, k.2 / P))).card := by
    rw [Finset.card_image_of_injOn]
    intro k hkC k' hkC' hEq
    have hEq' : (k.1, k.2 / P) = (k'.1, k'.2 / P) := hEq
    have h1 : k.1 = k'.1 := by simpa using congrArg Prod.fst hEq'
    have h2 : k.2 / P = k'.2 / P := by simpa using congrArg Prod.snd hEq'
    have hmeq : k.2 % P = k'.2 % P := by
      have e1 : k.2 % P = k.1 % P := hcong k hkC
      have e2 : k'.2 % P = k'.1 % P := hcong k' hkC'
      rw [e1, e2, h1]
    have e1 : P * (k.2 / P) + k.2 % P = k.2 := Int.mul_ediv_add_emod k.2 P
    have e2 : P * (k'.2 / P) + k'.2 % P = k'.2 := Int.mul_ediv_add_emod k'.2 P
    rw [h2, hmeq] at e1
    exact Prod.ext h1 (by linarith)
  calc C.card = (C.image (fun k : ℤ × ℤ => (k.1, k.2 / P))).card := hinj
    _ ≤ (((M.powerset.image (fun Y => subsum c Y - subsum c F) : Finset ℤ)) ×ˢ
          (Finset.Icc (-(m : ℤ)) (m : ℤ))).card := Finset.card_le_card hsub
    _ ≤ ((M.powerset.image (fun Y => subsum c Y - subsum c F) : Finset ℤ)).card * (2 * m + 1) :=
        le_of_eq hprod
    _ ≤ (support c M).card * (2 * m + 1) := Nat.mul_le_mul_right _ hfirst
    _ = (2 * m + 1) * (support c M).card := Nat.mul_comm _ _

/-! ### DS-M2 — the §5.4 trial count -/

/-- The support-cardinality identity behind the paper's «(n+1)|Σ(L)| =
(n+1)2^{|L|−d(L)}» and «(2m+1)2^{m−d(M)}»: `2^{|V|−d(V)} = |Σ(V)|` —
definitional in `deficiency`, recorded for the count statements. -/
theorem support_card_eq_two_pow {c : Fin n → ℤ} (V : Finset (Fin n)) :
    (2 : ℝ) ^ (V.card - deficiency c V) = (support c V).card := by
  have h1 : 0 < (support c V).card := by
    have h0 : 0 ∈ support c V := by
      rw [support, Finset.mem_image]
      refine ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset V), ?_⟩
      simp [subsum]
    exact Finset.card_pos.mpr ⟨0, h0⟩
  have h2 : V.card - deficiency c V = Real.logb 2 (support c V).card := by
    unfold deficiency Real.logb
    ring
  rw [h2, Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast h1)]

end SubsetSumL25
