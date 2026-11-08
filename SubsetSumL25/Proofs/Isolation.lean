/-
M3 (COMPLETE via M3a + M3b): PROOF of OpenAI Lemma 2.1 «Isolation», both
sentences.

Paper proof (setup.tex): «The identity c(I)=t_s gives C(a(I)−t)=s−u(I).  Since
s,u(I)∈[0,nN₀] and C>nN₀, this forces a(I)=t and u(I)=s.»

M3b (probabilistic half) follows the paper's MVV minimum-tie argument: fix i and
all tie weights off i; among solution subsets containing i the minimum tie weight
is (off-i minimum) + u_i, among those avoiding i it is a constant; the two
coincide for at most one value of u_i, and two distinct minimum-weight members of
F = {I : a(I)=t} differ at some such i.  Union bound: minimum unique with
probability ≥ 1 − n/N₀ ≥ 11/12 by 12n ≤ N₀.  In Lean no minima are computed: the
per-index coincidence event is captured by "two minimizers tie" (Cset i below);
two such configurations agreeing off i must agree at i because both tie equations
pin the same off-i difference, so coordinate-erasure is injective on Cset i.
-/
import Mathlib
import SubsetSumL25.Statements.Isolation

namespace SubsetSumL25

private theorem eq_zero_of_dvd_of_abs_lt {k m : ℤ} (hk : 0 < k) (hdvd : k ∣ m)
    (hlo : -k < m) (hhi : m < k) : m = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  by_contra hne
  have hq0 : q ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hq
    exact hne hq
  rcases Int.lt_trichotomy 0 q with hqpos | hqzero | hqneg
  · have hkq : k ≤ k * q := by
      calc k = k * 1 := (mul_one k).symm
        _ ≤ k * q := Int.mul_le_mul_of_nonneg_left hqpos hk.le
    exact absurd (show m < m by linarith [hq, hkq, hhi]) (by linarith)
  · exact hq0 hqzero.symm
  · have hqle : q ≤ -1 := by linarith
    have hkq : k * q ≤ -k := by
      calc k * q ≤ k * (-1) := Int.mul_le_mul_of_nonneg_left hqle hk.le
        _ = -k := by ring
    exact absurd (show m < m by linarith [hq, hkq, hlo]) (by linarith)

/-- The sum of tie weights of a subset is at most `n·N₀`. -/
private theorem sum_u_le {n N₀ : ℕ} (u : Fin n → Fin N₀) (I : Finset (Fin n)) :
    (∑ i ∈ I, (u i : ℕ)) ≤ n * N₀ := by
  calc ∑ i ∈ I, (u i : ℕ)
      ≤ I.card • (N₀ - 1) :=
        Finset.sum_le_card_nsmul I (fun i => (u i : ℕ)) (N₀ - 1)
          (fun i _ => Nat.le_sub_one_of_lt (Fin.is_lt (u i)))
    _ = I.card * (N₀ - 1) := rfl
    _ ≤ I.card * N₀ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ n * N₀ := by
        have h1 : I.card ≤ n := by simpa using I.card_le_univ
        exact Nat.mul_le_mul_right _ h1

/-- The decomposition of a transformed sum: `c(I) = C·a(I) + u(I)`. -/
private theorem subsum_transformed {n N₀ : ℕ} (a : Fin n → ℤ)
    (u : Fin n → Fin N₀) (I : Finset (Fin n)) :
    subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) I
      = transformedC n N₀ * subsum a I
        + ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
  unfold subsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- OpenAI L2.1, first sentence: the transformed equivalence. -/
theorem L2_1_isolation (a : Fin n → ℤ) (t : ℤ) (N₀ : ℕ)
    (u : Fin n → Fin N₀) :
    ((∃ I : Finset (Fin n), subsum a I = t) ↔
      (∃ s : ℕ, s ≤ n * N₀ ∧ ∃ I : Finset (Fin n),
        subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) I
          = transformedC n N₀ * t + s)) := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨(∑ i ∈ I, (u i : ℕ)), sum_u_le u I, I, by
      rw [subsum_transformed, hI, Nat.cast_sum]⟩
  · rintro ⟨s, hs, I, hI⟩
    rw [subsum_transformed] at hI
    have hCpos : (0 : ℤ) < transformedC n N₀ := by unfold transformedC; positivity
    have hCnN₀ : (n * N₀ : ℤ) < transformedC n N₀ := by
      unfold transformedC
      have : (0 : ℤ) ≤ n * N₀ := by positivity
      linarith
    have hsumle : (∑ i ∈ I, ((u i : ℕ) : ℤ)) ≤ (n * N₀ : ℤ) :=
      mod_cast sum_u_le u I
    have hsle : ((s : ℤ)) ≤ (n * N₀ : ℤ) := by exact_mod_cast hs
    have hkey : transformedC n N₀ * (subsum a I - t)
        = (s : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) := by linarith
    have hdvd : transformedC n N₀ ∣ ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) :=
      Dvd.intro (subsum a I - t) hkey
    have hlo : -(transformedC n N₀) < ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
      have h2 : (0 : ℤ) ≤ ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_nonneg _
      linarith
    have hhi : ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) < transformedC n N₀ := by
      have h2 : (0 : ℤ) ≤ ∑ i ∈ I, ((u i : ℕ) : ℤ) := by
        rw [← Nat.cast_sum]
        exact Nat.cast_nonneg _
      linarith
    have hm0 : ((s : ℕ) : ℤ) - ∑ i ∈ I, ((u i : ℕ) : ℤ) = 0 :=
      eq_zero_of_dvd_of_abs_lt hCpos hdvd hlo hhi
    have hzero : subsum a I - t = 0 := by
      rw [hm0] at hkey
      rcases mul_eq_zero.mp hkey with hC0 | hx0
      · exact absurd hC0 (by linarith)
      · exact hx0
    exact ⟨I, by linarith⟩

/-- OpenAI L2.1, second sentence: if the original instance has a solution, then
with probability at least 11/12 at least one transformed target `t_s` has exactly
one representing subset (probability = fraction of the uniform space
`Fin n → Fin N₀`, `12n ≤ N₀`). -/
theorem L2_1_isolation_prob (a : Fin n → ℤ) (t : ℤ) (N₀ : ℕ)
    (hN₀ : 12 * n ≤ N₀)
    (hsol : ∃ I : Finset (Fin n), subsum a I = t) :
    (11 : ℚ) / 12 ≤
      ((Finset.univ.filter (fun u : Fin n → Fin N₀ =>
          ∃ s ≤ n * N₀, ∃ I : Finset (Fin n),
            (Finset.univ.filter (fun J : Finset (Fin n) =>
                subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) J
                  = transformedC n N₀ * t + s)).card = 1)).card : ℚ) /
      (Fintype.card (Fin n → Fin N₀) : ℚ) := by
  classical
  set G : (Fin n → Fin N₀) → Prop := fun u : Fin n → Fin N₀ =>
    ∃ s ≤ n * N₀, ∃ I : Finset (Fin n),
      (Finset.univ.filter (fun J : Finset (Fin n) =>
          subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) J
            = transformedC n N₀ * t + s)).card = 1 with hGdef
  have huniv : Fintype.card (Fin n → Fin N₀) = N₀ ^ n := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- n = 0 : the space is a single function and it is good
    subst hn0
    obtain ⟨I₀, hI₀⟩ := hsol
    have hI₀e : I₀ = ∅ := Finset.ext fun j => Iff.intro (fun _ => j.elim0) (fun _ => j.elim0)
    have hI₀z : (0 : ℤ) = t := by
      rw [← hI₀, hI₀e]
      simp only [subsum, Finset.sum_empty]
    have hC1 : transformedC 0 N₀ = (1 : ℤ) := by simp [transformedC]
    set u₀ : Fin 0 → Fin N₀ := fun j => j.elim0 with hu₀
    have hall : ∀ J : Finset (Fin 0), J = ∅ := fun J =>
      Finset.ext fun j => Iff.intro (fun _ => j.elim0) (fun _ => j.elim0)
    have hempty_mem : ∅ ∈ Finset.univ.filter (fun J : Finset (Fin 0) =>
        subsum (fun i => transformedC 0 N₀ * a i + ((u₀ i : ℕ) : ℤ)) J
          = transformedC 0 N₀ * t + ((0 : ℕ) : ℤ)) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hC1, ← hI₀z]
      simp only [subsum, Finset.sum_empty]
      norm_num
    have hempty_sub : (Finset.univ.filter (fun J : Finset (Fin 0) =>
        subsum (fun i => transformedC 0 N₀ * a i + ((u₀ i : ℕ) : ℤ)) J
          = transformedC 0 N₀ * t + ((0 : ℕ) : ℤ))) ⊆ ({∅} : Finset (Finset (Fin 0))) :=
      fun J _ => by
        rw [hall J]
        exact Finset.mem_singleton_self ∅
    have hmem : u₀ ∈ Finset.univ.filter G := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hGdef]
      refine ⟨0, Nat.zero_le _, ∅, ?_⟩
      set Rf : Finset (Finset (Fin 0)) := Finset.univ.filter (fun J : Finset (Fin 0) =>
          subsum (fun i => transformedC 0 N₀ * a i + ((u₀ i : ℕ) : ℤ)) J
            = transformedC 0 N₀ * t + ((0 : ℕ) : ℤ)) with hRf
      have h1 : 0 < Rf.card := by
        rw [hRf]
        exact Finset.card_pos.mpr ⟨∅, hempty_mem⟩
      have h2 : Rf.card ≤ 1 := by
        rw [hRf]
        calc (Finset.univ.filter (fun J : Finset (Fin 0) =>
              subsum (fun i => transformedC 0 N₀ * a i + ((u₀ i : ℕ) : ℤ)) J
                = transformedC 0 N₀ * t + ((0 : ℕ) : ℤ))).card
            ≤ ({∅} : Finset (Finset (Fin 0))).card := Finset.card_le_card hempty_sub
          _ = 1 := Finset.card_singleton ∅
      omega
    have hge : 1 ≤ (Finset.univ.filter G).card := by
      have h : 0 < (Finset.univ.filter G).card := Finset.card_pos.mpr ⟨u₀, hmem⟩
      omega
    have hle2 : (Finset.univ.filter G).card ≤ Fintype.card (Fin 0 → Fin N₀) :=
      Finset.card_le_card fun x _ => Finset.mem_univ x
    rw [huniv, pow_zero] at hle2
    have heq1 : (Finset.univ.filter G).card = 1 := by omega
    rw [heq1, huniv, pow_zero]
    norm_num
  · -- 0 < n : the MVV union bound
    have hN₀pos : 0 < N₀ := by omega
    haveI : NeZero N₀ := ⟨by omega⟩
    obtain ⟨I₀, hI₀sol⟩ := hsol
    -- pointwise force: a representative of t_s (s ≤ nN₀) is a solution with u-sum s
    have force : ∀ (v : Fin n → Fin N₀) (J : Finset (Fin n)) (s : ℕ), s ≤ n * N₀ →
        subsum (fun i => transformedC n N₀ * a i + ((v i : ℕ) : ℤ)) J
          = transformedC n N₀ * t + ((s : ℕ) : ℤ) →
        subsum a J = t ∧ (∑ i ∈ J, (v i : ℕ)) = s := by
      intro v J s hs hcJ
      have hexp := subsum_transformed a v J
      rw [hexp] at hcJ
      have hCpos : (0 : ℤ) < transformedC n N₀ := by unfold transformedC; positivity
      have hCbig : (n * N₀ : ℤ) < transformedC n N₀ := by
        unfold transformedC
        have h : (0 : ℤ) ≤ n * N₀ := by positivity
        linarith
      have hsumle : ((∑ i ∈ J, ((v i : ℕ) : ℤ)) : ℤ) ≤ (n * N₀ : ℤ) :=
        mod_cast sum_u_le v J
      have hsle : ((s : ℕ) : ℤ) ≤ (n * N₀ : ℤ) := by exact_mod_cast hs
      have hsum0 : (0 : ℤ) ≤ (∑ i ∈ J, ((v i : ℕ) : ℤ)) := by
        rw [← Nat.cast_sum]; exact Nat.cast_nonneg _
      have hkey : transformedC n N₀ * (subsum a J - t)
          = ((s : ℕ) : ℤ) - (∑ i ∈ J, ((v i : ℕ) : ℤ)) := by linarith
      have hdvd : transformedC n N₀ ∣ (((s : ℕ) : ℤ) - (∑ i ∈ J, ((v i : ℕ) : ℤ))) :=
        Dvd.intro (subsum a J - t) hkey
      have hlo : -(transformedC n N₀) < ((s : ℕ) : ℤ) - (∑ i ∈ J, ((v i : ℕ) : ℤ)) := by
        linarith
      have hhi : ((s : ℕ) : ℤ) - (∑ i ∈ J, ((v i : ℕ) : ℤ)) < transformedC n N₀ := by
        linarith
      have hm : ((s : ℕ) : ℤ) - (∑ i ∈ J, ((v i : ℕ) : ℤ)) = 0 :=
        eq_zero_of_dvd_of_abs_lt hCpos hdvd hlo hhi
      rw [hm] at hkey
      rcases mul_eq_zero.mp hkey with h0 | hx0
      · exact absurd h0 (by linarith)
      · exact ⟨by linarith, by
          have hz : ((∑ i ∈ J, (v i : ℕ)) : ℤ) = ((s : ℕ) : ℤ) := by linarith
          exact_mod_cast hz⟩
    -- the solution family and its minimizers
    set F : Finset (Finset (Fin n)) := Finset.univ.filter (fun J => subsum a J = t) with hFdef
    have hI₀F : I₀ ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI₀sol⟩
    have hdiff : ∀ I J : Finset (Fin n), I ≠ J →
        ∃ i : Fin n, (i ∈ I ∧ i ∉ J) ∨ (i ∈ J ∧ i ∉ I) := by
      intro I J hIJ
      by_contra hcon
      have h1 : ∀ i, i ∈ I → i ∈ J := by
        intro i hi
        by_contra h9
        exact hcon ⟨i, Or.inl ⟨hi, h9⟩⟩
      have h2 : ∀ i, i ∈ J → i ∈ I := by
        intro i hi
        by_contra h9
        exact hcon ⟨i, Or.inr ⟨hi, h9⟩⟩
      exact hIJ (Finset.ext fun i => Iff.intro (h1 i) (h2 i))
    -- Cset i : configurations in which two distinct minimizers of u over F
    -- differ exactly at i (the paper's "two minima coincide" event)
    set Cset : Fin n → Finset (Fin n → Fin N₀) := fun i =>
      Finset.univ.filter (fun u : Fin n → Fin N₀ =>
        ∃ I J : Finset (Fin n), i ∈ I ∧ i ∉ J ∧ subsum a I = t ∧ subsum a J = t ∧
          (∀ K ∈ F, (∑ k ∈ I, (u k : ℕ)) ≤ (∑ k ∈ K, (u k : ℕ))) ∧
          (∑ k ∈ I, (u k : ℕ)) = (∑ k ∈ J, (u k : ℕ))) with hCsetdef
    -- W i : functions vanishing at coordinate i
    set W : Fin n → Finset (Fin n → Fin N₀) := fun i =>
      Finset.univ.filter (fun w : Fin n → Fin N₀ => w i = 0) with hWdef
    -- ¬G produces two distinct minimizers, hence membership in some Cset i
    have hext : ∀ u : Fin n → Fin N₀, ¬ G u → ∃ i : Fin n, u ∈ Cset i := by
      intro u hng
      simp only [hGdef] at hng
      obtain ⟨Im, hImF, hmin⟩ :=
        Finset.exists_min_image F (fun K => ∑ k ∈ K, (u k : ℕ)) ⟨I₀, hI₀F⟩
      have hsle : (∑ k ∈ Im, (u k : ℕ)) ≤ n * N₀ := sum_u_le u Im
      set s₀ : ℕ := (∑ k ∈ Im, (u k : ℕ)) with hs0
      set R : Finset (Finset (Fin n)) := Finset.univ.filter (fun J : Finset (Fin n) =>
          subsum (fun i => transformedC n N₀ * a i + ((u i : ℕ) : ℤ)) J
            = transformedC n N₀ * t + ((s₀ : ℕ) : ℤ)) with hRdef
      have hImR : Im ∈ R := by
        rw [hRdef]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [subsum_transformed a u Im, (Finset.mem_filter.mp hImF).2]
        have hcast : (∑ i ∈ Im, ((u i : ℕ) : ℤ)) = ((s₀ : ℕ) : ℤ) := by
          rw [← Nat.cast_sum, ← hs0]
        rw [hcast]
      have hRne : R.card ≠ 1 := by
        intro hc
        rw [hRdef] at hc
        exact hng ⟨s₀, hsle, Im, hc⟩
      have hRge : 1 ≤ R.card := by
        have h : 0 < R.card := Finset.card_pos.mpr ⟨Im, hImR⟩
        omega
      have hRlt : 1 < R.card := by omega
      obtain ⟨Ja, Jb, hJa, hJb, hne⟩ := Finset.one_lt_card_iff.mp hRlt
      obtain ⟨J, hJR, hJne⟩ : ∃ J ∈ R, J ≠ Im := by
        by_cases hca : Ja = Im
        · exact ⟨Jb, hJb, fun h => hne (hca.trans h.symm)⟩
        · exact ⟨Ja, hJa, hca⟩
      obtain ⟨-, hJc⟩ := Finset.mem_filter.mp hJR
      obtain ⟨haJ, huJ⟩ := force u J s₀ hsle hJc
      have hJF : J ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, haJ⟩
      have hminJ : ∀ K ∈ F, (∑ k ∈ J, (u k : ℕ)) ≤ (∑ k ∈ K, (u k : ℕ)) := fun K hK => by
        rw [huJ]; exact hmin K hK
      rcases hdiff Im J hJne.symm with ⟨i, hi | hi⟩
      · refine ⟨i, ?_⟩
        rw [hCsetdef]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨Im, J, hi.1, hi.2, (Finset.mem_filter.mp hImF).2, haJ, hmin, hs0.symm.trans huJ.symm⟩⟩
      · refine ⟨i, ?_⟩
        rw [hCsetdef]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨J, Im, hi.1, hi.2, haJ, (Finset.mem_filter.mp hImF).2, hminJ, huJ.trans hs0⟩⟩
    -- per-slice uniqueness: erasing coordinate i is injective on Cset i
    have hslice : ∀ (i : Fin n) (u u' : Fin n → Fin N₀), u ∈ Cset i → u' ∈ Cset i →
        (∀ k, k ≠ i → u k = u' k) → u = u' := by
      intro i u u' hu hu' hoff
      simp only [hCsetdef, Finset.mem_filter, Finset.mem_univ] at hu hu'
      obtain ⟨I, J, hiI, hiJ, hI, hJ, hminI, heqIJ⟩ := hu.2
      obtain ⟨I', J', hiI', hiJ', hI', hJ', hminI', heqIJ'⟩ := hu'.2
      have split : ∀ (v : Fin n → Fin N₀) (S : Finset (Fin n)), i ∈ S →
          (∑ k ∈ S, (v k : ℕ)) = ((v i : ℕ)) + (∑ k ∈ Finset.erase S i, (v k : ℕ)) := by
        intro v S hiS
        have hs2 : i ∉ Finset.erase S i := fun hm => absurd rfl (Finset.mem_erase.mp hm).1
        conv_lhs => rw [← Finset.insert_erase hiS]
        rw [Finset.sum_insert hs2]
      have eraseJ : ∀ (S : Finset (Fin n)), i ∉ S → Finset.erase S i = S := fun S hiS =>
        Finset.ext fun k => Iff.intro (fun hk => (Finset.mem_erase.mp hk).2)
          (fun hk => Finset.mem_erase.mpr ⟨fun h => hiS (h ▸ hk), hk⟩)
      have hIF : I ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩
      have hI'F : I' ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'⟩
      have hJF : J ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩
      have hJ'F : J' ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ'⟩
      have hαI : ∀ K ∈ F, i ∈ K → (∑ k ∈ Finset.erase I i, (u k : ℕ))
          ≤ (∑ k ∈ Finset.erase K i, (u k : ℕ)) := by
        intro K hK hiK
        have h1 := hminI K hK
        rw [split u I hiI, split u K hiK] at h1
        omega
      have hαI' : ∀ K ∈ F, i ∈ K → (∑ k ∈ Finset.erase I' i, (u' k : ℕ))
          ≤ (∑ k ∈ Finset.erase K i, (u' k : ℕ)) := by
        intro K hK hiK
        have h1 := hminI' K hK
        rw [split u' I' hiI', split u' K hiK] at h1
        omega
      have hoffEI : (∑ k ∈ Finset.erase I i, (u k : ℕ)) = (∑ k ∈ Finset.erase I i, (u' k : ℕ)) :=
        Finset.sum_congr rfl fun k hk =>
          congrArg (fun x : Fin N₀ => (x : ℕ)) (hoff k (Finset.mem_erase.mp hk).1)
      have hoffEI' : (∑ k ∈ Finset.erase I' i, (u k : ℕ))
          = (∑ k ∈ Finset.erase I' i, (u' k : ℕ)) :=
        Finset.sum_congr rfl fun k hk =>
          congrArg (fun x : Fin N₀ => (x : ℕ)) (hoff k (Finset.mem_erase.mp hk).1)
      have hoffEJ : (∑ k ∈ J, (u k : ℕ)) = (∑ k ∈ J, (u' k : ℕ)) :=
        Finset.sum_congr rfl fun k hk =>
          congrArg (fun x : Fin N₀ => (x : ℕ)) (hoff k (fun h => hiJ (h ▸ hk)))
      have hoffEJ' : (∑ k ∈ J', (u k : ℕ)) = (∑ k ∈ J', (u' k : ℕ)) :=
        Finset.sum_congr rfl fun k hk =>
          congrArg (fun x : Fin N₀ => (x : ℕ)) (hoff k (fun h => hiJ' (h ▸ hk)))
      have hαeq : (∑ k ∈ Finset.erase I i, (u k : ℕ))
          = (∑ k ∈ Finset.erase I' i, (u k : ℕ)) := by
        have h1 : (∑ k ∈ Finset.erase I i, (u k : ℕ))
            ≤ (∑ k ∈ Finset.erase I' i, (u k : ℕ)) := hαI I' hI'F hiI'
        have h2 : (∑ k ∈ Finset.erase I' i, (u' k : ℕ))
            ≤ (∑ k ∈ Finset.erase I i, (u' k : ℕ)) := hαI' I hIF hiI
        rw [← hoffEI', ← hoffEI] at h2
        linarith
      have hβeq : (∑ k ∈ J, (u k : ℕ)) = (∑ k ∈ J', (u k : ℕ)) := by
        have h1 : (∑ k ∈ J, (u k : ℕ)) ≤ (∑ k ∈ J', (u k : ℕ)) := by
          rw [← heqIJ]; exact hminI J' hJ'F
        have h2 : (∑ k ∈ J', (u' k : ℕ)) ≤ (∑ k ∈ J, (u' k : ℕ)) := by
          calc (∑ k ∈ J', (u' k : ℕ)) = (∑ k ∈ I', (u' k : ℕ)) := heqIJ'.symm
            _ ≤ (∑ k ∈ J, (u' k : ℕ)) := hminI' J hJF
        rw [← hoffEJ', ← hoffEJ] at h2
        linarith
      have e1 : ((u i : ℕ)) + (∑ k ∈ Finset.erase I i, (u k : ℕ)) = (∑ k ∈ J, (u k : ℕ)) := by
        rw [← split u I hiI]; exact heqIJ
      have e2 : ((u' i : ℕ)) + (∑ k ∈ Finset.erase I' i, (u' k : ℕ)) = (∑ k ∈ J', (u' k : ℕ)) := by
        rw [← split u' I' hiI']; exact heqIJ'
      have hfin : (u i : ℕ) = (u' i : ℕ) := by
        have c1 := e1
        rw [hαeq, hβeq] at c1
        have c2 := e2
        rw [← hoffEI', ← hoffEJ'] at c2
        omega
      funext k
      by_cases hk : k = i
      · rw [hk]; exact Fin.ext hfin
      · exact hoff k hk
    -- hence #(Cset i) ≤ #(functions vanishing at i)
    have hWC : ∀ i : Fin n, (Cset i).card ≤ (W i).card := by
      intro i
      have hinj : Set.InjOn (fun u : Fin n → Fin N₀ => Function.update u i (0 : Fin N₀))
          (Cset i) := by
        intro u hu u' hu' huu'
        have hoff : ∀ k, k ≠ i → u k = u' k := by
          intro k hk
          have h1 := congrFun huu' k
          simp only [Function.update_of_ne hk] at h1
          exact h1
        exact hslice i u u' hu hu' hoff
      have hsub : (Cset i).image (fun u : Fin n → Fin N₀ => Function.update u i (0 : Fin N₀))
          ⊆ W i := by
        simp only [hWdef, Finset.image_subset_iff]
        intro u _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.update_self i (0 : Fin N₀) u⟩
      calc (Cset i).card
          = ((Cset i).image (fun u : Fin n → Fin N₀ => Function.update u i (0 : Fin N₀))).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (W i).card := Finset.card_le_card hsub
    -- #(W i) · N₀ ≤ N₀^n : (w, v) ↦ update w i v is injective on vanishing-i pairs
    have hWbound : ∀ i : Fin n, (W i).card * N₀ ≤ N₀ ^ n := by
      intro i
      set img : (Fin n → Fin N₀) × Fin N₀ → (Fin n → Fin N₀) :=
        fun x => Function.update x.1 i x.2 with himgdef
      have hinj : ∀ p ∈ (W i ×ˢ (Finset.univ : Finset (Fin N₀))),
          ∀ q ∈ (W i ×ˢ (Finset.univ : Finset (Fin N₀))), img p = img q → p = q := by
        intro p hp q hq hfeq
        rw [Finset.mem_product] at hp hq
        have hvv : p.2 = q.2 := by
          have h1 := congrFun hfeq i
          simp only [himgdef, Function.update_self] at h1
          exact h1
        have hww : p.1 = q.1 := by
          funext k
          by_cases hk : k = i
          · rw [hk, show p.1 i = 0 from (Finset.mem_filter.mp hp.1).2,
                show q.1 i = 0 from (Finset.mem_filter.mp hq.1).2]
          · have h1 := congrFun hfeq k
            simp only [himgdef, Function.update_of_ne hk] at h1
            exact h1
        exact Prod.ext hww hvv
      have hstep : ((W i ×ˢ (Finset.univ : Finset (Fin N₀))).image img).card
          = (W i ×ˢ (Finset.univ : Finset (Fin N₀))).card :=
        Finset.card_image_of_injOn fun p hp q hq h => hinj p hp q hq h
      have h1 : ((W i ×ˢ (Finset.univ : Finset (Fin N₀))).image img).card
          ≤ (Finset.univ : Finset (Fin n → Fin N₀)).card :=
        Finset.card_le_card fun x _ => Finset.mem_univ x
      rw [hstep, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        Finset.card_univ, huniv] at h1
      exact h1
    -- union bound and arithmetic
    have hS1 : (Finset.univ.filter (fun u : Fin n → Fin N₀ => ¬ G u)).card
        ≤ ∑ i : Fin n, (Cset i).card := by
      have hsub2 : Finset.univ.filter (fun u : Fin n → Fin N₀ => ¬ G u)
          ⊆ Finset.univ.biUnion Cset := by
        intro u hu
        rw [Finset.mem_filter] at hu
        rcases hext u hu.2 with ⟨i, hi⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
      calc (Finset.univ.filter (fun u : Fin n → Fin N₀ => ¬ G u)).card
            ≤ (Finset.univ.biUnion Cset).card := Finset.card_le_card hsub2
        _ ≤ ∑ i : Fin n, (Cset i).card := Finset.card_biUnion_le
    have hS2 : N₀ * (∑ i : Fin n, (Cset i).card) ≤ n * N₀ ^ n := by
      calc N₀ * (∑ i : Fin n, (Cset i).card)
          = (∑ i : Fin n, (Cset i).card) * N₀ := mul_comm _ _
        _ = ∑ i : Fin n, (Cset i).card * N₀ := Finset.sum_mul _ _ _
        _ ≤ ∑ i : Fin n, N₀ ^ n := Finset.sum_le_sum fun i _ =>
              le_trans (Nat.mul_le_mul_right _ (hWC i)) (hWbound i)
        _ = (Finset.univ : Finset (Fin n)).card * N₀ ^ n := by
              rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
        _ = n * N₀ ^ n := by rw [Finset.card_univ, Fintype.card_fin]
    have hpart : (Finset.univ.filter G).card
        + (Finset.univ.filter (fun u : Fin n → Fin N₀ => ¬ G u)).card
          = Fintype.card (Fin n → Fin N₀) := Finset.card_filter_add_card_filter_not G
    have h1 : (N₀ ^ n : ℕ) ≤ (Finset.univ.filter G).card + (∑ i : Fin n, (Cset i).card) := by
      have h2 := hpart
      rw [huniv] at h2
      omega
    have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    have hN₀q : (0 : ℚ) < (N₀ : ℚ) := by exact_mod_cast hN₀pos
    have h12n : (12 : ℚ) * (n : ℚ) ≤ (N₀ : ℚ) := by exact_mod_cast hN₀
    have hS2q : (N₀ : ℚ) * (((∑ i : Fin n, (Cset i).card : ℕ) : ℚ))
        ≤ (n : ℚ) * ((N₀ ^ n : ℕ) : ℚ) := by exact_mod_cast hS2
    have keyS : (12 : ℚ) * (((∑ i : Fin n, (Cset i).card : ℕ) : ℚ)) ≤ ((N₀ ^ n : ℕ) : ℚ) := by
      have s1 : (n : ℚ) * ((12 : ℚ) * (((∑ i : Fin n, (Cset i).card : ℕ) : ℚ)))
          ≤ (N₀ : ℚ) * (((∑ i : Fin n, (Cset i).card : ℕ) : ℚ)) := by
        rw [← mul_assoc, mul_comm (n : ℚ) (12 : ℚ)]
        exact mul_le_mul_of_nonneg_right h12n (Nat.cast_nonneg _)
      have s2 : (n : ℚ) * ((12 : ℚ) * (((∑ i : Fin n, (Cset i).card : ℕ) : ℚ)))
          ≤ (n : ℚ) * ((N₀ ^ n : ℕ) : ℚ) := by linarith [s1, hS2q]
      exact le_of_mul_le_mul_left s2 hnq
    have hfinal : (11 : ℚ) * ((N₀ ^ n : ℕ) : ℚ)
        ≤ (12 : ℚ) * ((Finset.univ.filter G).card : ℚ) := by
      have e1 : ((N₀ ^ n : ℕ) : ℚ) ≤ ((Finset.univ.filter G).card : ℚ)
          + (((∑ i : Fin n, (Cset i).card : ℕ) : ℚ)) := by exact_mod_cast h1
      linarith [e1, keyS]
    have hDq : (0 : ℚ) < ((N₀ ^ n : ℕ) : ℚ) := pow_pos hN₀q n
    rw [huniv, div_le_div_iff₀ (by norm_num : (0 : ℚ) < 12) hDq]
    linarith [hfinal]

end SubsetSumL25
