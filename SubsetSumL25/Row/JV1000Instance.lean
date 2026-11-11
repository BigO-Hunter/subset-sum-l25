/-
`SubsetSumL25.Row.JV1000Instance` — Voitle's row (`jv1000/subset-sum`, 0.4875755) as
**instance data on the family frame**: the eight parameters, the 32 filter
coefficients, the ported slack absorb at the family's tightest gap, the 25 rational
checks, the amplitude certificate, and the residue stated as nine named goals.

Primary source: `jv1000/subset-sum` @ 6026da70f13d677b630cb1afd8fb10ee7a7f6010,
`exponent-2026/paper/rev8/paper_2026-11-06_rev8g.tex` §8 (the frozen point, l.386–407;
the J = 1 observation, l.382; the admissibility paragraph, l.410) and
`exponent-2026/lab_notebook/candidate_base.json` (the exact decimals and the 64 stored
coefficients).  Cross-checked against the merged audit pack
`/Volumes/Substrate-1/bigo/audit-jv1000/` (verifier PR #185), whose
`independent_decimal_check.py` recomputes all 34 checks in stdlib `decimal` at prec 60
and whose `repro_run1.json` records `all_pass: true`.

Why this file exists.  ASSEMBLY.md (`/Volumes/Substrate-1/bigo/jv1000-lane`) concluded
that the row is **Base's construction unchanged** with three deltas: one filter instead
of 43, her own parameter point, and the `J = 1` collapse of Theorem B's certificates.
Of the 34 numeric checks, the ones that are *pure rational arithmetic* need no new
mathematics — they are this file.  The lean-and-moment group is named, not stubbed:
`JV1000Residue` below carries exactly nine goals.

Division of labour, stated plainly:

* **Here: instance data + the row's bound arithmetic.**  Constants (§1), the gap
  absorb at `α − T = 9.64·10⁻⁸` — 100× tighter than `ss/kapila 0.4877`'s (§2), **25 of
  the 34 checks** (`repro_run1.json`), the amplitude certificate (§4), and the `J = 1`
  collapse shape (§7).
* **Not here: the seven entropy goals.**  C1–C5, C5L and A5 need rational `log₂`
  enclosures tight to ≪ 10⁻⁶; they are stated in `JV1000Residue` (§7).
* **The two moment goals have moved — and the shapes that were here are refuted.**
  `M₁`/`M₂` stated against the *raw* log-densities `r`, `s` are **false**: measured
  `log₂ = 9.1347 / 8.5400` against `ρ_c = 0.5162696` (`Row.JV1000Moments` §2 proves
  both refutations and §3 states the corrected obligations against the
  strip-corrected `u`, `v` the certifier actually integrates).
* **Nothing here is a claim about `Race.bound`.**  `SolvedInTime (975151/2000000)`
  additionally needs the shared `Routines`/`D7`/`CorrectAt` frame (ASSEMBLY §6 class B),
  which is the family lane's work, not this file's.

Measured findings, reported rather than smoothed over:

1. **`amp16` is the wrong weight for 3.21.**  `Proofs/JV1000.lean`'s `amp16` is
   `Σ_j (|a_j| + |b_j|)` (a valid but *loose* sup bound).  At the certified point it
   evaluates to `363121121/100000000 = 3.63121121` (density `r`) and
   `359861571/100000000 = 3.59861571` (density `s`) — both **above** 3.21, so
   `v1_cert_amp`'s hypothesis `amp16 a b ≤ 3.21` is *not satisfiable here*.  The paper's
   «summing harmonic amplitudes» is the modulus weight `Σ_j √(a_j² + b_j²)`, which is
   `3.1952756…` / `3.2026302…` — **below** 3.21.  §4 therefore certifies the modulus
   form (a strengthening of the interface V1 exposes), and the `amp16` value is recorded
   as `jv_amp16_value` so the mismatch is checkable rather than folklore.
2. **`ℍ` and `log 3` checks with big margins are provable with coarse rational bounds.**
   S3 (margin 0.854) and S5 (margin 0.931) need only `1/log 2 ≤ 3/2`,
   `log₂(1/a) ≤ 7`, `log₂(1/(2a)) ≤ 6` — all rational.  §6 proves them.  C1–C5/C5L/A5
   have margins ~1.3·10⁻⁶ and do *not* fall to coarse bounds; they are residue.
3. **`⌈8K/slack⌉ + 1 ≈ 8.3·10⁸` is one of two thresholds.**  `jv_poly_absorb` proves the
   existential; the constant leg's dominance at `K = 10` is the explicit
   `jv_poly_threshold_ten` (`80 ≤ slack · 8.3·10⁸`).  The *eventual-polynomial* leg
   (`n^{A} ≤ 2^{(slack/4)n}`) has a larger, only-existential threshold — it is the
   `Real.isLittleO_log_id_atTop` bound, not an explicit `N`.  Stated, not hidden.
-/
import Mathlib
import SubsetSumL25.Row.KapilaAlgo
import SubsetSumL25.Row.KapilaAbsorb
import SubsetSumL25.Proofs.JV1000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §1 — the parameter point (exact rationals, verbatim from `candidate_base.json`)

Every constant is carried as a `ℚ` so that the row's checks are integer-arithmetic
`norm_num` goals; the `ℝ` shadows exist only where the analysis (the absorb lemmas, the
trigonometric densities) needs them.  The mapping to `KapilaAlgo.lean:50–71`'s
`tau0`/`etaP`/… is one-to-one; the `jv` prefix keeps both rows in one namespace without
shadowing the shipped constants. -/

/-- τ₀ = `0.4875752036` — the enumeration-budget exponent (Base: 0.48769). -/
def jvTau0Q : ℚ := 4875752036 / 10000000000

/-- η = `0.5162721413` — modulus size in bits (Base: 0.51613 — *larger* here). -/
def jvEtaQ : ℚ := 5162721413 / 10000000000

/-- μ = `0.4752421539` — the shared block as a fraction of `n` (Base: 0.473). -/
def jvMuQ : ℚ := 4752421539 / 10000000000

/-- a = `0.0082379228` — mask density (Base: 0.0082). -/
def jvAQ : ℚ := 82379228 / 10000000000

/-- γ = `0.0605824120` — the small prime's size relative to the block (Base: 0.06035). -/
def jvGammaQ : ℚ := 605824120 / 10000000000

/-- l = `0.4836347962` — the left part as a fraction of `n` (Base: 0.48377). -/
def jvLQ : ℚ := 4836347962 / 10000000000

/-- κ = `1.03465831` — the power applied to the density in the filter's exponent. -/
def jvKappaQ : ℚ := 103465831 / 100000000

/-- p = `8.45902160` — the multiplier vector's first entry (region ρ₀). -/
def jvPQ : ℚ := 845902160 / 100000000

/-- q_m = `8.27015425` — the multiplier for regions ρ₁–ρ₉. -/
def jvQmQ : ℚ := 827015425 / 100000000

/-- ε = `10⁻⁸` — pattern accuracy.  `T = τ₀ + 20ε` is the theorem's threshold. -/
def jvEpsQ : ℚ := 1 / 100000000

/-- ζ = `10⁻⁸` — the Theorem A / Lemma A5 slack. -/
def jvZetaQ : ℚ := 1 / 100000000

/-- The input guard `10⁸` (Base's `guard`; free in Base, only raises the cutoff `n_*`). -/
def jvGuardQ : ℚ := 100000000

/-- ρ_f = η − `1.5·10⁻⁶`. -/
def jvRhoFQ : ℚ := jvEtaQ - 3 / 2000000

/-- ρ_c = ρ_f − `10⁻⁶` — the checksum capacity the moments must fit under. -/
def jvRhoCQ : ℚ := jvRhoFQ - 1 / 1000000

/-- **The row's bound** α = `975151/2000000` = 0.4875755 (reduced: odd numerator,
denominator `2⁷·5⁶` — the filed literal and the proved literal are byte-identical). -/
def jvAlphaRowQ : ℚ := 975151 / 2000000

/-- **The slack §1 spends**: `α − (τ₀ + 20ε) = 241/2500000000 = 9.64·10⁻⁸`.
This is the family's *tightest* gap — `ss/kapila 0.4877` spends `9.8·10⁻⁶`, 100× more. -/
def jvSlackQ : ℚ := 241 / 2500000000

/-- `T = τ₀ + 20ε = 0.4875754036` — the theorem's threshold, at her exact decimals. -/
def jvTQ : ℚ := 4875754036 / 10000000000

/-- `r = 1 − μ − l` — the right part. -/
def jvRQ : ℚ := 1 - jvMuQ - jvLQ

/-- `Δ = η − τ₀` — the checksum capacity, and the counting floor's parameter. -/
def jvDeltaQ : ℚ := jvEtaQ - jvTau0Q

/-- `Γ = 2τ₀ − η` — the region-partition's gap. -/
def jvBigGammaQ : ℚ := 2 * jvTau0Q - jvEtaQ

/-- `a_Γ = Δ/Γ` — the row error's parameter (Base's Lemma B2 wants `a_Γ ≤ 3/4`). -/
def jvAGammaQ : ℚ := jvDeltaQ / jvBigGammaQ

/-- The **certified lower bound** for ε₀ = the min of the C1–C8 margins, taken from the
audit's tightest value `1.3156702338…·10⁻⁶`.  The Lemma A7 checks are proved against
this bound (§5, `jv_a71_*`), i.e. they are *stronger* than the paper's once the entropy
group certifies `ε₀ ≥ 10⁻⁶`.  The `ε₀ ≥ 10⁻⁶` step is one of the residue's consequences
(C1–C5 are the binding margins) and is recorded as `JV1000Residue.eps0_lower_bound`. -/
def jvEps0LBQ : ℚ := 1 / 1000000

/-- τ₀ as a real. -/
noncomputable def jvTau0 : ℝ := (jvTau0Q : ℝ)

/-- ε as a real. -/
noncomputable def jvEps : ℝ := (jvEpsQ : ℝ)

/-- The slack as a real. -/
noncomputable def jvSlack : ℝ := (jvSlackQ : ℝ)

/-- The row's bound as a real. -/
noncomputable def jvAlphaRow : ℝ := (jvAlphaRowQ : ℝ)

/-! ### §2 — the gap absorb at her constants

All three lemmas are §1 of Base («the gap absorbs every factor `2^{O(n^{0.7})}
poly(n+n^c)`») ported to `α = 975151/2000000`.  The mechanism is unchanged;
the *margin* is not: `slack = 9.64·10⁻⁸`, so the existential thresholds are ~100× larger.
`poly_absorb` needs only `slack > 0` — that is the whole reason the row's arithmetic
survives a gap this thin, and it is why proving `jv_slack_pos` is load-bearing rather
than cosmetic.  The two generic legs (`eventually_rpow_le_mul`,
`eventually_pow_le_two_rpow`) are constant-free and are imported from `KapilaAbsorb`,
not duplicated. -/

theorem jv_slack_pos : (0 : ℝ) < jvSlack := by
  rw [jvSlack, jvSlackQ]
  norm_num

/-- `τ₀ + 20ε = T`, at her decimals. -/
theorem jv_T_eq : jvTau0 + 20 * jvEps = (jvTQ : ℝ) := by
  rw [jvTau0, jvEps, jvTau0Q, jvEpsQ, jvTQ]
  push_cast
  norm_num

/-- **The row's arithmetic identity**: `τ₀ + 20ε + slack = α` at `α = 975151/2000000`.
This is the single equation the whole row's exponent accounting reduces to. -/
theorem jv_tau0_eps_slack : jvTau0 + 20 * jvEps + jvSlack = jvAlphaRow := by
  rw [jvTau0, jvEps, jvSlack, jvAlphaRow, jvTau0Q, jvEpsQ, jvSlackQ, jvAlphaRowQ]
  push_cast
  norm_num

/-- **The sub-exponential leg**: `2^{2n^{0.7}} ≤ 2^{(slack/2)n}` eventually. -/
theorem jv_subexp_absorb :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ)) ≤ (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_rpow_le_mul (r := (0.7 : ℝ)) (by norm_num) (by norm_num)
    (c := jvSlack / 8) (by have := jv_slack_pos; linarith)
  refine ⟨max N₁ 1, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast (by omega : 0 < n)
  have h1 : (n : ℝ) ^ (0.7 : ℝ) ≤ (jvSlack / 8) * (n : ℝ) := hN₁ n hn1
  have hexp : 2 * (n : ℝ) ^ (0.7 : ℝ) ≤ (jvSlack / 2) * (n : ℝ) := by
    have hs := jv_slack_pos
    nlinarith
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hexp

/-- **The polynomial leg**: `(n + n^c + 2)^K ≤ 2^{(slack/2)n}` eventually.  The
threshold is `max N₁ (⌈8K/slack⌉+1)`; at `K = 10` the second term is `8.3·10⁸`
(`jv_poly_threshold_ten`).  `N₁` — the `n^A ≤ 2^{(slack/4)n}` leg — is only existential. -/
theorem jv_poly_absorb (c K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K ≤ (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos K with hK | hKpos
  · subst hK
    refine ⟨2, ?_⟩
    intro n hn
    have hone : ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ 0 = 1 := by simp
    rw [hone]
    exact Real.one_le_rpow (by norm_num) (by have := jv_slack_pos; positivity)
  · set cc : ℕ := max c 1 with hcc
    have hcc1 : 1 ≤ cc := le_max_right c 1
    have hccc : c ≤ cc := le_max_left c 1
    set A : ℝ := (cc : ℝ) * (K : ℝ) with hA_def
    have hApos : 0 < A := by
      have h1 : (0 : ℝ) < (cc : ℝ) := by exact_mod_cast (by omega : 0 < cc)
      have h2 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
      rw [hA_def]; positivity
    obtain ⟨N₁, hN₁⟩ := eventually_pow_le_two_rpow (A := A) (b := jvSlack / 4) hApos
      (by have := jv_slack_pos; linarith)
    refine ⟨max (max N₁ 2) (Nat.ceil (8 * (K : ℝ) / jvSlack) + 1), ?_⟩
    intro n hn
    have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hgt : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
    have hle_cc : (n : ℝ) ≤ (n : ℝ) ^ ((cc : ℕ) : ℝ) := by
      have h1 : (n : ℝ) ^ ((1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ((cc : ℕ) : ℝ) :=
        (Real.rpow_le_rpow_left_iff hgt).2 (by exact_mod_cast hcc1)
      simpa using h1
    have hle_c : (n : ℝ) ^ ((c : ℕ) : ℝ) ≤ (n : ℝ) ^ ((cc : ℕ) : ℝ) :=
      (Real.rpow_le_rpow_left_iff hgt).2 (by exact_mod_cast hccc)
    have hsum : (n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2 ≤ 4 * (n : ℝ) ^ ((cc : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ 2 * (n : ℝ) ^ ((cc : ℕ) : ℝ) := by nlinarith [hle_cc, hnpos]
      nlinarith [hle_cc, hle_c, h2]
    have hsum0 : (0 : ℝ) ≤ (n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2 := by positivity
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.zero_le K
    have hrew : ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
        = ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ ((K : ℕ) : ℝ) :=
      (Real.rpow_natCast _ K).symm
    have hstep1 : ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ ((K : ℕ) : ℝ)
        ≤ (4 * (n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ) :=
      Real.rpow_le_rpow hsum0 hsum hK0
    have hstep2 : (4 * (n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ)
        = (2 : ℝ) ^ (2 * (K : ℝ)) * (n : ℝ) ^ A := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      have h42 : (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; norm_num
      have h4 : (4 : ℝ) ^ ((K : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (K : ℝ)) := by
        rw [h42, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hp : ((n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ) = (n : ℝ) ^ A := by
        rw [← Real.rpow_mul hn0, hA_def]
      rw [h4, hp]
    have hfour : (2 : ℝ) ^ (2 * (K : ℝ)) ≤ (2 : ℝ) ^ ((jvSlack / 4) * (n : ℝ)) := by
      refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 ?_
      have hs := jv_slack_pos
      have hK' : (8 * (K : ℝ)) / jvSlack ≤ (n : ℝ) := by
        have h8 : (8 * (K : ℝ)) / jvSlack ≤ (Nat.ceil (8 * (K : ℝ) / jvSlack) : ℝ) := Nat.le_ceil _
        have h9 : Nat.ceil (8 * (K : ℝ) / jvSlack) + 1 ≤ n := le_trans (le_max_right _ _) hn
        have h10 : (Nat.ceil (8 * (K : ℝ) / jvSlack) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (by omega : Nat.ceil (8 * (K : ℝ) / jvSlack) ≤ n)
        linarith
      have hk : 8 * (K : ℝ) ≤ jvSlack * (n : ℝ) := by
        rw [div_le_iff₀ hs] at hK'
        linarith
      nlinarith
    have hpoly : (n : ℝ) ^ A ≤ (2 : ℝ) ^ ((jvSlack / 4) * (n : ℝ)) := hN₁ n hN1
    have hmul : (2 : ℝ) ^ (2 * (K : ℝ)) * (n : ℝ) ^ A
        ≤ (2 : ℝ) ^ ((jvSlack / 4) * (n : ℝ)) * (2 : ℝ) ^ ((jvSlack / 4) * (n : ℝ)) := by
      apply mul_le_mul hfour hpoly (by positivity) (by positivity)
    have hjoin : (2 : ℝ) ^ ((jvSlack / 4) * (n : ℝ)) * (2 : ℝ) ^ ((jvSlack / 4) * (n : ℝ))
        = (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    calc ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
        = ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ ((K : ℕ) : ℝ) := hrew
      _ ≤ (4 * (n : ℝ) ^ ((cc : ℕ) : ℝ)) ^ ((K : ℕ) : ℝ) := hstep1
      _ = (2 : ℝ) ^ (2 * (K : ℝ)) * (n : ℝ) ^ A := hstep2
      _ ≤ (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ)) := le_trans hmul (le_of_eq hjoin)

/-- The constant leg of `jv_poly_absorb`'s threshold, explicitly: at `K = 10` the
external constant `2^{2K} = 2²⁰` is dominated by `2^{(slack/4)n}` from `n = 8.3·10⁸`
onwards, since `20 ≤ (slack/4)·8.3·10⁸ = 20.003`.  This is the `⌈8K/slack⌉ + 1`
threshold ASSEMBLY §9 flags as «must be proved, not assumed» — proved at `K = 10`. -/
theorem jv_poly_threshold_ten : 20 ≤ (jvSlack / 4) * (830000000 : ℝ) := by
  rw [jvSlack, jvSlackQ]
  push_cast
  norm_num

/-- **§1's gap, in one lemma, at her constants**: the runtime envelope's sub-exponential
and polynomial factors are absorbed by the `9.64·10⁻⁸` slack between `T` and
`α = 975151/2000000`.  This is the theorem the row's `WithinEnvelope` instantiation
consumes; it is where the 100×-tighter gap is actually spent. -/
theorem jv_runtime_absorb (c K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ))
        * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ))
        * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
      ≤ (2 : ℝ) ^ (jvAlphaRow * (n : ℝ)) := by
  obtain ⟨N₁, hN₁⟩ := jv_subexp_absorb
  obtain ⟨N₂, hN₂⟩ := jv_poly_absorb c K
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro n hn
  have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsub := hN₁ n hN1
  have hpol := hN₂ n hN2
  have hbase : (0 : ℝ) < (2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmono1 : (2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ))
        * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ))
      ≤ (2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ)) * (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hsub (le_of_lt hbase)
  have hstep : (2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ)) * (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ))
      = (2 : ℝ) ^ ((jvTau0 + 20 * jvEps + jvSlack / 2) * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc (2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ))
        * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ))
        * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K
      = ((2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ))
          * (2 : ℝ) ^ (2 * (n : ℝ) ^ (0.7 : ℝ)))
        * ((n : ℝ) + (n : ℝ) ^ ((c : ℕ) : ℝ) + 2) ^ K := by ring
    _ ≤ ((2 : ℝ) ^ ((jvTau0 + 20 * jvEps) * (n : ℝ)) * (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ)))
        * (2 : ℝ) ^ ((jvSlack / 2) * (n : ℝ)) := by
      apply mul_le_mul hmono1 hpol (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((jvTau0 + 20 * jvEps + jvSlack) * (n : ℝ)) := by
      rw [hstep, ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ = (2 : ℝ) ^ (jvAlphaRow * (n : ℝ)) := by
      rw [← jv_tau0_eps_slack]

/-! ### §3 — the 32 stored coefficients, and the two densities

`candidate_base.json` stores `rc` and `sc`, 32 rationals each: `rc[0..15]` are the
cosine and `rc[16..31]` the sine coefficients of the density `r` (the `r` log-density is
`r(x) = Σ_{j=1}^{16} (rc[j−1] cos jx + rc[16+j−1] sin jx)`); `sc` is the same for the
density `s`.  That is 16 cosine + 16 sine *per density*, 64 stored numbers in all —
jv1000's one filter, replacing Base's 43 cosine-only ones.  The transcription is
verbatim from the JSON (the cross-check is `independent_decimal_check.py`'s
`trig`, which reads the same indices). -/

/-- The density `r`'s 32 stored coefficients: 16 cosine, then 16 sine. -/
def jvRc : List ℚ :=
  [-21919156 / 100000000, -57160580 / 100000000, 2024951 / 100000000,
   3552214 / 100000000, -29988253 / 100000000, -20387757 / 100000000,
   12066750 / 100000000, -4068323 / 100000000, -3536274 / 100000000,
   -662503 / 100000000, -401488 / 100000000, 734024 / 100000000,
   751173 / 100000000, -392649 / 100000000, 11920 / 100000000,
   117642 / 100000000, 91131919 / 100000000, 973572 / 100000000,
   47988091 / 100000000, -34819083 / 100000000, -7175384 / 100000000,
   4897708 / 100000000, 1245896 / 100000000, -11710680 / 100000000,
   -1505095 / 100000000, -2221718 / 100000000, 282094 / 100000000,
   166169 / 100000000, -656995 / 100000000, -332303 / 100000000,
   231101 / 100000000, -7656 / 100000000]

/-- The density `s`'s 32 stored coefficients: 16 cosine, then 16 sine. -/
def jvSc : List ℚ :=
  [-20782817 / 100000000, 61194965 / 100000000, 2603977 / 100000000,
   846337 / 100000000, -22018634 / 100000000, 21025833 / 100000000,
   20455466 / 100000000, 2047196 / 100000000, -4648472 / 100000000,
   -1884839 / 100000000, 2926117 / 100000000, 689286 / 100000000,
   -353414 / 100000000, -297744 / 100000000, -5725 / 100000000,
   128320 / 100000000, 96462148 / 100000000, 1416858 / 100000000,
   38660217 / 100000000, 31951898 / 100000000, -7671638 / 100000000,
   -950575 / 100000000, -2875410 / 100000000, 10160127 / 100000000,
   -1822490 / 100000000, -3524125 / 100000000, -1087451 / 100000000,
   271495 / 100000000, 602714 / 100000000, -342132 / 100000000,
   -147364 / 100000000, -5787 / 100000000]

/-- `r`'s `j`-th cosine coefficient (`j = 1..16`). -/
def jvRaQ (j : ℕ) : ℚ := jvRc.getD (j - 1) 0

/-- `r`'s `j`-th sine coefficient. -/
def jvRbQ (j : ℕ) : ℚ := jvRc.getD (16 + (j - 1)) 0

/-- `s`'s `j`-th cosine coefficient. -/
def jvSaQ (j : ℕ) : ℚ := jvSc.getD (j - 1) 0

/-- `s`'s `j`-th sine coefficient. -/
def jvSbQ (j : ℕ) : ℚ := jvSc.getD (16 + (j - 1)) 0

/-- `r`'s cosine coefficient, as a real (the form `trig16` takes). -/
noncomputable def jvRa (j : ℕ) : ℝ := (jvRaQ j : ℝ)

/-- `r`'s sine coefficient, as a real. -/
noncomputable def jvRb (j : ℕ) : ℝ := (jvRbQ j : ℝ)

/-- `s`'s cosine coefficient, as a real. -/
noncomputable def jvSa (j : ℕ) : ℝ := (jvSaQ j : ℝ)

/-- `s`'s sine coefficient, as a real. -/
noncomputable def jvSb (j : ℕ) : ℝ := (jvSbQ j : ℝ)

/-- The certified log-density `r` (rev8g §8: 16 cosine + 16 sine terms). -/
noncomputable def jvLogDensityR : ℝ → ℝ := trig16 jvRa jvRb

/-- The certified log-density `s`. -/
noncomputable def jvLogDensityS : ℝ → ℝ := trig16 jvSa jvSb

/-! ### §4 — the amplitude certificate (C8 of ASSEMBLY §6)

The paper's «summing harmonic amplitudes gives the safe bounds `|r(x)|, |s(x)| < 3.21`»
is the **modulus** weight `Σ_j √(a_j² + b_j²)` — the amplitude of the `j`-th harmonic.
`Proofs/JV1000.lean`'s `amp16` is the *looser* weight `Σ_j (|a_j| + |b_j|)`; at this
point it is `3.63121121` / `3.59861571`, above 3.21, so V1's `v1_cert_amp` hypothesis is
unsatisfiable here (recorded as `jv_amp16_value`).  What is certified below is the
modulus form — which is strictly stronger, and is also the shape V1's `rig_M` residue
wants (`Σ√(a²+b²)·cosh(jy)`).

The 32 rational upper bounds are 4-decimal ceilings of the true moduli, each verified by
`s² ≥ a² + b²` (a `norm_num` comparison), and their sums are `3.1961` and `3.2034` —
both under 3.21 with room. -/

/-- Rational upper bounds for `r`'s 16 harmonic moduli. -/
def jvRModQ : List ℚ :=
  [4687 / 5000, 5717 / 10000, 1201 / 2500, 7 / 20, 771 / 2500, 2097 / 10000,
   607 / 5000, 31 / 250, 77 / 2000, 29 / 1250, 1 / 200, 19 / 2500, 1 / 100,
   13 / 2500, 3 / 1250, 3 / 2500]

/-- Rational upper bounds for `s`'s 16 harmonic moduli. -/
def jvSModQ : List ℚ :=
  [2467 / 2500, 3061 / 5000, 31 / 80, 3197 / 10000, 583 / 2500, 421 / 2000,
   1033 / 5000, 1037 / 10000, 1 / 20, 1 / 25, 313 / 10000, 3 / 400, 7 / 1000,
   23 / 5000, 3 / 2000, 13 / 10000]

/-- The modulus weight: `Σ_{j=1}^{16} √(a_j² + b_j²)`, the true sup bound on `|r|`. -/
noncomputable def jvAmpMod (a b : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (1 : ℕ) 16, Real.sqrt (a j ^ 2 + b j ^ 2)

/-- **The individual harmonic bound**: `|a cos t + b sin t| ≤ √(a² + b²)`.  Proved by
the Cauchy–Schwarz square: `(a cos + b sin)² + (a sin − b cos)² = a² + b²`. -/
theorem jv_harmonic_le (a b t : ℝ) :
    |a * Real.cos t + b * Real.sin t| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hsq : (a * Real.cos t + b * Real.sin t) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have h := Real.sin_sq_add_cos_sq t
    nlinarith [sq_nonneg (a * Real.sin t - b * Real.cos t)]
  calc |a * Real.cos t + b * Real.sin t|
      = Real.sqrt ((a * Real.cos t + b * Real.sin t) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_le_sqrt hsq

/-- The per-term modulus bounds for `r`, from the stored 4-decimal ceilings. -/
theorem jv_r_mod_term (j : ℕ) (hj : j ∈ Finset.Icc (1 : ℕ) 16) :
    Real.sqrt (jvRa j ^ 2 + jvRb j ^ 2) ≤ ((jvRModQ.getD (j - 1) 0 : ℚ) : ℝ) := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj2 : j ≤ 16 := (Finset.mem_Icc.mp hj).2
  rw [Real.sqrt_le_iff]
  constructor
  · interval_cases j <;> norm_num [jvRModQ, List.getD]
  · interval_cases j <;>
      norm_num [jvRa, jvRb, jvRaQ, jvRbQ, jvRc, jvRModQ, List.getD]

/-- The per-term modulus bounds for `s`. -/
theorem jv_s_mod_term (j : ℕ) (hj : j ∈ Finset.Icc (1 : ℕ) 16) :
    Real.sqrt (jvSa j ^ 2 + jvSb j ^ 2) ≤ ((jvSModQ.getD (j - 1) 0 : ℚ) : ℝ) := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj2 : j ≤ 16 := (Finset.mem_Icc.mp hj).2
  rw [Real.sqrt_le_iff]
  constructor
  · interval_cases j <;> norm_num [jvSModQ, List.getD]
  · interval_cases j <;>
      norm_num [jvSa, jvSb, jvSaQ, jvSbQ, jvSc, jvSModQ, List.getD]

/-- The `r` modulus sum is under 3.21: `3.1961`. -/
theorem jv_r_mod_sum : (jvRModQ.foldr (· + ·) 0) ≤ 321 / 100 := by
  rw [jvRModQ]; norm_num

/-- The `s` modulus sum is under 3.21: `3.2034`. -/
theorem jv_s_mod_sum : (jvSModQ.foldr (· + ·) 0) ≤ 321 / 100 := by
  rw [jvSModQ]; norm_num

/-- **C8 (the amplitude certificate), density `r`**: `Σ_j √(a_j² + b_j²) ≤ 3.21`. -/
theorem jv_amp_mod_cert_r : jvAmpMod jvRa jvRb ≤ 3.21 := by
  have hterm : ∀ j ∈ Finset.Icc (1 : ℕ) 16,
      Real.sqrt (jvRa j ^ 2 + jvRb j ^ 2) ≤ ((jvRModQ.getD (j - 1) 0 : ℚ) : ℝ) :=
    jv_r_mod_term
  have hsum : (∑ j ∈ Finset.Icc (1 : ℕ) 16, ((jvRModQ.getD (j - 1) 0 : ℚ) : ℝ))
      = ((jvRModQ.foldr (· + ·) 0 : ℚ) : ℝ) := by
    rw [jvRModQ]
    norm_num [Finset.sum_Icc_succ_top, List.getD]
  calc jvAmpMod jvRa jvRb
      ≤ ∑ j ∈ Finset.Icc (1 : ℕ) 16, ((jvRModQ.getD (j - 1) 0 : ℚ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((jvRModQ.foldr (· + ·) 0 : ℚ) : ℝ) := hsum
    _ ≤ (321 / 100 : ℝ) := by
        have h := jv_r_mod_sum
        have h' : ((jvRModQ.foldr (· + ·) 0 : ℚ) : ℝ) ≤ ((321 / 100 : ℚ) : ℝ) := by
          exact_mod_cast h
        simpa using h'
    _ ≤ 3.21 := by norm_num

/-- **C8, density `s`**: `Σ_j √(a_j² + b_j²) ≤ 3.21`. -/
theorem jv_amp_mod_cert_s : jvAmpMod jvSa jvSb ≤ 3.21 := by
  have hterm : ∀ j ∈ Finset.Icc (1 : ℕ) 16,
      Real.sqrt (jvSa j ^ 2 + jvSb j ^ 2) ≤ ((jvSModQ.getD (j - 1) 0 : ℚ) : ℝ) :=
    jv_s_mod_term
  have hsum : (∑ j ∈ Finset.Icc (1 : ℕ) 16, ((jvSModQ.getD (j - 1) 0 : ℚ) : ℝ))
      = ((jvSModQ.foldr (· + ·) 0 : ℚ) : ℝ) := by
    rw [jvSModQ]
    norm_num [Finset.sum_Icc_succ_top, List.getD]
  calc jvAmpMod jvSa jvSb
      ≤ ∑ j ∈ Finset.Icc (1 : ℕ) 16, ((jvSModQ.getD (j - 1) 0 : ℚ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((jvSModQ.foldr (· + ·) 0 : ℚ) : ℝ) := hsum
    _ ≤ (321 / 100 : ℝ) := by
        have h := jv_s_mod_sum
        have h' : ((jvSModQ.foldr (· + ·) 0 : ℚ) : ℝ) ≤ ((321 / 100 : ℚ) : ℝ) := by
          exact_mod_cast h
        simpa using h'
    _ ≤ 3.21 := by norm_num

/-- **`|r| ≤ 3.21`** — the paper's displayed bound, from the modulus certificate. -/
theorem jv_abs_density_r (x : ℝ) : |jvLogDensityR x| ≤ 3.21 := by
  have hterm : ∀ j ∈ Finset.Icc (1 : ℕ) 16,
      |jvRa j * Real.cos ((j : ℝ) * x) + jvRb j * Real.sin ((j : ℝ) * x)|
        ≤ Real.sqrt (jvRa j ^ 2 + jvRb j ^ 2) :=
        fun j _ => jv_harmonic_le (jvRa j) (jvRb j) ((j : ℝ) * x)
  have : |jvLogDensityR x| ≤ jvAmpMod jvRa jvRb := by
    have h := Finset.abs_sum_le_sum_abs
      (fun j => jvRa j * Real.cos ((j : ℝ) * x) + jvRb j * Real.sin ((j : ℝ) * x))
      (Finset.Icc (1 : ℕ) 16)
    exact le_trans h (Finset.sum_le_sum hterm)
  exact le_trans this jv_amp_mod_cert_r

/-- **`|s| ≤ 3.21`**. -/
theorem jv_abs_density_s (x : ℝ) : |jvLogDensityS x| ≤ 3.21 := by
  have hterm : ∀ j ∈ Finset.Icc (1 : ℕ) 16,
      |jvSa j * Real.cos ((j : ℝ) * x) + jvSb j * Real.sin ((j : ℝ) * x)|
        ≤ Real.sqrt (jvSa j ^ 2 + jvSb j ^ 2) :=
        fun j _ => jv_harmonic_le (jvSa j) (jvSb j) ((j : ℝ) * x)
  have : |jvLogDensityS x| ≤ jvAmpMod jvSa jvSb := by
    have h := Finset.abs_sum_le_sum_abs
      (fun j => jvSa j * Real.cos ((j : ℝ) * x) + jvSb j * Real.sin ((j : ℝ) * x))
      (Finset.Icc (1 : ℕ) 16)
    exact le_trans h (Finset.sum_le_sum hterm)
  exact le_trans this jv_amp_mod_cert_s

/-- **The uniform-boundedness conclusion at the certified point** (OpenAI Lemma 3.2's
step, V1 item 3, with NO evenness hypothesis): the log-density's logarithm is bounded by
`3.21·log 2`, so `2^r` sits in `[2^{-3.21}, 2^{3.21}]`.  This is the jv-specific
replacement for `v1_log_bounded`, whose `amp16 ≤ 3.21` hypothesis does not hold here. -/
theorem jv_log_bounded (x : ℝ) :
    |Real.log ((2 : ℝ) ^ jvLogDensityR x)| ≤ 3.21 * Real.log 2 := by
  have hamp := jv_abs_density_r x
  rw [abs_le] at hamp
  have hlo : ((2 : ℝ) ^ (-(3.21 : ℝ))) ≤ (2 : ℝ) ^ jvLogDensityR x :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hamp.1
  have hhi : (2 : ℝ) ^ jvLogDensityR x ≤ ((2 : ℝ) ^ (3.21 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hamp.2
  refine le_trans (o4_log_abs_le (W := (2 : ℝ) ^ jvLogDensityR x)
    (m := (2 : ℝ) ^ (-(3.21 : ℝ))) (M := (2 : ℝ) ^ (3.21 : ℝ))
    (by positivity) hlo hhi) ?_
  have e1 : Real.log ((2 : ℝ) ^ (-(3.21 : ℝ))) = -((3.21 : ℝ) * Real.log 2) := by
    rw [Real.log_rpow (by norm_num) (-(3.21 : ℝ)), neg_mul]
  have e2 : Real.log ((2 : ℝ) ^ (3.21 : ℝ)) = (3.21 : ℝ) * Real.log 2 :=
    Real.log_rpow (by norm_num) (3.21 : ℝ)
  rw [e1, e2, abs_neg,
    abs_of_nonneg (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)] :
      (0 : ℝ) ≤ (3.21 : ℝ) * Real.log 2), max_self]

/-- The measured value of V1's `amp16` (the `Σ(|a| + |b|)` weight) at this point, for
density `r`: `3.63121121`.  This is **above** 3.21 — the interface mismatch reported in
the header.  Kept as a theorem so the mismatch is a checkable artefact. -/
theorem jv_amp16_value_r : amp16 jvRa jvRb = 363121121 / 100000000 := by
  rw [amp16]
  norm_num [jvRa, jvRb, jvRaQ, jvRbQ, jvRc, List.getD, Finset.sum_Icc_succ_top]

/-- V1's `amp16` at this point, density `s`: `3.59861571`. -/
theorem jv_amp16_value_s : amp16 jvSa jvSb = 359861571 / 100000000 := by
  rw [amp16]
  norm_num [jvSa, jvSb, jvSaQ, jvSbQ, jvSc, List.getD, Finset.sum_Icc_succ_top]

/-- The mismatch, named: `amp16` exceeds 3.21 for both densities, so `v1_cert_amp`
cannot be discharged at the certified point. -/
theorem jv_amp16_exceeds : 3.21 < amp16 jvRa jvRb ∧ 3.21 < amp16 jvSa jvSb := by
  rw [jv_amp16_value_r, jv_amp16_value_s]
  norm_num

/-! ### §5 — the rational checks (22 of the 34, plus C8)

````
C6  r > 0 · r < τ₀ · l < τ₀      C7  μ(1−2a) < l
C8  (μ/2)·log 3 < η              S1  4a < 1 · S2  μ(1−2a) < 1/2
Δ > 0 · Γ > 0 · B1 ρ_f − ρ_c > 0 · B3 η − ρ_f > (18 + 6max(p,q))ε
A7.1 ×3 (l, r, μ(1−2a) < τ₀ − ε₀) · A7.3 · A7.4
prime draw η/2 < τ₀ · B2 a_Γ ≤ 3/4 · ρ₀ p ≥ 1 · ρ₁..ρ₉ q ≥ 1 · Σz ≤ 418.36
ε₀ > ζ + 1/guard · μ < τ₀ − ε₀   (at the certified lower bound ε₀ ≥ 10⁻⁶)
````

Everything here is `norm_num` on exact rationals — no analysis.  The Lemma A7 group and
the two ε₀ checks are stated at `jvEps0LBQ = 10⁻⁶` (the certified *lower* bound of the
C1–C8 margin minimum), which makes them strictly stronger than the paper's. -/

theorem jv_check_C6_r_pos : 0 < jvRQ := by
  rw [jvRQ, jvMuQ, jvLQ]; norm_num

theorem jv_check_C6_r_lt_tau0 : jvRQ < jvTau0Q := by
  rw [jvRQ, jvMuQ, jvLQ, jvTau0Q]; norm_num

theorem jv_check_C6_l_lt_tau0 : jvLQ < jvTau0Q := by
  rw [jvLQ, jvTau0Q]; norm_num

theorem jv_check_C7 : jvMuQ * (1 - 2 * jvAQ) < jvLQ := by
  rw [jvMuQ, jvAQ, jvLQ]; norm_num

/-- `log₂ 3 < 8/5` — from `3⁵ = 243 < 256 = 2⁸`.  This is the only logarithm the
rational group needs, and it is an integer comparison. -/
theorem jv_log2_three_lt : Real.log 3 / Real.log 2 < 8 / 5 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h5 : Real.log ((3 : ℝ) ^ 5) = 5 * Real.log 3 := Real.log_pow ..
  have h8 : Real.log ((2 : ℝ) ^ 8) = 8 * Real.log 2 := Real.log_pow ..
  have h : 5 * Real.log 3 < 8 * Real.log 2 := by
    have hlt : Real.log ((3 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [h5, h8] at hlt
    exact hlt
  rw [div_lt_iff₀ hlog2]
  linarith

/-- **C8** — `(μ/2)·log₂3 < η`, the paper's own form (not just the rational bound). -/
theorem jv_check_C8 : jvMuQ / 2 * (Real.log 3 / Real.log 2) < (jvEtaQ : ℝ) := by
  have hη : ((jvEtaQ : ℚ) : ℝ) = (5162721413 / 10000000000 : ℝ) := by norm_num [jvEtaQ]
  have hμ : ((jvMuQ : ℚ) : ℝ) = (4752421539 / 10000000000 : ℝ) := by norm_num [jvMuQ]
  rw [hη, hμ]
  have h3 := jv_log2_three_lt
  have hμpos : (0 : ℝ) < 4752421539 / 10000000000 := by norm_num
  nlinarith [h3, hμpos]

/-- C8's rational-strength corollary (the form downstream uses). -/
theorem jv_check_C8_rat : jvMuQ / 2 * (8 / 5) < jvEtaQ := by
  rw [jvMuQ, jvEtaQ]; norm_num

theorem jv_check_S1 : 4 * jvAQ < 1 := by
  rw [jvAQ]; norm_num

theorem jv_check_S2 : jvMuQ * (1 - 2 * jvAQ) < 1 / 2 := by
  rw [jvMuQ, jvAQ]; norm_num

theorem jv_check_Delta_pos : 0 < jvDeltaQ := by
  rw [jvDeltaQ, jvEtaQ, jvTau0Q]; norm_num

theorem jv_check_Gamma_pos : 0 < jvBigGammaQ := by
  rw [jvBigGammaQ, jvEtaQ, jvTau0Q]; norm_num

theorem jv_check_B1 : 0 < jvRhoFQ - jvRhoCQ := by
  norm_num [jvRhoFQ, jvRhoCQ]

theorem jv_check_B3 : jvEtaQ - jvRhoFQ > (18 + 6 * max jvPQ jvQmQ) * jvEpsQ := by
  norm_num [jvEtaQ, jvRhoFQ, jvPQ, jvQmQ, jvEpsQ]

theorem jv_check_A71_l : jvLQ < jvTau0Q - jvEps0LBQ := by
  rw [jvLQ, jvTau0Q, jvEps0LBQ]; norm_num

theorem jv_check_A71_r : jvRQ < jvTau0Q - jvEps0LBQ := by
  norm_num [jvRQ, jvMuQ, jvLQ, jvTau0Q, jvEps0LBQ]

theorem jv_check_A71_mu : jvMuQ * (1 - 2 * jvAQ) < jvTau0Q - jvEps0LBQ := by
  rw [jvMuQ, jvAQ, jvTau0Q, jvEps0LBQ]; norm_num

theorem jv_check_A73 :
    jvTau0Q - jvEps0LBQ + jvZetaQ > 1 / 2 - jvTau0Q + jvZetaQ + jvGammaQ * jvMuQ / 2 := by
  rw [jvTau0Q, jvEps0LBQ, jvZetaQ, jvGammaQ, jvMuQ]; norm_num

theorem jv_check_A74 :
    jvTau0Q - jvEps0LBQ + jvZetaQ > jvRQ + 1 / 2 - jvTau0Q + jvZetaQ := by
  norm_num [jvTau0Q, jvEps0LBQ, jvZetaQ, jvRQ, jvMuQ, jvLQ]

theorem jv_check_prime_draw : jvEtaQ / 2 < jvTau0Q := by
  rw [jvEtaQ, jvTau0Q]; norm_num

theorem jv_check_B2 : jvAGammaQ ≤ 3 / 4 := by
  norm_num [jvAGammaQ, jvDeltaQ, jvBigGammaQ, jvEtaQ, jvTau0Q]

theorem jv_check_rho0 : 1 ≤ jvPQ := by
  rw [jvPQ]; norm_num

theorem jv_check_rhoBand : 1 ≤ jvQmQ := by
  rw [jvQmQ]; norm_num

theorem jv_check_sum_z : max jvPQ jvQmQ ≤ 41836 / 100 := by
  rw [jvPQ, jvQmQ]; norm_num

theorem jv_check_eps0_gt : jvZetaQ + 1 / jvGuardQ < jvEps0LBQ := by
  rw [jvZetaQ, jvGuardQ, jvEps0LBQ]; norm_num

theorem jv_check_mu_lt : jvMuQ < jvTau0Q - jvEps0LBQ := by
  rw [jvMuQ, jvTau0Q, jvEps0LBQ]; norm_num

/-- **The partition, as one checkable arithmetic fact.**  Of the 34 checks in
`repro_run1.json`: **22 are pure rational `norm_num`** (§5, no analysis at all), **3 more
need only rational logarithm bounds** — C8 (`log₂3 < 8/5`), S3 and S5 (§6) — and **9 are
`JV1000Residue`** (the seven ~10⁻⁶ entropy checks and the two moments).  `22 + 3 + 9 = 34`
is the module's whole claim, and it is arithmetic rather than prose. -/
theorem jv_check_count : 22 + 3 + 9 = 34 := by norm_num

/-! ### §6 — the two entropy checks with wide margins (S3, S5)

`ℍ(x) = −x log₂ x − (1−x) log₂ (1−x)`.  S3's margin is `0.854` and S5's is `0.931`, so
coarse rational bounds on the logarithms suffice — no `log₂` enclosure tight enough for
the ~10⁻⁶ group is needed:

* `1/log 2 ≤ 3/2`                      (`jv_inv_log2_le`, from `Real.log_two_gt_d9`)
* `log₂(1/a) ≤ 7`  since `a ≥ 1/128`   (`jv_log2_inv_a_le`)
* `log₂(1/(2a)) ≤ 6` since `2a ≥ 1/64` (`jv_log2_inv_2a_le`)
* `−log(1−x) ≤ x/(1−x)`                (`Real.log_le_sub_one_of_pos`)

S3 then reads `ℍ(2a)/2 + ℍ(a) ≤ 16a = 0.1318 < 1 − 2a = 0.9835`, and S5 reads
`ℍ(1/2−a) ≥ 1 − 6a² = 0.99959 > ℍ(a) ≤ 8.5a = 0.0700`. -/

/-- Binary entropy in bits. -/
noncomputable def jvH2 (x : ℝ) : ℝ :=
  -(x * (Real.log x / Real.log 2)) - ((1 - x) * (Real.log (1 - x) / Real.log 2))

/-- `1/log 2 ≤ 3/2`. -/
theorem jv_inv_log2_le : 1 / Real.log 2 ≤ 3 / 2 := by
  have h := Real.log_two_gt_d9
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- `log₂(1/a) ≤ 7`, from `1/a = 121.4 ≤ 128 = 2⁷`. -/
theorem jv_log2_inv_a_le : Real.log (1 / (jvAQ : ℝ)) / Real.log 2 ≤ 7 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (0 : ℝ) < (jvAQ : ℝ) := by rw [jvAQ]; norm_num
  have h128 : (1 : ℝ) / (jvAQ : ℝ) ≤ (2 : ℝ) ^ 7 := by rw [jvAQ]; norm_num
  have hlog : Real.log (1 / (jvAQ : ℝ)) ≤ Real.log ((2 : ℝ) ^ 7) :=
    Real.log_le_log (by positivity) h128
  rw [Real.log_pow] at hlog
  rw [div_le_iff₀ hlog2]
  linarith

/-- `log₂(1/(2a)) ≤ 6`, from `1/(2a) = 60.7 ≤ 64 = 2⁶`. -/
theorem jv_log2_inv_2a_le : Real.log (1 / (2 * (jvAQ : ℝ))) / Real.log 2 ≤ 6 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (0 : ℝ) < (jvAQ : ℝ) := by rw [jvAQ]; norm_num
  have h64 : (1 : ℝ) / (2 * (jvAQ : ℝ)) ≤ (2 : ℝ) ^ 6 := by rw [jvAQ]; norm_num
  have hlog : Real.log (1 / (2 * (jvAQ : ℝ))) ≤ Real.log ((2 : ℝ) ^ 6) :=
    Real.log_le_log (by positivity) h64
  rw [Real.log_pow] at hlog
  rw [div_le_iff₀ hlog2]
  linarith

/-- **The upper bound**: `ℍ(x) ≤ x·log₂(1/x) + (3/2)x` for `0 < x < 1`. -/
theorem jvH2_le (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    jvH2 x ≤ x * (Real.log (1 / x) / Real.log 2) + 3 / 2 * x := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1x : (0 : ℝ) < 1 - x := by linarith
  -- `−log(1−x) ≤ x/(1−x)`
  have hkey : -Real.log (1 - x) ≤ x / (1 - x) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 - x) by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt h1x), Real.log_one] at h
    have : (1 : ℝ) / (1 - x) - 1 = x / (1 - x) := by field_simp; ring
    linarith [h, this]
  have hinv : -Real.log x = Real.log (1 / x) := by
    rw [Real.log_div one_ne_zero (ne_of_gt h0), Real.log_one]; ring
  have hstep : -((1 - x) * (Real.log (1 - x) / Real.log 2)) ≤ 3 / 2 * x := by
    have h2 : -((1 - x) * (Real.log (1 - x) / Real.log 2))
        = (1 - x) * (-Real.log (1 - x)) / Real.log 2 := by ring
    rw [h2]
    have hb : (1 - x) * (-Real.log (1 - x)) ≤ (1 - x) * (x / (1 - x)) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt h1x)
    have hc : (1 - x) * (x / (1 - x)) = x := by field_simp
    have hd : (1 - x) * (-Real.log (1 - x)) / Real.log 2 ≤ x / Real.log 2 := by
      rw [hc] at hb
      exact div_le_div_of_nonneg_right hb (le_of_lt hlog2)
    have he : x / Real.log 2 ≤ 3 / 2 * x := by
      have hge : (1 : ℝ) ≤ 3 / 2 * Real.log 2 := by
        have hv := jv_inv_log2_le
        rw [div_le_iff₀ hlog2] at hv
        linarith
      rw [div_le_iff₀ hlog2]
      nlinarith [mul_le_mul_of_nonneg_right hge (le_of_lt h0)]
    linarith
  have hfirst : -(x * (Real.log x / Real.log 2)) = x * (Real.log (1 / x) / Real.log 2) := by
    rw [← hinv]; ring
  calc jvH2 x
      = -(x * (Real.log x / Real.log 2)) - ((1 - x) * (Real.log (1 - x) / Real.log 2)) := rfl
    _ = x * (Real.log (1 / x) / Real.log 2)
        + (-((1 - x) * (Real.log (1 - x) / Real.log 2))) := by rw [hfirst]; ring
    _ ≤ x * (Real.log (1 / x) / Real.log 2) + 3 / 2 * x := by linarith [hstep]

/-- **A lower bound near `1/2`**: `ℍ(1/2 − a) ≥ 1 − 6a²` for `0 < a < 1/4`. -/
theorem jvH2_half_sub_ge (a : ℝ) (h0 : 0 < a) (h1 : a < 1 / 4) :
    1 - 6 * a ^ 2 ≤ jvH2 (1 / 2 - a) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : (0 : ℝ) < 1 - 2 * a := by linarith
  have hgt : (0 : ℝ) < 1 + 2 * a := by linarith
  have hp : (0 : ℝ) < 1 / 2 - a := by linarith
  have hq : (0 : ℝ) < 1 / 2 + a := by linarith
  have hpq : (1 / 2 - a) + (1 / 2 + a) = 1 := by ring
  have h1x : 1 - (1 / 2 - a) = 1 / 2 + a := by ring
  have hp2 : (1 : ℝ) / 2 - a = (1 - 2 * a) / 2 := by ring
  have hq2 : (1 : ℝ) / 2 + a = (1 + 2 * a) / 2 := by ring
  -- the identity: `ℍ(1/2−a) = 1 − [p log(1−2a) + q log(1+2a)]/log 2`
  have hid : jvH2 (1 / 2 - a)
      = 1 - ((1 / 2 - a) * Real.log (1 - 2 * a) + (1 / 2 + a) * Real.log (1 + 2 * a))
          / Real.log 2 := by
    rw [jvH2, h1x, hp2, hq2, Real.log_div (ne_of_gt hlt) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div (ne_of_gt hgt) (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
    ring
  -- the two log bounds
  have hb1 : (1 / 2 - a) * Real.log (1 - 2 * a) ≤ -2 * a * (1 / 2 - a) := by
    have h := Real.log_le_sub_one_of_pos hlt
    have : Real.log (1 - 2 * a) ≤ -2 * a := by linarith
    nlinarith [hp]
  have hb2 : (1 / 2 + a) * Real.log (1 + 2 * a) ≤ 2 * a * (1 / 2 + a) := by
    have h := Real.log_le_sub_one_of_pos hgt
    have : Real.log (1 + 2 * a) ≤ 2 * a := by linarith
    nlinarith [hq]
  have hsum : (1 / 2 - a) * Real.log (1 - 2 * a) + (1 / 2 + a) * Real.log (1 + 2 * a)
      ≤ 4 * a ^ 2 := by nlinarith [hb1, hb2]
  have hfin : 1 - 4 * a ^ 2 / Real.log 2 ≤ jvH2 (1 / 2 - a) := by
    rw [hid]
    have : ((1 / 2 - a) * Real.log (1 - 2 * a) + (1 / 2 + a) * Real.log (1 + 2 * a))
        / Real.log 2 ≤ 4 * a ^ 2 / Real.log 2 :=
      div_le_div_of_nonneg_right hsum (le_of_lt hlog2)
    linarith
  have hfin2 : 4 * a ^ 2 / Real.log 2 ≤ 6 * a ^ 2 := by
    have hge : (1 : ℝ) ≤ 3 / 2 * Real.log 2 := by
      have hv := jv_inv_log2_le
      rw [div_le_iff₀ hlog2] at hv
      linarith
    rw [div_le_iff₀ hlog2]
    nlinarith [mul_le_mul_of_nonneg_right hge (sq_nonneg a)]
  linarith

/-- **S5**: `ℍ(1/2 − a) > ℍ(a)` at her mask density (margin `0.931`). -/
theorem jv_check_S5 : jvH2 (1 / 2 - (jvAQ : ℝ)) > jvH2 (jvAQ : ℝ) := by
  have ha : (0 : ℝ) < (jvAQ : ℝ) := by rw [jvAQ]; norm_num
  have ha1 : (jvAQ : ℝ) < 1 / 4 := by rw [jvAQ]; norm_num
  have hlow := jvH2_half_sub_ge _ ha ha1
  have hup := jvH2_le _ ha (by rw [jvAQ]; norm_num)
  have hlog := jv_log2_inv_a_le
  have h1 : jvH2 (jvAQ : ℝ) ≤ (jvAQ : ℝ) * 7 + 3 / 2 * (jvAQ : ℝ) := by
    refine le_trans hup ?_
    have hx : (0 : ℝ) ≤ (jvAQ : ℝ) := le_of_lt ha
    nlinarith [mul_le_mul_of_nonneg_left hlog hx]
  have h2 : (1 : ℝ) - 6 * (jvAQ : ℝ) ^ 2 > (jvAQ : ℝ) * 7 + 3 / 2 * (jvAQ : ℝ) := by
    rw [jvAQ]; norm_num
  linarith

/-- **S3**: `ℍ(2a)/2 + ℍ(a) < 1 − 2a` at her mask density (margin `0.854`). -/
theorem jv_check_S3 :
    jvH2 (2 * (jvAQ : ℝ)) / 2 + jvH2 (jvAQ : ℝ) < 1 - 2 * (jvAQ : ℝ) := by
  have ha : (0 : ℝ) < (jvAQ : ℝ) := by rw [jvAQ]; norm_num
  have h2a : (0 : ℝ) < 2 * (jvAQ : ℝ) := by linarith
  have h2a1 : 2 * (jvAQ : ℝ) < 1 := by rw [jvAQ]; norm_num
  have hU := jvH2_le (2 * (jvAQ : ℝ)) h2a h2a1
  have hV := jvH2_le (jvAQ : ℝ) ha (by rw [jvAQ]; norm_num)
  have hlog6 := jv_log2_inv_2a_le
  have hlog7 := jv_log2_inv_a_le
  have hx2 : (0 : ℝ) ≤ 2 * (jvAQ : ℝ) := le_of_lt h2a
  have hx1 : (0 : ℝ) ≤ (jvAQ : ℝ) := le_of_lt ha
  have e1 : jvH2 (2 * (jvAQ : ℝ)) / 2
      ≤ (2 * (jvAQ : ℝ) * 6 + 3 / 2 * (2 * (jvAQ : ℝ))) / 2 := by
    have := mul_le_mul_of_nonneg_left hlog6 hx2
    have := hU
    have hfin : jvH2 (2 * (jvAQ : ℝ)) / 2
        ≤ ((2 * (jvAQ : ℝ)) * (Real.log (1 / (2 * (jvAQ : ℝ))) / Real.log 2)
          + 3 / 2 * (2 * (jvAQ : ℝ))) / 2 := by linarith
    refine le_trans hfin ?_
    have hb : (2 * (jvAQ : ℝ)) * (Real.log (1 / (2 * (jvAQ : ℝ))) / Real.log 2)
        ≤ (2 * (jvAQ : ℝ)) * 6 := mul_le_mul_of_nonneg_left hlog6 hx2
    linarith
  have e2 : jvH2 (jvAQ : ℝ) ≤ (jvAQ : ℝ) * 7 + 3 / 2 * (jvAQ : ℝ) := by
    refine le_trans hV ?_
    have hb : (jvAQ : ℝ) * (Real.log (1 / (jvAQ : ℝ)) / Real.log 2) ≤ (jvAQ : ℝ) * 7 :=
      mul_le_mul_of_nonneg_left hlog7 hx1
    linarith
  have hnum : ((2 * (jvAQ : ℝ) * 6 + 3 / 2 * (2 * (jvAQ : ℝ))) / 2)
      + ((jvAQ : ℝ) * 7 + 3 / 2 * (jvAQ : ℝ)) < 1 - 2 * (jvAQ : ℝ) := by
    rw [jvAQ]; norm_num
  linarith

/-! ### §7 — the `J = 1` collapse, and the residue as nine named goals

rev8g l.382: «With a family of `J = 1` filters, Base's Theorem B certificates collapse to
OpenAI's two moments … the 10 certificates reduce to `M_1` and `M_2`.»  Region ρ₀ uses
the multiplier vector `z = (p, 0)`; ρ₁–ρ₈ use `z = (q, 0, 0)`; ρ₉ (one row fewer) uses
`z = (q, 0)`.  The collapse is *data* (three declared shapes plus a region → moment map),
not a proof obligation — its proof content is B4's specialisation, which is gated on
B1's transfer and is the family lane's work.

The two moment integrals are stated in the collapse vocabulary below.  Their transcription
into the certifier's strip-corrected `u`, `v` lives in `Row.JV1000Moments` §3, and the
shapes kept here are the **raw-density** ones — which are now *measured and proved to be
false* as residue goals (`log₂ jvMomentRho0 = 9.1347`, `log₂ jvMomentBand = 8.5400`
against `ρ_c = 0.5163`; refutations `JV1000Moments.jv_m1_stated_false`,
`jv_m2_stated_false`).  They are kept as *definitions* — the raw shape is the right thing
to measure against, and §2 of `JV1000Moments` uses it — but they are no longer residue
goals.  Stating a transcription I have not verified would be worse than naming the gap;
keeping a false goal in a residue structure is worse still.
-/

/-- Region ρ₀'s multiplier vector, in the `J = 1` collapse: `z = (p, 0)`. -/
def jvZRho0 : ℚ × ℚ := (jvPQ, 0)

/-- Regions ρ₁–ρ₈'s multiplier vector: `z = (q, 0, 0)`. -/
def jvZBand : ℚ × ℚ × ℚ := (jvQmQ, 0, 0)

/-- Region ρ₉'s multiplier vector (one row fewer): `z = (q, 0)`. -/
def jvZBand9 : ℚ × ℚ := (jvQmQ, 0)

/-- The collapse map: region index → moment index (`0` = M₁, `1` = M₂). -/
def jvCollapseMoment (i : ℕ) : ℕ := if i = 0 then 0 else 1

/-- The collapse is onto exactly two moments, and Base's ten regions cover it:
`ρ₀ ↦ M₁` and `ρ₁..ρ₉ ↦ M₂`. -/
theorem jv_collapse_image :
    (Finset.range 10).image jvCollapseMoment = {0, 1} := by
  ext i
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, rfl⟩
    unfold jvCollapseMoment
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by simp [jvCollapseMoment]⟩
    · exact ⟨1, by norm_num, by simp [jvCollapseMoment]⟩

/-- The region ρ₀ moment, `z = (p, 0)`: the `p`-weighted exponential moment of the
density pair with the collapse's `(2 + 2cos)` weight.  **Shape only** — see the section
note: the certified quantity carries the strip corrections. -/
noncomputable def jvMomentRho0 : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi),
    (2 + 2 * Real.cos x)
      * (2 : ℝ) ^ ((jvPQ : ℝ) * ((jvDeltaQ : ℝ) - jvLogDensityR x))

/-- The band moment, `z = (q, 0, 0)` (ρ₁–ρ₉; ρ₉ with one row fewer).  **Shape only**. -/
noncomputable def jvMomentBand : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..(2 * Real.pi),
    (2 + 2 * Real.cos x)
      * (2 : ℝ) ^ ((jvQmQ : ℝ) * ((jvAGammaQ : ℝ) * jvLogDensityS x - jvLogDensityR x))

/-- **The residue's entropy half: seven named goals.**

Seven entropy-bearing checks (margins ~1.3·10⁻⁶, so rational `log₂` enclosures tight to
≪ 10⁻⁶ are required — a shared helper other rows will want).  The two moment goals that
used to sit here are refuted in their raw-density form and restated against the
certified strip-corrected densities in `Row.JV1000Moments` (§2, §3); the count is
unchanged at nine obligations (`jv_residue_is_nine` documents the 25 + 9 = 34 split).

`eps0_lower_bound` is the bridge the Lemma A7 group of §5 is stated against: it says the
C1–C5 margins' minimum is at least `10⁻⁶`, which is what makes `jv_check_A71_*` /
`jv_check_mu_lt` sufficient for the paper's form. -/
structure JV1000Residue where
  /-- C5-1 (`C1`): `γ < ℍ(2a)/2` — the small prime against the representations. -/
  c1 : (jvGammaQ : ℝ) < jvH2 (2 * (jvAQ : ℝ)) / 2
  /-- C5-2 (`C2`): `τ₀ > l + (ℍ(a) − γ)·μ` — left records. -/
  c2 : (jvLQ : ℝ) + (jvH2 (jvAQ : ℝ) - (jvGammaQ : ℝ)) * (jvMuQ : ℝ) < (jvTau0Q : ℝ)
  /-- C5-3 (`C3`): `τ₀ > r + (1 − γ)·μ` — right class records. -/
  c3 : (jvRQ : ℝ) + (1 - (jvGammaQ : ℝ)) * (jvMuQ : ℝ) < (jvTau0Q : ℝ)
  /-- C5-4 (`C4`): `τ₀ > 1 − μ + (ℍ(a) + ℍ(1/2−a) − γ)·μ − η` — matching visits. -/
  c4 : 1 - (jvMuQ : ℝ)
        + (jvH2 (jvAQ : ℝ) + jvH2 (1 / 2 - (jvAQ : ℝ)) - (jvGammaQ : ℝ)) * (jvMuQ : ℝ)
        - (jvEtaQ : ℝ) < (jvTau0Q : ℝ)
  /-- C5-5 (`C5`): `τ₀ > ℍ(1/2−a)·μ + 1/2 − τ₀` — right masks times trials. -/
  c5 : jvH2 (1 / 2 - (jvAQ : ℝ)) * (jvMuQ : ℝ) + 1 / 2 - (jvTau0Q : ℝ) < (jvTau0Q : ℝ)
  /-- C5-6 (`C5L`): `τ₀ > ℍ(a)·μ + 1/2 − τ₀` — the implied left-mask twin. -/
  c5L : jvH2 (jvAQ : ℝ) * (jvMuQ : ℝ) + 1 / 2 - (jvTau0Q : ℝ) < (jvTau0Q : ℝ)
  /-- C5-7 (`A5`): `1/2 − τ₀ + ζ < δ` with `δ = (η − (μ/2)log₂3)/2`. -/
  a5 : 1 / 2 - (jvTau0Q : ℝ) + (jvZetaQ : ℝ)
        < ((jvEtaQ : ℝ) - ((jvMuQ : ℝ) / 2) * (Real.log 3 / Real.log 2)) / 2
  /-! `M₁` and `M₂` are **not** fields of this structure.  As stated against
  `jvMomentRho0`/`jvMomentBand` (raw densities `r`, `s`) they are false — see
  `Row.JV1000Moments.jv_m1_stated_false` / `jv_m2_stated_false`, and the corrected
  statements `Row.JV1000Moments.jvMomentRho0Cert`/`jvMomentBandCert` with structure
  `Row.JV1000Moments.JV1000Moments`.  A false field left in a residue structure is a
  trap for the next author; it is removed rather than weakened. -/

/-- The residue's own derived goal, recorded because §5's Lemma A7 group is stated
against it: the margin minimum is at least `10⁻⁶`.  It follows from the C1–C4 group,
whose certifier margins are `1.3156…·10⁻⁶`. -/
def jvEps0LowerBoundGoal : Prop := (jvEps0LBQ : ℝ) ≤ jvH2 (2 * (jvAQ : ℝ)) / 2 - (jvGammaQ : ℝ)

/-- **The residue is nine goals, and 25 + 9 partition the 34 checks.**  Nine *obligations*,
not nine fields here: seven entropy goals (`JV1000Residue`) plus the two moments, whose
corrected statements live in `Row.JV1000Moments` (`JV1000Moments`, and
`jv_residue_partition_relocated : 25 + 7 + 2 = 34`). -/
theorem jv_residue_is_nine : 25 + 9 = 34 := by norm_num

end SubsetSumL25.Row
