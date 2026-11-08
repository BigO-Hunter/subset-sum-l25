/-
Base (a-kapila) B4 — Theorem B's region analysis: the §6.1 region partition,
Lemma B2 (domination), and the a_Γ ≤ 3/4 per-row guard.

Primary source: `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298), §6.1
(regions + certificate data), §6.3 (Lemma B2).  Verified against
`subset-sum-bridge/BRIDGE.md` appendix row B4 («matches»).  Credit: regions,
certificates and Lemma B2 are Base's; the region-predicate shape follows Bills'
`Regions.lean` template (yannouli-ss verification/lean), credited in STMTS.md
§B4.  The certificate numerics (Prop B's 430 integrals, Appendix C rows) are
separately certified and enter here only as data.

Verbatim (PROOF_0.4877.tex §6.1):

    Regions.  Put b₀ = 1, b₁ = 1.25, b₂ = 1.6, b₃ = 2, b₄ = 2.6, b₅ = 3.5,
    b₆ = 5, b₇ = 8, b₈ = 15 and b₉ = ∞.  A real number W lies in the region ρ₀
    if W ≤ Γ, and in the region ρᵢ (1 ≤ i ≤ 9) if Γb_{i−1} < W ≤ Γbᵢ.

    Every certificate has Σ_t z_t ≤ 418.36.

Verbatim (§6.3, Lemma B2 and its proof's two cases):

    Lemma B2 (domination).  Let π be a sampled pattern, v = v*(π), and ρ the
    region of W_{v,π}.  Let z and G be the certificate data for (v, ρ).  Then
    every frequency k of pattern π satisfies
        −α_π U_{v,π} ≤ −Δ + (1/n)Σ_{i=1}^n z·G(x_i) + 6ε Σ_t z_t.

    … the rows have errors at most 3ε, 4ε, 6ε, (4a_Γ+3)ε, 4ε and 4ε. …
    [z·Ḡ ≥ z₀G^π₀ − 6ε Σ_t z_t.]
    Region ρ₀.  Here W_{v,π} ≤ Γ, so α_π = 1.  Sampling means U_{v,π} < Δ.  Then
    G^π₀ = Δ − U_{v,π} > 0 and z₀ ≥ 1 give −U_{v,π} = −Δ + G^π₀ ≤ −Δ + z₀G^π₀.
    Region ρᵢ, i ≥ 1.  Here W_{v,π} > Γb_{i−1} ≥ Γ.  So α_π = Γ/W_{v,π} <
    1/b_{i−1} ≤ z₀, and α_π a_Γ W_{v,π} = Δ.  Sampling means α_π U_{v,π} < Δ,
    that is, G^π₀ = a_Γ W_{v,π} − U_{v,π} > 0.  Then −α_π U_{v,π} = −Δ +
    α_π G^π₀ ≤ −Δ + z₀ G^π₀.

Scope (BRIDGE row B4): the region structure and the domination argument are
formalized; Prop B's 430 integral bounds are separately certified and enter as
data.  Theorem B itself is an *algorithm* statement (FAIL / estimates / error
/ word count) — like Lemma A5's `D_s`, it is outside this package; the §6.1 +
§6.3 content above is the rung.  The empty-expect audit finds nothing to carry:
B4 has no `Finset.expect` anywhere (its hypotheses are pointwise), so there is
no silent-`0` degeneracy class in this file.

`sorry`: M1 placeholders — proof targets `Proofs/ThmB.lean` (M2, M3).
-/
import Mathlib

namespace SubsetSumL25

/-- The nine finite band tops of §6.1: b₀ = 1, b₁ = 1.25, b₂ = 1.6, b₃ = 2,
b₄ = 2.6, b₅ = 3.5, b₆ = 5, b₇ = 8, b₈ = 15 (exactly Bills' list — template
credited).  `bandUpper 9 = 0` is junk: the ninth region has no upper bound. -/
noncomputable def bandUpper : ℕ → ℝ
  | 0 => 1
  | 1 => 5 / 4
  | 2 => 8 / 5
  | 3 => 2
  | 4 => 13 / 5
  | 5 => 7 / 2
  | 6 => 5
  | 7 => 8
  | 8 => 15
  | _ => 0

/-- Base §6.1 verbatim: «A real number W lies in the region ρ₀ if W ≤ Γ, and in
the region ρᵢ (1 ≤ i ≤ 9) if Γb_{i−1} < W ≤ Γbᵢ» — ρ₉'s upper bound is absent
(b₉ = ∞).  Indices above 9 are not regions; the lemmas take `i ≤ 9`. -/
def inRegion (Γ W : ℝ) : ℕ → Prop
  | 0 => W ≤ Γ
  | (i + 1) => Γ * bandUpper i < W ∧ (i + 1 = 9 ∨ W ≤ Γ * bandUpper (i + 1))

/-- The regions cover: every `W` lies in exactly one of ρ₀..ρ₉ (for `Γ > 0`).
(Bills' `region_existence` / `region_disjoint` / `full_region_partition`
pattern — template credited.) -/
theorem region_existence (hΓ : 0 < Γ) (W : ℝ) : ∃ i, i ≤ 9 ∧ inRegion Γ W i := by
  sorry

theorem region_disjoint (hΓ : 0 < Γ) (W : ℝ) (i j : ℕ) (hi : i ≤ 9) (hj : j ≤ 9)
    (hI : inRegion Γ W i) (hJ : inRegion Γ W j) : i = j := by
  sorry

theorem region_unique (hΓ : 0 < Γ) (W : ℝ) :
    ∃! i, i ≤ 9 ∧ inRegion Γ W i := by
  obtain ⟨i, hi, hI⟩ := region_existence hΓ W
  exact ExistsUnique.intro i ⟨hi, hI⟩
    (fun y (hy : y ≤ 9 ∧ inRegion Γ W y) =>
      (region_disjoint hΓ W i y hi hy.1 hI hy.2).symm)

/-- The referee-extracted per-row guard (BRIDGE row B4): `a_Γ ≤ 3/4` makes the
fourth row's error `(4a_Γ+3)ε` at most `6ε`, so **all six** rows of the
certificate vector have error at most `6ε` (§6.3: «the rows have errors at most
3ε, 4ε, 6ε, (4a_Γ+3)ε, 4ε and 4ε»). -/
theorem row_errors_le_six_eps {ε aΓ : ℝ} (hε : 0 ≤ ε) (haΓ : aΓ ≤ 3 / 4)
    {e₁ e₂ e₃ e₄ e₅ e₆ : ℝ}
    (h₁ : e₁ ≤ 3 * ε) (h₂ : e₂ ≤ 4 * ε) (h₃ : e₃ ≤ 6 * ε)
    (h₄ : e₄ ≤ (4 * aΓ + 3) * ε) (h₅ : e₅ ≤ 4 * ε) (h₆ : e₆ ≤ 4 * ε) :
    e₁ ≤ 6 * ε ∧ e₂ ≤ 6 * ε ∧ e₃ ≤ 6 * ε ∧ e₄ ≤ 6 * ε ∧ e₅ ≤ 6 * ε ∧ e₆ ≤ 6 * ε := by
  sorry

/-- Lemma B2's display (§6.3): `z·Ḡ ≥ z₀G^π₀ − 6ε Σ_t z_t`, from the uniform
row errors, the certificate's `z ≥ 0`, and the region/maximality nonnegativity
of every pattern row except the distinguished row `t₀`. -/
theorem z_dot_Gbar_ge {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 ≤ ε)
    {Gbar Gpi z : ι → ℝ} {t₀ : ι}
    (hrowerr : ∀ t, |Gbar t - Gpi t| ≤ 6 * ε)
    (hz₀ : 0 ≤ z t₀) (hGpi₀ : 0 ≤ Gpi t₀) (hGpi : ∀ t ≠ t₀, 0 ≤ Gpi t) :
    z t₀ * Gpi t₀ - 6 * ε * ∑ t, z t ≤ ∑ t, z t * Gbar t := by
  sorry

/-- Lemma B2, region ρ₀ (verbatim: «Here W_{v,π} ≤ Γ, so α_π = 1.  Sampling
means U_{v,π} < Δ.  Then G^π₀ = Δ − U_{v,π} > 0 and z₀ ≥ 1 give
−U_{v,π} = −Δ + G^π₀ ≤ −Δ + z₀G^π₀»). -/
theorem lem_B2_region_zero {Δ α U G₀ z₀ : ℝ} (hα : α = 1) (hU : U < Δ) (hG₀ : 0 < G₀)
    (hz₀ : 1 ≤ z₀) : -α * U ≤ -Δ + z₀ * G₀ := by
  sorry

/-- Lemma B2, regions ρ₁..ρ₉ (verbatim: «Here W_{v,π} > Γb_{i−1} ≥ Γ.  So
α_π = Γ/W_{v,π} < 1/b_{i−1} ≤ z₀, and α_π a_Γ W_{v,π} = Δ.  Sampling means
α_π U_{v,π} < Δ, that is, G^π₀ = a_Γ W_{v,π} − U_{v,π} > 0.  Then
−α_π U_{v,π} = −Δ + α_π G^π₀ ≤ −Δ + z₀ G^π₀»).  `b` is `b_{i−1}` (and `15` for
ρ₉). -/
theorem lem_B2_region_band {Δ α U aΓ W G₀ z₀ b : ℝ} (hΓ : 0 < Γ) (hb : 0 < b)
    (hα : α = Γ / W) (hW : Γ * b < W) (haΓΔ : α * aΓ * W = Δ) (hU : α * U < Δ)
    (hG₀ : 0 < G₀) (hG₀def : G₀ = aΓ * W - U) (hz₀ : 1 ≤ z₀ * b) :
    -α * U ≤ -Δ + z₀ * G₀ := by
  sorry

/-- Lemma B2 (domination), verbatim conclusion: the dispatch of the two region
cases against Lemma B2's display.  `zGbar` is the paper's `z·Ḡ =
(1/n)Σ_{i=1}^n z·G(x_i)`; `t₀` is row `0` of the certificate vector. -/
theorem lem_B2_domination {ι : Type*} [Fintype ι] {ε Δ α U G₀ zGbar : ℝ}
    {Gbar Gpi z : ι → ℝ} {t₀ : ι}
    (hG₀ : 0 < G₀) (hGpi₀ : 0 ≤ Gpi t₀) (hGpi : ∀ t ≠ t₀, 0 ≤ Gpi t)
    (hz₀ : 0 ≤ z t₀)
    (hzdot : z t₀ * Gpi t₀ - 6 * ε * ∑ t, z t ≤ zGbar)
    (hcase : -α * U ≤ -Δ + z t₀ * Gpi t₀) :
    -α * U ≤ -Δ + zGbar + 6 * ε * ∑ t, z t := by
  sorry

end SubsetSumL25
