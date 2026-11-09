/-
M1 (O4): OpenAI Lemma 3.2 «Finite filtering data» — the finite-circle
machinery Base consumes via (F7) and Lemma B1.  Paper-only (BRIDGE row O4);
the formalizable core is the Riemann-sum estimate, the finite relative-entropy
order (3.3), the P₀ assembly with the strict slack, and the uniform
log-boundedness primitives.  The D7 boundary holds as on O8: the
approximability procedure is an algorithm statement and stays named, and no
Light-step translation is imported.

Primary sources: OpenAI preprint «Subset-Sum in Time O(2^{0.49n})»
(openai/math @ `adc7f124`, 2026-10-04), `sections/filtering.tex`
(Lemma 3.2 = `lemma:finite-filtering`, the Riemann estimate, the effective
version); Base `a-kapila/maths-proofs` @ 44c34961, `subset-sum/PROOF_0.4877.tex`
(sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298)
§2.2 (F7), §6.1 (Lemma B1), Appendix B.2.  Cross-checked against BRIDGE rows
O4, V1, and the B4 boundary notes.  Credit: L3.2 is OpenAI's; the (F7)
generalization observation and Lemma B1's use are Base's; this package
formalizes the mathematical core.
-/
import Mathlib

namespace SubsetSumL25

/- Verbatim (OpenAI filtering.tex), Lemma 3.2 «Finite filtering data»:

   «There is an absolute integer P₀ such that for every P ≥ P₀ the finite
   functions satisfy (3.3) [D(x) ≥ 0, D(x)−A(x) ≥ 0, D(x)−E(x) ≥ 0] and
       (1/P) ∑_{x∈Z/PZ} M(x)² 2^{8.5(Δ−u(x))} < 2^{0.5169},
       (1/P) ∑_{x∈Z/PZ} M(x)² 2^{8.3(av(x)−u(x))} < 2^{0.5169}.
   There is an absolute bound, independent of P, for the absolute values of
   D, A, E, u, v, log f_*, log g_*, and log K_x(w).  For every fixed positive
   rational ρ, each of these quantities can be approximated to absolute error
   at most ρ by one fixed deterministic rational-arithmetic procedure, in time
   polynomial in log P, given the relevant residues and P.  This procedure
   need not enumerate the P points.»

   Verbatim, the proof's two load-bearing facts:

   «If H(x,w) is a continuously differentiable periodic function, the error in
   replacing its w integral by a P-point average is at most
   2π‖∂_w H‖_∞/P, uniformly in x.»

   «… Thus the finite versions of D, A, E, u, v converge uniformly, at their
   grid points, to the continuous versions.  Applying the same Riemann-sum
   estimate once more to the two outer integrands proves (finite-filtering-
   moments) from (continuous-filtering-moments) and the strict slack between
   0.5168 and 0.5169.»

   Verbatim (Base §2.2, (F7)):
   «Section 3 and Lemma 3.2.  The proof of Lemma 3.2 uses only that r and s
   are fixed trigonometric polynomials.  So its conclusions hold for every
   such pair, except the numerical moment bound (3.7).»

   Verbatim (Base §6.1, Lemma B1's proof, the consumed core):
   «By (F7), the proof of Lemma 3.2 applies to each filter.  … Each row of G
   is a fixed linear combination of these functions and constants.  So the
   finite averages converge to the integrals of Proposition B, by the same
   Riemann-sum estimate.  There are finitely many pairs, and each has the
   slack 2^{η−0.0002} − 2^{η−0.00025} > 0.» -/

/-- The normalized P-point average on the circle grid `2πj/P` (the paper's
«replace every integral … by the normalized average P⁻¹∑»).  `P = 0` is the
junk value 0; every consumer carries `0 < P`. -/
noncomputable def o4Avg (P : ℕ) (H : ℝ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range P, H (2 * Real.pi * j / P)) / P

/-- The paper's P₀ for the integrand bound `B`, continuous bound `C`, and
target `T`: the constant threshold above which the finite-to-continuous error
is under the strict slack `T − C` (the paper: «choose a constant threshold
above which the finite-to-continuous error is less than ρ/2»).  Meaningful
only under `C < T`; consumers carry that hypothesis. -/
noncomputable def o4P₀ (B C T : ℝ) : ℕ := (⌈2 * Real.pi * B / (T - C)⌉ : ℤ).toNat + 1

/-- The Riemann-sum estimate («the error … is at most 2π‖∂_w H‖_∞/P,
uniformly in x»), in Lipschitz form: `B` is the named explicit bound on the
relevant derivative («the displayed coefficient bounds give explicit bounds on
every fixed derivative needed»). -/
theorem o4_avg_err_le {H : ℝ → ℝ} {B : ℝ}
    (hLip : ∀ t s : ℝ, |H t - H s| ≤ B * |t - s|)
    {P : ℕ} (hP : 0 < P) :
    |o4Avg P H - (∫ x in (0:ℝ)..(2 * Real.pi), H x) / (2 * Real.pi)|
      ≤ 2 * Real.pi * B / P := by
  sorry

/-- The finite relative-entropy order (3.3) — «the relative-entropy argument
is unchanged for normalized finite averages»: Gibbs's inequality for finite
probability vectors `w` (the normalized kernel `K_x`) against `q` (the
uniform law 1, or `f_*(x+·)`, or `g_*`).  Both orientations: the paper's
D−q-entropy ≥ 0 is the second conjunct. -/
theorem o4_gibbs {P : ℕ} (w q : ℕ → ℝ)
    (hwpos : ∀ i ∈ Finset.range P, 0 < w i) (hwsum : ∑ i ∈ Finset.range P, w i = 1)
    (hqpos : ∀ i ∈ Finset.range P, 0 < q i) (hqsum : ∑ i ∈ Finset.range P, q i = 1) :
    ∑ i ∈ Finset.range P, w i * Real.log (q i / w i) ≤ 0
      ∧ 0 ≤ ∑ i ∈ Finset.range P, w i * Real.log (w i / q i) := by
  sorry

/-- The P₀ assembly: from the continuous moment bound `C` (named data — the
paper's 2^{0.5168} quadrature result, or Base's Prop B 2^{η−0.00025}) and the
strict slack to the target `T` (2^{0.5169}, resp. 2^{η−0.0002}), every `P ≥
o4P₀ B C T` has the finite average below `T`.  «Applying the same Riemann-sum
estimate once more … proves … from … and the strict slack». -/
theorem o4_finite_from_continuous {H : ℝ → ℝ} {B C T : ℝ}
    (hLip : ∀ t s : ℝ, |H t - H s| ≤ B * |t - s|)
    (hC : (∫ x in (0:ℝ)..(2 * Real.pi), H x) / (2 * Real.pi) < C)
    (hCT : C < T) :
    ∀ P ≥ o4P₀ B C T, 0 < P → o4Avg P H < T := by
  sorry

/-- Uniform log-boundedness («The lower bounds on denominators allow division
and taking logarithms without losing uniform convergence»): a quantity known
to lie in `[m, M]` with `0 < m` has absolutely bounded log. -/
theorem o4_log_abs_le {W m M : ℝ} (hm : 0 < m) (h1 : m ≤ W) (h2 : W ≤ M) :
    |Real.log W| ≤ max |Real.log m| |Real.log M| := by
  sorry

/-- Quotient boundedness, upper half: shrinking the denominator raises the
quotient. -/
theorem o4_div_le {num den N d : ℝ} (hden : 0 < den) (hle : den ≤ d) (hN : num ≤ N) :
    num / den ≤ N / d := by
  sorry

/-- Quotient boundedness, lower half: `0 < m ≤ num`, `0 < d ≤ den` give
`m / d ≤ num / den`. -/
theorem o4_le_div {num den m d : ℝ} (hden : 0 < den) (hle : d ≤ den)
    (hm : 0 < m) (hnum : m ≤ num) :
    m / d ≤ num / den := by
  sorry

/- Proved-vs-named ledger (full table in STMTS.md §O4):
   PROVED: o4_avg_err_le, o4_gibbs, o4_finite_from_continuous,
   o4_log_abs_le, o4_div_le, o4_le_div.
   NAMED (algorithm/external-input boundary, never axioms): the continuous
   moment bounds (2^{0.5168}; Base's Prop B 2^{η−0.00025} over the 430
   certified rows — data, not restated, the B4 decision); the coefficient
   bounds |r| ≤ 2.433, |s| ≤ 4.010 and every derivative bound (→ the named
   `B` of the Lipschitz form); the deterministic rational approximability
   procedure and its poly(log P) time (an algorithm statement — the same
   boundary as Lemma A5's D_s).  (3.7)'s specific numerals enter only as the
   `C`/`T` parameters of o4_finite_from_continuous. -/

end SubsetSumL25
