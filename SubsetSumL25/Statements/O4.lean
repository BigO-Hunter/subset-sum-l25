/-
M1 (O4): OpenAI Lemma 3.2 «Finite filtering data» — verbatim quotes and
pointers.  This file holds NO declarations: the statement-of-record for
everything is `Proofs/O4.lean` (M2 proved all six, with two statement
corrections recorded there and in STMTS.md §O4).

Paper-only (BRIDGE row O4); the D7 boundary holds as on O8: the
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
   slack 2^{η−0.0002} − 2^{η−0.00025} > 0.»

Declarations (all in `Proofs/O4.lean`, all proved — see STMTS.md §O4 for the
proved-vs-named ledger and the two statement corrections):

* `o4Avg`                    — the normalized P-point circle average (P⁻¹∑
                               over the grid 2πj/P); junk `P = 0` guarded by
                               `0 < P` on every consumer.
* `o4P₀`                     — the explicit ceiling threshold («choose a
                               constant threshold above which the
                               finite-to-continuous error is less than ρ/2»).
* `o4_avg_err_le`            — the Riemann estimate 2π‖∂_w H‖_∞/P, Lipschitz
                               form (`B` = the named derivative bound).
* `o4_gibbs`                 — the finite relative-entropy order (3.3)
                               («the relative-entropy argument is unchanged
                               for normalized finite averages»).
* `o4_finite_from_continuous`— the strict-slack assembly (continuous bound C
                               < target T ⟹ finite average < T for P ≥ P₀);
                               (3.7)'s numerals enter only as C/T parameters
                               — Base's own (F7) exclusion respected.
* `o4_log_abs_le`, `o4_div_le`, `o4_le_div` — the uniform-boundedness
                               primitives; the composition with the displayed
                               constants |r| ≤ 2.433, |s| ≤ 4.010 is named
                               data, as is the certified moment data
                               (2^{0.5168}; Prop B's 430 rows — the B4
                               decision, not restated).

Statement-hygiene notes carried from M1:

* **Empty-expect audit:** no `Finset.expect` in any O4 statement. Junk
  guards: `P = 0` on `o4Avg` (guarded by `0 < P` on consumers), the division
  in `o4P₀` (guarded by `C < T`), all `q/w` divisions in `o4_gibbs` (guarded
  by strict positivity — the paper's `K_x` is a strictly positive density).
* M2 corrections (hn07 pattern): the quotient-boundedness pair was restated
  in `Proofs/O4.lean` — the M1 hypothesis directions were false; the corrected
  pair matches the paper's `K_x = f·g/Q` use exactly.
-/

end SubsetSumL25
