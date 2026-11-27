/-
M1 (V1): jv1000's sine extension — verbatim quotes and pointers.  This
file holds NO declarations: the statement-of-record for everything proved
is `Proofs/JV1000.lean` (same pattern as Statements/O4.lean).

Source of record: jv1000 rev8g §8 «Independent checks and admissibility»
(paper_2026-11-06_rev8g.tex l.410) + the referee3 verdict, cross-checked
against rung V1.  Base anchors: PROOF_0.4877.tex @
44c34961 (sha256 b397531cc…) filter definition l.620–627, cosine-only
statements l.1038–1040, Appendix D.2's trig_nodes/abs_sum.

Verbatim (rung V1, the four extracted items):

  «Let the log-density polynomials be r(x) = Σ_{j=1}^{16}(a_j cos jx + b_j
  sin jx) and s(x) likewise — 16 cosine + 16 sine terms per density
  (64 coefficients; Base's filters are 8-term cosine-only).»

  1. «Positivity/smoothness: 2^r, 2^s are strictly positive and C^∞ on 𝕋;
     the densities f = 2^r/∫2^r, g = 2^s/∫2^s are well-defined for any
     coefficient choice.»
  2. «Relative-entropy identities: D ≥ 0, D−A ≥ 0, D−E ≥ 0 (Base (3.3))
     and the definitions of u, w hold unchanged — they are relative
     entropies regardless of the filters' parity.»
  3. «Uniform boundedness (the O4-invoking step): at the certified point
     |r(x)|, |s(x)| < 3.21 by summing harmonic amplitudes, and every
     required fixed derivative is bounded explicitly by its coefficient
     sum with harmonic powers.  Hence OpenAI Lemma 3.2's uniform-
     boundedness argument applies without an evenness assumption — this is
     what lets (F7) cover sine terms and Lemma B1 transfer to P ≥ P₀ (all
     L3.2 conclusions except (3.7)).»
  4. «Affected Base lines: filter definition l.620–627, cosine-only
     statements l.1038–1040, and Appendix D.2's trig_nodes/abs_sum
     (cosine-only; jv1000's rig_M.py replaces D.2, bounding sine terms by
     Σ√(a²+b²)·cosh(jy)).»

Premise boundary: item 3 is the only non-bookkeeping content; items 1–2
are definitional.

Proved-vs-named ledger (see Proofs/JV1000.lean for the statements):
  PROVED  item 1 — positivity, C^∞ smoothness, density well-definedness.
  PROVED  item 3 — harmonic-amplitude bound, certified-point corollary
          (|r| ≤ 3.21 shape), cos/sin Lipschitz, r' bound by the
          coefficient sum with harmonic powers, and the O4 transfer:
          o4_finite_from_continuous / o4_log_abs_le instantiate at the
          sine-inclusive family with NO parity hypothesis anywhere.
  NAMED   item 2 — the continuous relative-entropy assembly (D ≥ 0,
          D−A ≥ 0, D−E ≥ 0 for the densities): o4_gibbs is the discrete
          hook (already parity-free); the integral-form assembly is an
          M2 target.
  NAMED   item 4 — the rig_M modulus bound Σ√(a²+b²)·cosh(jy): complex-
          trig arithmetic, M2 target.
  NAMED   the «Lemma B1 transfers to P ≥ P₀» full statement: Lemma B1 is
          itself unformalized (ThmB.lean carries the B4 region machinery
          only); the V1→B1 interface is the O4 hooks this file proves
          parity-free, and the assembly lands with B1.

Credit chain: Base → Bills → us.  jv1000 asserts items 1–2 with derivation
sketch and referee confirmation; the package formalizes the mathematical
core at the O4 hooks.
-/
import Mathlib
