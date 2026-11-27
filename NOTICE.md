NOTICE — third-party portions, attribution, and upstream licenses
=================================================================

This repository's own portions (AI-assisted, disclosed work) are licensed under the
Copy-Free/Stays-Free (CFSF) License — see LICENSE. Nothing here changes the upstream
licenses of third-party material; those apply to their portions as published upstream.

The mathematics formalized here is credited to its authors; this package provides the
Lean 4 formalization, not the results:

- **L2.1 / L2.2 / L2.3 / L2.5 / L5.2 coverage lemmas, Thm 4.1 / Thm 5.1, L3.2 finite
  filtering data** — OpenAI, `openai/math` subset-sum material (Apache-2.0), preprint
  «Subset-Sum in Time O(2^0.49n)» @ `adc7f124`.
- **Combinatorial core (L3.1–3.3, Corollary D, Lemma A5 / Cor A6, Theorem B regions,
  Prop P, word-RAM accounting, the `D_s` dictionary)** — Base (a-kapila),
  `a-kapila/maths-proofs` @ `44c34961`, `subset-sum/PROOF_0.4877.tex` (paper-only;
  formalized here with attribution).
- **Region-predicate template** — Bills (`Verification/Regions.lean` /
  `RowMargins.lean`), re-expressed locally for this package's Mathlib pin; credit chain
  Base → Bills → this package.
- **Sine extension (V1)** — jv1000, rev8g §8 «Independent checks and admissibility»
  (paper-only; formalized here with attribution).
