# subset-sum-l25

Lean 4 formalization of the lemma ladder behind the sub-½ subset-sum attack: the OpenAI coverage lemmas (L2.1 / L2.2 / L2.3 / L2.5 / L5.2) and the Base (a-kapila) combinatorial core they feed. AI-assisted; disclosed.

## Board state (BigO Speedrun, subset-sum race)

The race is **open**. Current leader: **OpenAI + 2 more, O(2^{0.49995n})**, Nov 26 2026, Lean Verified ([bigospeedrun.com](https://bigospeedrun.com)). This org's earlier α = ½ baseline is **superseded** by that bound; it is preserved in the [subset-sum](https://github.com/BigO-Hunter/subset-sum) umbrella. No bound is yet provably optimal, so the race is not closed.

This repo is the **formalization shelf** those attacks build on: kernel-checked statements of the coverage and combinatorial lemmas, reusable by anyone pursuing a better bound. It claims no board row of its own.

## What is here

Everything below is **proved** — zero `sorry`, and every theorem's `#print axioms` is exactly `[propext, Classical.choice, Quot.sound]` (no `native_decide`, no new axioms). Paper premises that are external inputs appear as **named hypotheses**, never as Lean `axiom`s; algorithm procedures stay named (the honest boundary, documented per rung in [STMTS.md](STMTS.md)).

| Cluster | Content | Where |
|---|---|---|
| **L2.5** | OpenAI coverage lemmas: isolation, deficiency, random restrictions, random-prime collisions, sparse distinctions | `Statements/`, `Proofs/` |
| **PRIMECOUNT** | Erdős dyadic prime count — discharges the PNT premise `hcount`, making L2.5 / L5.2 unconditional number theory | `Proofs/PrimeCount.lean` |
| **B1–B5** | Base combinatorial core: covering / sampling / good layer (L3.1–3.3), Corollary D, Lemma A5 + Cor A6, Theorem B region machinery, Prop P + cost accounting | `Proofs/Layers,CorD,A5,ThmB,Presearch.lean` |
| **O4 / O8 / O5+O7** | finite filtering data, word-RAM accounting, checksum (Thm 4.1) + alias-extraction (Thm 5.1) cores | `Proofs/O4,O8,O57.lean` |
| **V1** | jv1000 sine extension — parity-free O4 hooks (positivity, smoothness, uniform boundedness, transfer) | `Proofs/JV1000.lean` |
| **DS** | the `D_s` alias-class dictionary core: signed-weight identities, class machinery, soundness, closure corollary | `Proofs/DS.lean` |

- [STMTS.md](STMTS.md) — verbatim paper statements, translation notes, and the proved-vs-named ledger per rung.
- [PROGRESS.md](PROGRESS.md) — milestone receipts, statement corrections caught by proving, and Mathlib-pin gotchas.
- [NOTICE.md](NOTICE.md) — upstream attribution and licenses.

## Reproduce / verify

Pins: **Lean v4.34.1**, **Mathlib d13f23b** (the subset-sum challenge profile) — see [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get      # fetch prebuilt Mathlib oleans
lake build              # build the whole package (CI does exactly this)
```

Check a theorem's axiom footprint:

```lean
#print axioms SubsetSumL25.L2_5_prime_collision
#print axioms SubsetSumL25.erdos_dyadic_primes
#print axioms SubsetSumL25.Base_lem_A5
```

CI ([`.github/workflows/lean.yml`](.github/workflows/lean.yml)) builds the package on every push via `leanprover/lean-action` with the Mathlib cache.

## Next steps for a continuer

The conditional chain is banked through the combinatorial core; the open frontier is the algorithm layer and the remaining DS rungs (the ~18–35k-line "mountain", split in [`Statements/DS.lean`](SubsetSumL25/Statements/DS.lean)):

1. **DS-M2** — Lemma A2 key/class counts + the §5.4 trial count (Chebyshev).
2. **DS-M3/M4** — Lemma A5 Steps 1–6, consuming the proved Corollary D and the O3 prime-dispatch chain.
3. **DS-M5** — Corollary A6 coverage, Lemma A7 expected work, and the §5.8 assembly (five failure events + Markov + the 1/16 precision bound).
4. **V1 residuals** — item 2's continuous integral-form assembly, item 4's `rig_M` modulus bound, and the Lemma B1 transfer (ledger in [`Statements/JV1000.lean`](SubsetSumL25/Statements/JV1000.lean)).
5. **Procedures** — the `D_s` exec machinery, checksum tables, and alias extraction are named hypotheses; formalizing them is the path to an unconditional row.

The named-boundary pattern (procedure = named, arithmetic = proved) and the pin gotchas in [PROGRESS.md](PROGRESS.md) are the working contract for extending the ladder.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). Vendored third-party material keeps its upstream license — see [NOTICE](NOTICE.md).

---

[BigO-Hunter](https://github.com/BigO-Hunter) — tracking & packaging org for [Big O Speedrun](https://bigospeedrun.com) contributions · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io)
