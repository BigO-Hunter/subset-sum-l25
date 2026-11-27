/-
M1 (D_s): the alias-class dictionary of Base's Theorem A — verbatim quotes,
the proved-vs-named ledger, and the milestone ladder.  The statement-of-record
for everything proved is `Proofs/DS.lean`.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` (sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298),
§5 (Theorem A).  Rung mapping: the D_s closure consumes rungs
O5 (the checksum estimator, the «SumCheck» side: §5.2 Step 3's T-assembly and
the (C2)–(C7) constant ledger) and O7 (the alias extraction, the «AliasExt»
side: §5.2 Steps (a)–(g) + §5.6 coverage) — the ~18–35k «mountain» of the
ladder.

Verbatim (PROOF_0.4877.tex §5.1, Theorem A part 1):

    «Assume (LD). Let P be uniform among the primes of the interval, and let
    φ be arbitrary … Then, with probability 1 − o(1), the procedure does not
    fail and
        |Â_s − Σ_{I∈A_s(P)} χ(I)| ≤ 1/16   for every s.»

Verbatim (§5.3):

    «Lemma A1 (soundness). Every key inserted into D_s is an alias class of
    t_s.»
    «… if D_s contains every alias class of t_s, then the exact output sum
    equals Σ_{I∈A_s(P)} χ(I).»

Verbatim (§5.6):

    «Corollary A6. Assume (LD), E_3, and the event of Lemma A4. Then, except
    with probability o(1), every alias class of every target is in its
    dictionary at the end of Step 4.»

Proved-vs-named ledger (see Proofs/DS.lean):
  PROVED  (5.1) the signed-weight identities; the class machinery (members
          share (c, b)-sums; every I lies in exactly one class); (5.2) the
          class-sum identity (phases multiplicative over disjoint unions);
          Lemma A1 (soundness — arithmetic); **the D_s closure corollary**
          (sound + complete ⇒ the exact output sum equals Σ_{I∈A_s(P)} χ(I))
          — the dictionary's content, with the exec machinery abstracted to
          a Finset of key-triples (the D7 boundary: balanced trees, sorting
          and op-counting stay named).
  NAMED   Lemma A2 (key/class counts), §5.4 trial count (Chebyshev), §5.5
          mod-P reduction, Lemma A5 (one trial — Steps 1–6, consuming
          Corollary D, (F4) = the O3 prime-dispatch, and the good-layer
          machinery), Corollary A6 (coverage union bound), Lemma A7
          (expected work — the (C2)–(C7) ledger), and the §5.8 assembly
          (five failure events + Markov + the 1/16 precision bound).

MILESTONE LADDER (each with statement + proof + receipts; the ~18–35k
mountain split):
  DS-M1 (LANDED)  defs + (5.1) + class machinery + (5.2) + Lemma A1 + the
                  closure corollary.  Statement work + core arithmetic.
  DS-M2           Lemma A2 (key/class counts) + the §5.4 trial count
                  (T-assembly from n² deficiency draws; mathlib Chebyshev).
  DS-M3           Lemma A5 Steps 1–3 (half-block sampling; signs fixed;
                  the Corollary-D consumption E_S a_k ≥ 2^{-g_M}/(v+1) —
                  consumes our proved CorD machinery).
  DS-M4           Lemma A5 Steps 4–5 (small-prime residues — consumes
                  (F4), i.e. our O3 prime-dispatch chain; the Step-5
                  recovery walk).
  DS-M5           Lemma A5 Step 6 + Corollary A6 (the coverage union bound
                  e^{-n} = o(1)).
  DS-M6           Lemma A7 (expected work — the seven-step cost ledger with
                  (C2)–(C7); the v2-snapshot op-bound style applies).
  DS-M7           Theorem A assembly (§5.8: five failure events, Markov on
                  the cap, the 1/16 finite-precision bound).

Credit chain: Base → Bills → us.  The D_s dictionary is Base's construction;
this file formalizes its mathematical core with attribution.
-/
import Mathlib
