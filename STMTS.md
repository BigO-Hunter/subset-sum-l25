# STMTS — verbatim statements + translation notes for the L2.5 cluster

Source of every quote: OpenAI preprint «Subset-Sum in Time O(2^0.49n)» (openai/math
@ `adc7f124`, 2026-10-04), local LaTeX at
`/Volumes/Substrate-1/bigo/subset-sum-subclassic/openai-math/preprints/Subset-Sum-in-Time-2-power-0-49n-October-4-2026/build/`
(`sections/setup.tex`, `sections/aliases.tex`). Paper numbering: L2.1 = `lem:isolation`,
L2.2 = `lem:deficiency`, L2.3 = `lem:half-variance`, L2.5 = `lem:prime-collision`,
L5.2 = `lem:sparse-distinction`. Context line (setup.tex): «All logarithms are to
base 2, except for ln.  Write [n]={1,…,n}, and for weights v₁,…,vₙ write
v(I)=∑_{i∈I}v_i for I⊆[n].  Empty sums are zero.»

## L2.1 — Isolation (setup.tex, after eq. (1) `eq:transformed`)

> **Lemma 2.1 (Isolation).** For every choice of the tie weights, there is a
> subset I⊆[n] with a(I)=t if and only if there are s∈{0,…,nN₀} and I⊆[n] with
> c(I)=t_s. If the original instance has a solution, then with probability at
> least 11/12 at least one transformed target t_s has exactly one representing
> subset.

Context (eq. (1)): choose a power of two N₀ with 12n ≤ N₀ < 24n; independent
uniform integers u_i ∈ {1,…,N₀}; C = 1+nN₀, c_i = C·a_i + u_i, t_s = C·t+s
(0 ≤ s ≤ nN₀). Lean: `SubsetSumL25.L2_1_isolation` (first sentence, all u),
`SubsetSumL25.L2_1_isolation_prob` (second sentence).

## L2.2 — Properties of deficiency (setup.tex, eq. (2))

> **Lemma 2.2 (Properties of deficiency).** For arbitrary fixed integer weights,
> d(∅)=0 and d(V)≥0. For i∉V,
>   0 ≤ d(V∪{i}) − d(V) ≤ 1.
> For disjoint U,V⊆[n],
>   d(U∪V) ≥ d(U)+d(V).
> If V,V′ have equal size and differ by exchanging one index, then
> |d(V)−d(V′)| ≤ 1.

Context (eq. (2)): Σ(V) = {c(I) : I ⊆ V}, d(V) = |V| − log|Σ(V)|. Lean:
`L2_2_deficiency_empty/nonneg/insert/superadd/exchange` (exchange stated as
V = U∪{i}, V′ = U∪{j}, i,j ∉ U, i ≠ j — the paper's own proof shape: «in an
exchange write V=U∪{i} and V′=U∪{j}»).

## L2.3 — Random restrictions (setup.tex)

> **Lemma 2.3 (Random restrictions).** Let V_q be a uniformly random q-element
> subset of [n], for 0 ≤ q ≤ n. Then
>   Var d(V_q) ≤ q.
> Moreover, 𝔼 d(V_q) is nondecreasing in q.

Lean: `L2_3_halfVariance` (variance in the elementary form
𝔼[(d−𝔼d)²] ≤ q over `uniformQSubsets n q`), `L2_3_expectation_mono`.

## L2.5 — Random-prime collisions (setup.tex)

> **Lemma 2.5 (Random-prime collisions).** There are absolute constants K and
> L_* such that the following holds. For an integer L ≥ L_*, let p be uniform
> among the primes in [2^L, 2^{L+1}). If D is a nonzero integer with |D| < 2^B,
> where B ≥ 1, then
>   Pr{D ≡ 0 (mod p)} ≤ K·B·L·2^{−L}.
> The same bound applies to the collision of two fixed unequal integers whose
> difference has absolute value less than 2^B.

Lean: `L2_5_prime_collision`, `L2_5_prime_collision_two`.

## L5.2 — Sparse distinctions (aliases.tex, eq. (14))

> **Lemma 5.2 (Sparse distinctions).** With probability 1−o(1) over P, the
> following implication holds simultaneously for every v∈{−1,0,1}^n with at
> most m nonzero coordinates:
>   ∑ᵢ vᵢcᵢ ≠ 0  ⟹  ∑ᵢ vᵢcᵢ ≢ 0 (mod P).                                (14)
> The error is uniform under (16).

Lean: `L5_2_sparse_distinctions`.

---

# Translation notes — what a reviewer should check first

1. **L2.5's PNT premise is a named hypothesis, not proved** (`hcount`). The
   paper's proof opens «The prime number theorem gives at least c₀·2^L/L primes
   in the specified interval … Rosser and Schoenfeld [Corollary 3]». Mathlib
   **d13f23b does not contain the PNT** (checked: `Mathlib/NumberTheory/
   PrimeCounting.lean` has only monotonicity/surjectivity; `Chebyshev.lean` has
   explicit bounds `Chebyshev.PrimeCounting.pi_ge` ≈ (ln2)x/lnx and
   `pi_le_log4_mul_div` ≈ (2ln2)x/lnx — constants that annihilate in the
   interval difference π(2^{L+1})−π(2^L)). So `hcount : ∀ L ≥ L₀, c₀·2^L/L ≤
   #(primesInterval L)` carries the paper's own external input. Everything
   after it is proved: distinct-prime-divisor count < B, union-ratio arithmetic,
   **K is explicit: K = c₀⁻¹, L\* = L₀** — the «absolute constants» existential
   is discharged inside the proof. `hpos : 0 < #(primesInterval L)` is
   well-formedness of the uniform distribution (needed since in Lean ℝ `0/0=0`
   would make the claim vacuous). In a later stage `hcount` is either (a)
   discharged by formalizing Rosser–Schoenfeld/PNT-strength input, or (b)
   carried as a documented premise of the conditional row, exactly as rev8g
   Theorem 1 conditions on «the non-numerical lemmas of the OpenAI paper».
2. **Probability = uniform count fraction.** All `Pr{·}` are `#{u ∈ univ | P u}
   / #univ` (L2.1 over `Fin n → Fin N₀`; L2.5/L5.2 over `primesInterval L`),
   stated as rational/real inequalities. No measure theory is used.
3. **Tie weights {1,…,N₀} ≅ `Fin N₀`.** The +1 shift is irrelevant to both L2.1
   parts (uniformity; «their two minima coincide for at most one value of u_i»).
4. **Power-of-two N₀ dropped.** Used only for bit-length accounting downstream;
   neither L2.1 part needs it. Kept: 12n ≤ N₀ (gives n/N₀ ≤ 1/12).
5. **Deficiency is real-valued** via `Real.log (|#Σ(V)|)/Real.log 2`; |Σ(V)| ≥ 1
   always (∅ ⊆ V, empty sum 0), so no log issues.
6. **L5.2's «1−o(1)» made explicit**: failure probability ≤
   K·S(n,m)·B·L·2^{−L} with S(n,m) = ∑_{j≤m} C(n,j)·2^j (`sparseCount`) —
   the paper's own union-bound shape («There are at most ∑_{j=0}^m C(n,j) 2^j
   such vectors»; «Every nonzero integer ∑ᵢ vᵢcᵢ has O(b+log n) bits» →
   hypothesis `hB`). The o(1) is the external ratio S(n,m)·poly/log-guard → 0
   under the bit-guard (16), outside the lemma. Same `hcount`/`hpos` premises
   as L2.5. P is uniform over a dyadic prime interval — the §5 application
   draws P from a specific range; the lemma is stated for generic L (the
   application fixes L).
7. **L5.2 statement fix at M5b (important).** The M1 statement bounded the
   COUNT `#(badSparsePrimes L)`; the paper (and note 6 above) bound the
   failure PROBABILITY. The count form is degenerate — it is provable only
   via `L* ≥ B`, where every interval prime exceeds every candidate sum and
   the failure set is empty; it asserts nothing in the interesting regime.
   The theorem now carries the division by `#(primesInterval L)`:
   `#(badSparsePrimes L) / #(primesInterval L) ≤ K·S(n,m)·B·L·2^{−L}`.
   Also note the translation choice for the candidate set: `Fin n → ℤ` is
   infinite (`Fintype ℤ` does not exist), so the paper's «∑_{j=0}^m C(n,j)2^j
   such vectors» is encoded as the explicit Finset `sparseAll n m` built from
   (support, sign pattern) — the counting `#(sparseAll n m) ≤ sparseCount n m`
   is PROVED (`sparseAll_card_le`), not assumed, so no `S` parameter appears
   in the theorem signature (option (b) of the scoping round was executed
   internally: the explicit `S` is `sparseAll`, with its cardinality bound
   discharged in-proof).
8. **Paper premise convention**: at lemma level, paper premises appear as named
   hypotheses (documented above), never as Lean `axiom`s. Nothing in this
   package claims a board row; per BRIDGE.md milestone 1, hypotheses-in-
   statements is the staged-ladder architecture, and rev8g's Theorem 1 is
   conditional on exactly these lemmas.
8. **M1 statements carry `sorry`** (placeholder proofs, precisely reported in
   the campaign README/report); M2+ replaces them in `Proofs/` files. All
   proved theorems must satisfy `#print axioms` = `[propext, Classical.choice,
   Quot.sound]`.

# Provenance for the conditional rows

BRIDGE.md appendix (2026-11-07): Base primary source verified
(`../subset-sum-base-src/`, a-kapila/maths-proofs@44c34961, PROOF_0.4877.tex
sha256-verified). Boundary relevant here: Base's B3 invokes OpenAI L2.5
(«(F4)») as read-only premise — formalizing L2.5 (this package, M2) upgrades
that link from paper-citation to kernel-checked statement; the remaining
B-row/B4/B5 content stays outside this cluster.
