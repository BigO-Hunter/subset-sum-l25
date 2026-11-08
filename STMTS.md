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
7. **Paper premise convention**: at lemma level, paper premises appear as named
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

# Base (a-kapila) combinatorial core — Lemmas 3.1–3.3 (B1)

Source of every quote: `a-kapila/maths-proofs` @ `44c34961`
(subset-sum/PROOF_0.4877.tex, sha256
`b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298`, local clone
`/Volumes/Substrate-1/bigo/subset-sum-base-src/`), §3 «An averaged
small-layer lemma». Statement-by-statement verification already recorded in
`/Volumes/Substrate-1/bigo/subset-sum-bridge/BRIDGE.md` appendix, row B1 —
verdict «matches». **Credit: the lemmas are Base's (paper-only); this package
formalizes them, it does not claim them.**

Context (PROOF_0.4877.tex §3): «Let w be integer weights on a finite index
set; equal weights are allowed.  For a finite index set V and j ≥ 0, put
Σ_j(V) = {w(T) : T ⊆ V, |T| = j}, a_j(V) = |Σ_j(V)|/C(|V|,j), and
Σ(V) = ⋃_j Σ_j(V), d(V) = |V| − log|Σ(V)|.»

## L3.1 — covering

> **Lemma 3.1 (covering).** Let 0 ≤ k ≤ t ≤ |V|, and let W be a uniform
> (t−k)-subset of V. Then a_t(V) ≤ E_W a_k(V∖W).

Proof shape (paper, verbatim): «For each x ∈ Σ_t(V), fix a t-set T_x ⊆ V with
w(T_x)=x.  Consider the pairs (x,W) with W ⊆ T_x and |W| = t−k.  The map
(x,W) ↦ (W, x−w(W)) is injective, because x = (x−w(W)) + w(W).  Its second
coordinate is w(T_x∖W) ∈ Σ_k(V∖W).  There are C(t,k)|Σ_t(V)| pairs, so
C(t,k)|Σ_t(V)| ≤ Σ_{W⊆V, |W|=t−k} |Σ_k(V∖W)|.  Divide by
C(|V|,t)C(t,k) = C(|V|,t−k)C(|V|−t+k,k).»

Lean: `SubsetSumL25.L3_1_covering` (Proofs/Layers.lean).

## L3.2 — sampling

> **Lemma 3.2 (sampling).** Let k ≤ s ≤ |V|, and let S be a uniform s-subset
> of V. Then E_S a_k(S) ≥ a_k(V).

Proof shape (paper, verbatim): «For each x ∈ Σ_k(V), fix a k-set K_x with
w(K_x)=x.  Then x ∈ Σ_k(S) whenever K_x ⊆ S.  This event has probability
C(|V|−k, s−k)/C(|V|,s) = C(s,k)/C(|V|,k).  Sum over x and divide by C(s,k).»

Lean: `SubsetSumL25.L3_2_sampling` (Proofs/Layers.lean).

## L3.3 — a good layer

> **Lemma 3.3 (a good layer).** Some t with 2t ≤ |V| has
> |Σ(V)| ≤ (|V|+1)|Σ_t(V)|.  In particular a_t(V) ≥ 2^{−d(V)}/(|V|+1).

Proof shape (paper, verbatim): «The |V|+1 layers cover Σ(V), so some layer j
has |Σ_j(V)| ≥ |Σ(V)|/(|V|+1).  Complementation gives Σ_{|V|−j}(V) =
w(V) − Σ_j(V), so we may take t = min(j, |V|−j).  Finally C(|V|,t) ≤ 2^{|V|}.»

Lean: `SubsetSumL25.L3_3_good_layer` (existence half) and
`SubsetSumL25.L3_3_good_layer_density` (the «in particular» clause).

## Translation choices (B1)

1. **Uniform-subset average = `Finset.expect` over `V.powersetCard m`.** The
   paper's «W a uniform (t−k)-subset of V» has no separate probability space:
   it is the average over all `(t−k)`-element subsets of the fixed ground set
   `V`. Modeled as `(V.powersetCard (t-k)).expect …`, the same house
   convention used for `uniformQSubsets` in L2.3. `V.powersetCard m` is
   nonempty under the stated size hypotheses, so no `0`-denominator arises.
2. **Weights are `c : Fin n → ℤ`** (the OpenAI-paper name kept from
   `Statements/Defs.lean`, where `subsum`/`support`/`deficiency` live), not a
   new `w` with a general index type. «equal weights are allowed» needs no
   hypothesis: `c` is an arbitrary function, so collisions are permitted.
3. **`Σ_j(V)` and `a_j(V)` are new definitions** (`Statements/LayerDefs.lean`):
   `layerSupport c V j = (V.powersetCard j).image (subsum c)` and
   `layerDensity c V j = |Σ_j(V)| / C(|V|,j)` as a division in `ℝ`. For
   `j > |V|` the layer is empty and `C(|V|,j) = 0`; the density is then the
   junk value `0`, which is why every lemma carries `j ≤ |V|` as a hypothesis.
4. **`|V∖W|` is `V \ W`** (Mathlib `Finset.sdiff`). From `W ∈ V.powersetCard
   (t−k)` one gets `W ⊆ V` and `|W| = t−k`, hence `(V \ W).card = |V| − t + k`
   — the paper's `|V| − t + k`. The lemmas do not need `∅`-conventions beyond
   `Finset`'s.
5. **`2^{−d(V)}` is real exponentiation** `(2:ℝ) ^ (-(deficiency c V))`
   (`Real.rpow`), and `deficiency` is `|V| − log₂|Σ(V)|` in `ℝ` — the paper's
   base-2 log. The identity used in the proof is the exact one
   `2^{−d(V)} = |Σ(V)|/2^{|V|}` (from `Real.rpow_sub` + `Real.rpow_logb` +
   `Real.rpow_natCast`); no inequality or approximation enters.
6. **Paper premise convention** (unchanged from the L2.5 cluster): paper
   premises are named hypotheses in Lean, never `axiom`s. Nothing here claims
   a board row; per BRIDGE.md the staged ladder is hypotheses-in-statements.
7. **M1 statements carry `sorry`** (placeholder proofs, reported in
   PROGRESS.md); M2/M3 replace them in `Proofs/Layers.lean`. All proved
   theorems must satisfy `#print axioms` = `[propext, Classical.choice,
   Quot.sound]`, no `native_decide`.
