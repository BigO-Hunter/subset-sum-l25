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
7. **Status (M1–M3 complete, 2026-11-08):** all six B1 declarations are
   proved — `L3_1_covering`, `L3_2_sampling`, `L3_3_good_layer`,
   `L3_3_good_layer_density` plus the counted forms `L3_1_covering_card`,
   `L3_2_sampling_card` and the helpers `layerSupport_compl`,
   `twoPow_neg_deficiency`. `#print axioms` = `[propext, Classical.choice,
   Quot.sound]` for every one; no `native_decide`, no new axioms. Proofs live
   in `Proofs/Layers.lean` (statement-of-record; the `Statements` module keeps
   only the quotes and pointers).

# Base (a-kapila) Corollary D — averaged small layer (B2)

Source of every quote: `a-kapila/maths-proofs` @ `44c34961`,
`subset-sum/PROOF_0.4877.tex` §3 (sha256
`b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298`), immediately
after Lemma 3.3. Cross-checked against `subset-sum-bridge/BRIDGE.md` appendix
row B2, verdict «matches», **with the one correction recorded there**: the old
condensation said «uniform half S», which is imprecise — the paper says
«Let S be a uniform σ-subset and V a uniform v-subset of M», and σ = m/2 holds
only in the application (§2.2, sizes S1), never in the corollary.
**Credit: the corollary is Base's; this package formalizes it.**

## Corollary D — verbatim

> **Corollary D (averaged small layer).** Let M be a finite index set with
> integer weights. Let k, σ, v be integers with 2k ≤ σ, 2σ ≤ v + 2k, v ≤ |M|
> and C(σ,k)C(v,k) ≤ 2^v. Let S be a uniform σ-subset and V a uniform v-subset
> of M. Then
>   E_S a_k(S) ≥ (E_V 2^{−d(V)})/(v+1).

Lean: `SubsetSumL25.Base_cor_D` (Proofs/CorD.lean), written
`E_V (2^{−d(V)}/(v+1)) ≤ E_S a_k(S)`. Two mechanical differences from the
displayed formula, both exact: the paper reads right-to-left (its `≥`), and its
`\frac{E_V 2^{−d(V)}}{v+1}` divides *after* the expectation while the Lean form
divides *inside* it — equal because `v+1` is constant (linearity of
`Finset.expect`). No inequality is weakened.

## Verbatim proof, and how each step maps

> The hypotheses give k ≤ σ ≤ v. Fix a v-set V ⊆ M, and let S_V be a uniform
> σ-subset of V. We show that 2^{−d(V)}/(v+1) ≤ E a_k(S_V). Take t from
> Lemma 3.3.

Per-`V` claim → `Base_cor_D_case_ge` (t ≥ k) and `Base_cor_D_case_lt` (t < k).

> **Case t ≥ k.** Lemma 3.1 gives a_t(V) ≤ E_W a_k(V∖W), where
> |V∖W| = v − t + k ≥ v/2 + k ≥ σ. Lemma 3.2 for V ∖ W and s = σ gives
> a_k(V∖W) ≤ E a_k(S') for a uniform σ-subset S' of V∖W. When W is uniform,
> S' is a uniform σ-subset of V. Hence 2^{−d(V)}/(v+1) ≤ a_t(V) ≤ E a_k(S_V).

`L3_1_covering` + `L3_2_sampling` (both from the B1 rung) + the disjoint
two-level averaging `expect_powersetCard_sdiff`. The cardinal inequality
`2^{−d(V)}/(v+1) ≤ a_t(V)` is `layerDensity_ge_of_card` (extracted from the
`L3_3_good_layer_density` assembly so the *same* `t` feeds both branches).

> **Case t < k.** Then t < k ≤ v/2, so |Σ_t(V)| ≤ C(v,t) ≤ C(v,k). Lemma 3.3
> gives 2^{v−d(V)} ≤ (v+1)C(v,k). With the hypothesis,
> 2^{−d(V)}/(v+1) ≤ C(v,k)2^{−v} ≤ 1/C(σ,k). Every σ-set S has
> a_k(S) ≥ 1/C(σ,k), because Σ_k(S) is not empty.

`one_div_choose_le_layerDensity` (the floor: `Σ_k(S) ≠ ∅` ⟹ `|Σ_k(S)| ≥ 1`) plus
`Nat.choose_le_choose` for `C(v,t) ≤ C(v,k)`, and the hypothesis
`C(σ,k)C(v,k) ≤ 2^v` used exactly here (`C(v,k)/2^v ≤ 1/C(σ,k)`).

> Finally average over V. A uniform σ-subset of a uniform v-subset of M is a
> uniform σ-subset of M.

`expect_powersetCard_powersetCard`.

## Translation choices (B2)

1. **Two separate averaging spaces, not one uniform measure.** «S uniform
  σ-subset of M» and «V uniform v-subset of M» are independent averages, modeled
  as `Finset.expect` over `M.powersetCard σ` and `M.powersetCard v`. The proof's
  inner object `S_V` («a uniform σ-subset of V») is `V.powersetCard σ`, i.e. an
  average nested inside the `V`-average — no coupling measure is introduced.
2. **The σ-subset correction, made explicit.** No `σ = m/2`, no `σ = v/2`, no
  «half» assumption anywhere: `σ` is an independent parameter constrained only
  by `2k ≤ σ` and `2σ ≤ v + 2k`. What the paper *does* derive is `k ≤ σ ≤ v`;
  that derivation is not a hypothesis in Lean, it stays inside the proof
  (`2σ ≤ v + 2k` with `2k ≤ σ` gives `σ ≤ v`), so the statement does not
  silently assume it.
3. **`v ≤ |M|` is `v ≤ M.card`** and does double duty: it is the paper's
  hypothesis *and* the nonemptiness certificate for `M.powersetCard v`. This is
  the rung's known risk — `Finset.expect` over an empty finset is `0`, so a
  weakened size hypothesis would make the average degenerate silently instead of
  failing loudly. `σ ≤ M.card` is derived (`σ ≤ v ≤ M.card`), and the nested
  spaces carry their own certificates: `expect_powersetCard_powersetCard` takes
  `p ≤ M.card`, `expect_powersetCard_sdiff` takes `p + q ≤ V.card`.
4. **`C` is `Nat.choose`** and `C(σ,k)C(v,k) ≤ 2^v` is a `ℕ` hypothesis, kept in
  `ℕ` (not cast to `ℝ`) so the branch that uses it can apply `Nat.choose_pos`
  and cast exactly once.
5. **The `t` is Lemma 3.3's `t`, not a fresh one.** `L3_3_good_layer` returns
  `t` with `2t ≤ |V|` and `|Σ(V)| ≤ (|V|+1)|Σ_t(V)|`; the density bound for that
  *same* `t` is a separate lemma (`layerDensity_ge_of_card`), so the two branches
  (`t ≥ k`, `t < k`) dispatch on one `t` as the paper does.
6. **Paper premise convention** unchanged: paper premises are named hypotheses,
  never `axiom`s. Nothing here claims a board row.
7. **Scaffolding is labelled.** `one_div_choose_le_layerDensity`,
  `expect_powersetCard_powersetCard` and `expect_powersetCard_sdiff` are not
  paper lemmas — the paper does those counts inline. They are stated separately
  (M1) and proved (M2/M3) so each count is auditable on its own.

# Base (a-kapila) Lemma A5 «one trial» + Corollary A6 (B3)

Source of every quote: `a-kapila/maths-proofs` @ `44c34961`,
`subset-sum/PROOF_0.4877.tex` §5.4–§5.6 (sha256
`b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298`). Cross-checked
against `subset-sum-bridge/BRIDGE.md` appendix row B3 (verdict «matches»: the
bound `≥ 2^{−g_M}·n^{−6}` under (LD)+E_3+A4 via the second prime `P′` + (F4),
with `2^{−g_M} := E_V 2^{−d(V)}` and Corollary A6 requiring `T ≥ n⁷2^{g_M}`).
**Credit: the lemma is Base's; this package formalizes it.**

## Lemma A5 — verbatim (§5.6)

> **Lemma A5 (one trial).** Assume (LD), E_3, and the event of Lemma A4. Fix s,
> an alias I ∈ A_s(P) with carry q, and one trial for (s, q). After the trial,
> D_s contains the key of the class of I with probability at least 2^{−g_M}n^{−6}.
> The threshold for n does not depend on I, s, P or M.

## Corollary A6 — verbatim (§5.6)

> **Corollary A6.** Assume (LD), E_3, and the event of Lemma A4. Then, except
> with probability o(1), every alias class of every target is in its dictionary
> at the end of Step 4.

## What A5 quantifies over, and what that forces

A5's subject is the *algorithm*: `D_s` (a dictionary), keys, classes
`C(κ_L,κ_R,Z)`, records, the trial procedure, `F`, `P′`, `j′`. None of that is
in this package, and inventing it would be a different (much larger) job than a
lemma rung. So, as with every rung of this ladder, **the algorithmic steps
become named hypotheses and the mathematics is proved**:

| Paper step | Lean | Kind |
|---|---|---|
| Step 1 (`F` uniform ⟹ `S` uniform; `|S|=σ` w.p. `C(m,σ)2^{−m} ≥ 1/(m+1)`) | `choose_div_two_pow_ge_inv`, `powerset_expect_ite_card` | PROVED |
| Step 2 (`c^F_i = ±c_i` on `S`, so `B_S ≥ a_k(S;c^I)C(σ,k)` on good `S`) | hypothesis `hgood` of `good_hit_expect_ge` | deterministic, named |
| Step 3 (bad fraction `2^{−δn}`; `E_S[1_good B_S/C(σ,k)] ≥ 2^{−g_M}/(v+1) − 2^{−δn}`) | `expect_bad_indicator_ge` + `good_hit_expect_ge` | PROVED |
| Step 4 ((F4) per pair; `E Σz² ≤ B + K₀n²B²2^{−γm}`; C–S occupancy; `j′` hit) | `expect_dvd_eq_badPrimes`, `pair_collision_le`, `collisionPairs_expect_le`, `occupied_ge_card_sub_collisions`, `hit_prob_eq_occupied` | PROVED (consumes `L2_5_prime_collision`) |
| Step 5 («a hit is recovered»: hit residue ⟹ key inserted) | hypothesis `hstep5` of `Base_lem_A5` | deterministic, named |
| Step 6 (product chain; `≥ 2^{−g_M}n^{−6}` for large `n`) | `lem_A5_product`, `lem_A5_threshold` | PROVED |
| Cor A6 (`(1−p)^T ≤ e^{−pT}`; union bound) | `cor_A6_per_alias` | PROVED |

## Translation choices (B3)

1. **`g_M` is a definition, not a numeral.** §5.4 verbatim: «g_M = −log E_V
   2^{−d(V)}», all paper logs base 2, so `gM c M v = −Real.logb 2 (E_V
   2^{−d(V)})`. The BRIDGE row's `2^{−g_M} := E_V 2^{−d(V)}` is then the
   theorem `two_pow_neg_gM`, not a definitional coincidence — and it carries the
   hypothesis `v ≤ |M|`, because `Finset.expect` of an empty finset is `0` and
   `logb 2 0` would make `gM` junk. **Nonemptiness is stated, never assumed.**
2. **The second-prime quantifiers stay where the paper puts them.** `P′` is
   uniform on `primesInterval ⌊γm⌋` (`primesInterval L` is the paper's
   `[2^L, 2^{L+1})` filtered to primes), and `j′` is uniform on `[0,P′)`
   (`Finset.range p`). The (F4) input is consumed once, in
   `pair_collision_le`, as `L2_5_prime_collision`'s conclusion — that is the
   exact place the paper writes «(F4) with L′ = ⌊γm⌋».
3. **(LD), E_3, A4 enter as the numeric bounds they are used for**, never as
   opaque events: Step 3 needs A3(4)'s `2^{−δn} ≤ 2^{−g_M}/(2(v+1))` (hypothesis
   `hδ`) and the A4 bad fraction (hypothesis `hbad`, stated as a count bound
   over `M.powersetCard σ`); Cor A6 needs A3(1)'s `2^{ĥF} ≥ 2^{g_M}`, which
   appears as `Tp ≥ 1` after multiplying `T ≥ n⁷2^{g_M}` by `p = 2^{−g_M}n^{−6}`.
4. **The second moment is stated in collision form.** The paper's `Σ_y z_y²`
   equals `|W_S| + #{ordered colliding pairs}`; `collisionPairs W p` is that
   count, so `collisionPairs_expect_le` is literally the paper's inequality
   without introducing residue-class sums over an infinite range.
5. **`B_S` is a function `ℕ`-valued on subsets** (`B : Finset (Fin n) → ℕ`), not
   a set `W_S`: only its cardinality is used, and Step 2 supplies the lower
   bound while `B_S ≤ C(σ,k)` is the trivial upper bound the paper also uses.
6. **«The threshold for n does not depend on I, s, P or M»** is formalized as
   `lem_A5_threshold`: an *explicit* `N` with `m, v ≤ N` and `128K₀ ≤ N²` — no
   quantifier over `I, s, P, M` appears, which is the content of that remark.
7. **Paper premise convention** unchanged: named hypotheses, never `axiom`s;
   nothing here claims a board row.

## B3 status (2026-11-08, complete)

All 14 declarations of the B3 lane are PROVED (`Proofs/A5.lean` is the
statement-of-record for every one; `Statements/A5.lean` is a pointer file).
Receipts: `#print axioms` = `[propext, Classical.choice, Quot.sound]` for all 14,
freshly measured. The two statement corrections recorded above (the
middle-layer binomial bound, and `σ ≤ |M|` for `good_hit_expect_ge`) stand as
corrected statements of the paper's intent; `collisionPairs_expect_le` gained
`0 ≤ K₀` for the same reason (the diagonal pairs' zero must be bounded).

# B4 — Base Theorem B region analysis: entry decision + statements

Source of every quote: `a-kapila/maths-proofs` @ `44c34961`, §6.1 (regions,
certificate data, Prop B) and §6.3 (Lemma B2).  Cross-checked against
`subset-sum-bridge/BRIDGE.md` row B4 («matches»).  **Credit chain: Base
(regions, certificates, Lemma B2) → Bills (region-predicate template,
`yannouli-ss/verification/lean/Verification/Regions.lean`) → this package
(formalization).**

## ENTRY DECISION — re-express locally (option ii), do not import Bills' modules

Examined at `subset-sum-subclassic/yannouli-ss/verification/lean/`:
`Verification/Regions.lean` (64 lines), `Verification/RowMargins.lean` (99
lines).  Reasons for (ii):

1. **Pin mismatch.** Bills' `lean-toolchain` is `v4.24.0`; our lane pins
   `v4.34.1` + Mathlib `d13f23b` (the subset-sum challenge profile).  Their
   `lakefile.toml` also requires an external git dep
   (`subset_sum_bound` @ bed8e18f) whose `SubsetSum.Asymptotics` defines their
   constants (`tau`, `eta`, `gammaB`, …).  Importing = vendoring two projects +
   toolchain reconciliation + porting: a dependency-management job, not a proof
   obligation, and it would put a foreign dep in the lane's lakefile.
2. **Their certificate layer is concrete, ours is abstract by contract.**
   Bills' `RowMargins.lean` runs `decide +kernel` over their own 43-filter
   `certificates : List RawCertificate` (their `DataBridge`/`Concrete` modules).
   BRIDGE's B4 scope here is «structure + domination with the certificate rows
   as data»; the 430 rows are separately certified (Appendix C), so a
   kernel-decide layer would re-verify what we are told not to re-verify.
3. **Their `firstBoundary v` is a Bills-specific refinement.** Bills sets the
   first boundary to `budget` (not `gammaB`) for filter 3; Base §6.1 has the
   uniform `b₀ = 1` for every filter.  We formalize Base's statement; the
   deviation is noted so a future port can add it as a one-line variant.
4. **The template is small.** 64 lines carry the whole reusable shape: the
   10-band list, the `by_cases` existence ladder, the `fin_cases`-disjointness.
   Re-expression in house style is cheaper than vendoring and keeps the credit
   chain explicit.  What was *taken from* the template: the band list as a
   literal table, the existence-by-ladder structure, and the
   existence/disjoint/uniqueness trio of lemmas.

## Statements and their sources

* `bandUpper` — §6.1's b₀..b₈ as a literal table (identical to Bills' list).
* `inRegion` — §6.1 verbatim: ρ₀ is `W ≤ Γ` (no lower bound — Base's own
  definition, so the partition is total without a `0 < W` side condition, and
  *unlike* the natural-but-wrong `(0,Γ]` reading); ρᵢ (1 ≤ i ≤ 9) is
  `Γb_{i−1} < W ≤ Γbᵢ` with ρ₉'s upper bound absent (b₉ = ∞).  `inRegion` is
  defined for all `ℕ`, but only `i ≤ 9` are regions — the lemmas carry `i ≤ 9`.
* `region_existence` / `region_disjoint` / `region_unique` — Bills' trio,
  re-derived for Base's predicate (needs `Γ > 0` so the bounds order correctly).
* `row_errors_le_six_eps` — the a_Γ ≤ 3/4 guard (BRIDGE row B4's «referee-
  extracted»): §6.3's six row errors 3ε, 4ε, 6ε, (4a_Γ+3)ε, 4ε, 4ε are all ≤ 6ε
  exactly because `(4a_Γ+3) ≤ 6 ⟺ a_Γ ≤ 3/4`.
* `z_dot_Gbar_ge` — Lemma B2's display `z·Ḡ ≥ z₀G^π₀ − 6εΣz` in abstract
  indexed form (row `t₀` = the vector's row 0).
* `lem_B2_region_zero` / `lem_B2_region_band` — the two dispatch cases,
  hypotheses verbatim from the proof text.
* `lem_B2_domination` — the verbatim conclusion
  `−α_πU_{v,π} ≤ −Δ + z·Ḡ + 6εΣ_t z_t`, dispatch against the display.

**Theorem B itself is out of this package's scope**: it is an algorithm
statement (FAIL / estimates / error / word count) with the checksum procedure
of §6.2 inside — the same boundary as Lemma A5's `D_s`, and BRIDGE's B4 row
marks the domination argument as the formalizable content.  Prop B's 430
integral bounds are separately certified and are *not* restated here (they
would be data, and re-verification is explicitly out of scope).

**Empty-expect audit:** B4 contains no `Finset.expect` — every hypothesis is
pointwise and every average enters as an abstract parameter (`zGbar`).  There
is no silent-`0` degeneracy class in this rung.

`sorry` ledger at M1: 7 (region_existence, region_disjoint,
row_errors_le_six_eps, z_dot_Gbar_ge, lem_B2_region_zero, lem_B2_region_band,
lem_B2_domination); `region_unique` is already proved from the first two.

# B5 — preliminary search (Prop P) + cost accounting: entry + statements

Source of every quote: `a-kapila/maths-proofs` @ `44c34961`, §4 (Prop P, (LD)),
§5.2 (Thm A part 2), §5.7 (Lemma A7), §5.8. Cross-checked against BRIDGE row B5
(«matches»). **Credit: Base.**

## Proved-vs-named ledger (the A5 pattern)

| Paper piece | Lean | Kind |
|---|---|---|
| Chebyshev over the split side («Var d(U) ≤ n, and Chebyshev's inequality gives …») | `chebyshev_fraction_le` | PROVED (finite-space Chebyshev; `s.Nonempty` stated) |
| The `4/(ζ²n)` instantiation («n/(ζn/2)² = 4/(ζ²n)») | `prop_p_chebyshev` | PROVED; variance input `Var d(U) ≤ n` = OpenAI L2.3's first clause, named hypothesis — the `hcount` cousin of the L2.5 lane |
| Cap fitting («log\|Σ(U)\| = \|U\| − d(U) ≤ n/2 + ½ − (½−τ₀+ζ/2)n < τ₀n for n > 1/ζ») | `cap_fit_lt` | PROVED (linear arithmetic; `1 < ζn`) |
| «returns CONTINUE with probability O(1/n)» | `continue_prob_le` | PROVED (explicit `4/(ζ²n)`; the O(·) is the asymptotic reading) |
| Thm A part 2 («Part 2 holds by Section 5.2»; op bound `2^{τ₀n+2n^{0.7}}poly`) | `prop_p_op_absorb` | PROVED (the absorption `2^{τ₀n} ≤ 2^{τ₀n+2n^{0.7}}`); the procedure's own op counts are the algorithm, named |
| Lemma A7 («Every item is at most (b+2)2^{(τ₀−ε₀+ζ)n+O(n^{0.6})}»; 7 items) | `a7_envelope` | PROVED (7 items ≤ (b+2)2^K and `5 ≤ b` ⟹ total ≤ (b+2)2^K — the paper absorbs the 7 into the constant); the seven per-item analyses ((C2)–(C7), Lemma A3(2)–(4), (F4)) are item-level hypotheses |
| Prop P correctness («returns the correct decision or CONTINUE»), Lemma 2.3 itself, Lemma A7's per-item exponents | — | algorithm/external-input boundary, named |

**Empty-expect audit:** `chebyshev_fraction_le` and `continue_prob_le` divide by
`#s` and carry `s.Nonempty` explicitly; no other statement touches
`Finset.expect`.  No silent-`0` degeneracy class.

# O8 — Base §5.2 word-RAM accounting: statements + proved-vs-named ledger

Source of every quote: `a-kapila/maths-proofs` @ `44c34961`,
`subset-sum/PROOF_0.4877.tex` §5.1 (Thm A part 2), §5.2 (Steps 3 and 6, the
closing accounting paragraph), §5.8 (bullet 5); sha256 re-verified this session
(`b397531c…`). Cross-checked against BRIDGE appendix rows O8 («paper-only») and
B5. **Credit: the accounting is Base's; this package formalizes it.**

**Boundary (D7 note):** every O8 statement counts *word operations* /
*elementary steps* in Base's OWN counters. The bit-cost → Light-step
translation is D7, assigned to L5 — it is deliberately not imported, exactly as
the APSP lane's FFT contract is stated over its own counters.

## Verbatim anchors

> (§5.1, Thm A part 2) On every execution the procedure uses at most
> 2^{τ₀n+2n^{0.7}} poly(n+b+2) word operations.

> (§5.2 Step 6) Count the elementary steps of Steps 1–5: subsets enumerated,
> merge operations, masks listed, keys sorted, records formed, records
> visited, members expanded, dictionary operations, terms summed, and trial
> divisions. Return FAIL as soon as the count would exceed
> 2^{⌈τ₀n⌉+⌈n^{0.7}⌉}. Also return FAIL if a bounded sampler fails.

> (§5.2, closing) Each step costs poly(n+b) word operations. Keys have
> O(b+log n) bits, masks have m bits, and the dictionaries are balanced search
> trees. The finite-precision sums use n² fractional bits (Section 6.2). With
> the cap, this proves part 2 of Theorem A.

> (§5.2 Step 3) … T = n⁷2^{e_n}⌈1/Ŝ⌉ … where e_n is an integer with
> 2n^{0.6} ≤ e_n ≤ 2n^{0.6}+1. Then n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂}.
> (F̂ = log(1/Ŝ) + e_n, Ŝ = (1/n²)∑_{j≤n²} 2^{−d(V_j)})

> (§5.8, bullet 5) A bounded sampler fails. A capped execution makes at most
> 2^{O(n)} draws, so this has probability 2^{O(n)}(2^{−n³}+e^{−c₀n²}) = o(1).

## Proved-vs-named ledger (the B4/B5 pattern)

| Paper piece | Lean | Kind |
|---|---|---|
| Step 6 cap `2^{⌈τ₀n⌉+⌈n^{0.7}⌉}` | `o8Cap` | definition (ℝ; `noncomputable`) |
| Cap fits part 2's budget (`⌈x⌉ < x+1` twice, absorbed by `2n^{0.7}`) | `o8_cap_absorb` | PROVED; hypothesis `2 ≤ n^{0.7}` = the paper's «sufficiently large n» made explicit (n ≥ 2^{10/7}; below it the absorption is genuinely false — n = 1/2 gives cap 2² > 2^{1.46}) |
| Ten counted categories within a uniform `C` | `o8_cap_envelope` | PROVED (`∑ ≤ 10·C`); the ten per-category analyses are the algorithm, named |
| Part 2's display, `poly(n+b+2)` slot = named `P` | `o8_time_bound` | PROVED skeleton (same `2 ≤ n^{0.7}` via `o8_cap_absorb`): ten categories ≤ `cap·P` ⟹ total ≤ `16·P·2^{τ₀n+2n^{0.7}}` (16 = 2⁴ absorbs the ten) |
| Step 3 trial count `n⁷2^{F̂} ≤ T ≤ 2n⁷2^{F̂}` | `o8_trial_count_bound` | PROVED; needs only `0 < Ŝ ≤ 1` (the `e_n` integer range is Lemma A3's input, not this bound's — noted in the docstring); the merge procedure of Prop 2.4 and the `V_j` draws are the algorithm, named |
| «Halts every execution» | `o8_trials_le_cap` | PROVED checkable core: per-trial ≥ 1 counted step (named data `S`) + prefix ≤ cap ⟹ `K ≤ cap` — no execution passes `cap` elementary steps; the FAIL rule itself is the named mechanism |
| «At most 2^{O(n)} draws» (§5.8 bullet 5) | `o8_draws_le` | PROVED explicit form: draws `2 + n² + 3K ≤ (n²+5)·cap` (Steps 1+3 draw 2+n², each trial draws 3: `F`, `P′`, `j′` — named ledger) |
| «Each step costs poly(n+b) word ops», key/mask bit-widths, balanced trees, n² fractional bits (§6.2) | — | algorithm/bit-level boundary, named |

## Statement hygiene (the standing audits)

* **Empty-expect audit:** no O8 statement touches `Finset.expect`. The only
  division is `1/Ŝ` in `o8_trial_count_bound`, guarded by explicit
  `hS : 0 < Ŝ` (well-formedness, so no `0/0`-junk); `Ŝ ≤ 1` follows in the
  application from proved L2.2 (`d(V) ≥ 0` ⟹ `2^{−d(V)} ≤ 1`) plus the draw
  structure, but is carried as a hypothesis because the `V_j` draws are
  algorithm data.
* **rpow junk audit:** `o8Cap` and every consumer state `n ≥ 0` (the paper's
  `n` is the input size), so `n^{0.7}` never has a negative base.
* **Identifier note:** `Ŝ` (combining circumflex) is not a valid Lean
  identifier — the Lean name is `Shat` throughout.
* **Pin fact (cost two failed builds to find):** `⌈x⌉` for `x : ℝ` is
  ℤ-valued here (`Int.ceil`); a `2 ^ (⌈τ₀n⌉ + …)` term is integer-exponent
  **zpow**, not `Real.rpow`. Bridge with `Real.rpow_intCast`
  (`x ^ ↑n = x ^ n`) before applying rpow lemmas; the ceil bounds live in the
  `Int` namespace even for ℝ (`Int.le_ceil`, `Int.ceil_lt_add_one`).
* **M2 status (2026-11-08): ALL PROVED.** `Proofs/O8.lean` is the
  statement-of-record; `Statements/O8.lean` holds quotes only. Receipts,
  freshly measured: `o8_cap_absorb`, `o8_cap_envelope`, `o8_time_bound`,
  `o8_trial_count_bound`, `o8_trials_le_cap` all
  `[propext, Classical.choice, Quot.sound]`; `o8_draws_le`
  `[propext, Quot.sound]` (pure ℕ arithmetic — not even choice). Build green,
  8949 jobs; package sorries 2 (the pre-existing L2.5 pair only).

# O4 — OpenAI L3.2 «Finite filtering data»: statements + proved-vs-named ledger

Sources: OpenAI preprint (`sections/filtering.tex`, Lemma 3.2 =
`lemma:finite-filtering` + the Riemann estimate + the effective version) and
Base `PROOF_0.4877.tex` (F7), §6.1 Lemma B1, Appendix B.2 (sha re-verified
`b397531c…`). Cross-checked against BRIDGE rows O4 and V1. **Credit: L3.2 is
OpenAI's; the (F7) generalization observation and Lemma B1's use are Base's;
this package formalizes the mathematical core.**

**Boundary (D7 note, as on O8):** the approximability procedure is an
algorithm statement (one fixed deterministic procedure, time poly(log P), no
point enumeration) and stays NAMED — no Light-step translation is imported,
and no procedure is constructed here. The numerical moment bounds
(2^{0.5168}, Base's Prop B 2^{η−0.00025} over the 430 certified rows) are
certified DATA and are not restated — the same decision as B4's certificate
rows.

## Proved-vs-named ledger

| Paper piece | Lean | Kind |
|---|---|---|
| «replace every integral … by the normalized average P⁻¹∑» | `o4Avg` | definition (junk `P = 0` guarded by `0 < P` on every consumer) |
| «the error … is at most 2π‖∂_w H‖_∞/P, uniformly in x» | `o4_avg_err_le` | PROVED in Lipschitz form; the derivative bound `B` is named data («the displayed coefficient bounds give explicit bounds on every fixed derivative») |
| (3.3) finite form: D ≥ 0, D−A ≥ 0, D−E ≥ 0 («unchanged for normalized finite averages») | `o4_gibbs` | PROVED (Gibbs via `ConcaveOn.le_map_sum` on `strictConcaveOn_log_Ioi`); one lemma, three instantiations (q = 1, f_*(x+·), g_*) as in the paper |
| «converge … at their grid points» + «the strict slack between 0.5168 and 0.5169» ⟹ finite moments; Lemma B1's «absolute P₀» | `o4_finite_from_continuous` + `o4P₀` | PROVED; P₀ is the explicit ceiling threshold, the continuous bound `C` and target `T` are named data (so (3.7)'s numerals enter only as parameters — Base's own (F7) exclusion respected) |
| «bounded above and bounded away from zero … their logarithms … uniformly bounded» | `o4_log_abs_le`, `o4_div_le`, `o4_le_div` | PROVED primitives; the composition with the displayed constants \|r\| ≤ 2.433, \|s\| ≤ 4.010 is named data |
| «one fixed deterministic procedure … in time polynomial in log P … need not enumerate the P points» | — | algorithm, named (the D_s boundary) |
| Prop 3.1's (3.6) / Prop B's 430 certified moment bounds | — | certified data, not restated (the B4 decision) |

## Statement hygiene (the standing audits)

* **Empty-expect audit:** no `Finset.expect` in any O4 statement. Junk
  guards: `P = 0` on `o4Avg` (guarded by `0 < P` on consumers), the division
  in `o4P₀` (guarded by `C < T`), all `q/w` divisions in `o4_gibbs` (guarded
  by strict positivity — the paper's `K_x` is a strictly positive density).
* **M2 status (2026-11-08): ALL PROVED.** `Proofs/O4.lean` is the
  statement-of-record; `Statements/O4.lean` holds quotes only. Receipts,
  freshly measured: all six `[propext, Classical.choice, Quot.sound]`.
  Build green, 8951 jobs; package sorries 2 (the pre-existing L2.5 pair
  only).
* **M2 statement corrections (the hn07 pattern, disclosed):**
  1. The quotient-boundedness pair as stated at M1 was FALSE: `num/den ≤ N/d`
     needs the denominator lower bound `d ≤ den` (not `≤` flipped), plus
     `0 < d` as an explicit hypothesis (correction 3: `d ≤ den` with
     `0 < den` does NOT give `0 < d`); the dual `o4_le_div` likewise takes
     `den ≤ D`. The corrected pair is exactly the paper's `K_x = f·g/Q` use.
  2. `o4_avg_err_le`'s Lipschitz hypothesis absorbs the paper's derivative
     bound (`B` named); `o4_finite_from_continuous` keeps `C`/`T` as
     parameters — (3.7)'s numerals never enter.
* **New pin gotchas (cost failed builds):** `∫ x in a..b, H x - c` parses
  the subtraction INSIDE the integral body — parenthesize `(∫ …)` before
  subtracting (bit twice); `Finset.sum_le_sum` with a `?_` body fails to
  synthesize the implicit `g` — pre-type the per-element proof as a `have`;
  `Real.log_div` takes `≠ 0` (not `0 <`); `norm_integral_le_of_norm_le_const`
  takes `uIoc` membership and concludes `C * |b - a|`; `neg_le_abs_self` is
  absent — derive via `le_abs_self (-a)` + `abs_neg` + linarith.

# O5+O7 — OpenAI Thm 4.1 + Thm 5.1: statements + proved-vs-named ledger

Sources: OpenAI preprint `sections/checksum.tex` (Thm 4.1 =
`thm:checksum`), `sections/aliases.tex` (Thm 5.1 = `thm:aliases`),
`sections/implementation.tex`; Base `PROOF_0.4877.tex` §2.2 (F8)
(sha re-verified `b397531c…`). Cross-checked against BRIDGE rows O5/O7.
**Credit: Thm 4.1 and Thm 5.1 are OpenAI's; this package formalizes the
mathematical core.** **D7 boundary:** the procedures stay named; op counts
stay in the papers' own counters.

## Proved-vs-named ledger

| Paper piece | Lean | Kind |
|---|---|---|
| Thm 4.1's budget `2^{(τ+20ε)n+O(√n)}poly(n+\|T\|)` — ceilings | `o5Cap` + `o5_cap_absorb` | PROVED; the two ceilings absorb unconditionally into the explicit `2√n+2` slack (unlike O8's absorption, no «sufficiently large n» needed — the budget's own slack covers the two units) |
| Thm 4.1's per-execution op bound (categories ≤ cap·poly) | `o5_time_bound` | PROVED (o8_time_bound consumer; ten counted categories; 16 = 2⁴ absorbs them; P = named per-category cost) |
| Thm 4.1's accuracy \|V̂_ρ − V_ρ\| ≤ 1/8 (MSE form) | `o5_mse_le` | PROVED skeleton; μ (per-table MSE, the L3.2/filtering input) and N (repetition count) named; the independence decomposition enters as the named `hMSE` |
| Thm 5.1's «stores and visits ≤ 2^{⌈τn⌉}poly(n) records» | `o7Cap` + `o7_records_le_cap` | PROVED (o8_trials_le_cap consumer: per-round ≥ 1 counted step + prefix ≤ cap ⟹ K ≤ cap); FAIL rule named |
| Thm 5.1's completeness «lists equal A_s(P) simultaneously, prob 1−o(1)» | `o7_union_le` | PROVED union-bound skeleton consuming B3's `cor_A6_per_alias`: total failure ≤ \|A\|·e^{−1}; the o(1) ratio is named external |
| The checksum/alias-extraction procedures (tables, patterns, phases, dedup, alias subtraction) | — | algorithm, named (the D_s boundary) |
| Per-table MSE μ, repetition count N, per-pair miss m, trial count Tp ≥ 1 | — | external inputs, named (the L3.2/filtering and B3 A5/A6 chains' outputs) |

## Statement hygiene (the standing audits)

* **Empty-expect audit:** `o5_mse_le` is the only expect-touching statement;
  `Ω.Nonempty` stated. Junk guards: `o5Cap`'s ℤ-ceilings (zpow bridging per
  the O8 pattern), `o7Cap`'s `.toNat` (the paper's τn ≥ 0).
* **Identifier note:** `X̄` (combining macron) is not a valid Lean identifier
  — the Lean name is `Xbar` (the `Ŝ`-class gotcha, second occurrence).
* **M2 status (2026-11-08): ALL PROVED.** `Proofs/O57.lean` is the
  statement-of-record; `Statements/O57.lean` holds quotes only. Receipts,
  freshly measured: all five `[propext, Classical.choice, Quot.sound]`
  (`o7_union_le` consumes B3's `cor_A6_per_alias` — the wired consumer).
  Build green, 8953 jobs; package sorries 2 (the pre-existing L2.5 pair
  only).

# PRIMECOUNT — the `hcount` premise (statements M1, 2026-11-09)

The dyadic prime-count input of the PROVED collision lemmas O3
(`L2_5_prime_collision`) and O6 (`L5_2_sparse_distinctions`), named so far
as the paper's own external input (setup.tex lem:prime-collision proof:
«The prime number theorem gives at least c₀·2^L/L primes … Rosser and
Schoenfeld»). Closing it makes the whole O1–O3+O6 cluster unconditional
number theory.

**Measured (this Mathlib, d13f23b):** Chebyshev-grade constants ANNIHILATE in
the interval difference — `pi_ge` ≈0.69·x/log x below vs
`pi_le_log4_mul_div` ≈2.77·x/log x above gives π(2^{L+1}) − π(2^L) ≥
(2/(L+1) − 4/L)·2^L < 0; and there is NO PNT asymptotic in the pin (grep of
`IsEquivalent … primeCounting`: no hits). The route is therefore Erdős's
binomial accounting; the pin holds all three anchors
(`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.pi_le_log4_mul_div`,
`Nat.factorization_choose'`).

## Statement file `Statements/PrimeCount.lean` (M1, module builds green)

| Step | Lean | Status |
|---|---|---|
| E1 geometric mass `4^n/(2n+1) ≤ C(2n,n)` | `central_binom_big` | **PROVED** (sum_range_choose + choose_le_middle + cast bridge) |
| E2 one carry: prime `n < p ≤ 2n` divides `C(2n,n)` | `prime_divides_central_binom` | **PROVED** (factorization_choose' carry-set over `Ico 1 2`; `p ≤ n+n < p²`; ⌊2n/p⌋=1, ⌊n/p⌋=0) |
| E3 zero carries for `2n/3 < p ≤ n` | (M2, inside assembly) | M1 plan only |
| E4 small-prime part O(√n log n) | (M2) | M1 plan only |
| E5 mid-strip product ≤ 4^{2n/3} (theta) | (M2) | M1 plan only |
| E6/E7 assembly + dyadic specialization | `erdos_dyadic_primes` | `sorry` (M2) |
| Discharge of O3/O6 (K = 1/c₀, L* = L₀) | `L2_5_prime_collision_unconditional` | `sorry` (M2, consumes the proved `L2_5_prime_collision`) |

Gotchas banked: `Nat.choose_le_middle (r n : ℕ)` — r FIRST, row SECOND, no
hypothesis, and it lands on `choose n (n/2)` (needs `2*n/2 = n` closed);
`Nat.mul_pow` closes `2^n * 2^n = 4^n` with the rfl that follows; push_cast's
output shape on `↑((2n+1)*C)` is the pushed product — rewrite it back with an
explicit `← h2`-style bridge rather than trusting the form; `if_pos` is
deprecated for `ite_eq_left` (warning only, M2 cleans it).

Build receipt: `lake build SubsetSumL25.Statements` green, 8931 jobs,
2026-11-09; the only package sorries are the two M2 placeholders above.

# PRIMECOUNT M2a+M2b progress (2026-11-09, wip-hcount @ 8719a64)

Landed on wip-hcount (not yet merged to main):
* **M2a (c0669f4):** E3 zero-carries (`mid_factorization_eq_zero`), E4
  `large_factorization_eq_one`, `large_product_le` — all PROVED.
* **M2b (8719a64):** `central_prod_factorization` (C = ∏ p^{v_p} over the
  primes ≤ 2n), `central_four_split` (the 4-way nested-filter split),
  `strip_prod_eq_one`, `large_prod_eq`, `small_prod_le`,
  `mid_prod_le` — all PROVED except the θ/primorial log-bridge tail
  inside mid_prod_le (the one named WIP sorry in the Proofs file).

## Remaining to close erdos_dyadic_primes (M2c):
1. `hprim` log-bridge: θ x = log (primorial ⌊x⌋₊) (theta_eq_log_primorial
   at x = (2*n/3 : ℕ)) + theta_le_log4_mul_x + the Nat.cast_le bridge
   (primorial ≤ 4^x from the log inequality). The hθ/h4log pieces are
   already in the file, commented.
2. The assembly: P_large·P_small·P_mid ≤ C ≤ 4^n ⟹
   (2n)^{k+c₁} ≥ 4^{n/3}/(2n+1) ⟹ k ≥ ((n/3)·log4 − log(2n+1) −
   π(√(2n))·log(2n))/log(2n) ≥ c₀·2^L/L for n = 2^L, L ≥ L₀.
   Suggested constants: c₀ = 1/12, L₀ via exists_nat_gt (~16-20);
   the √(2^{L+1}) ≤ 2^{L/2+1} bound avoids parity pain.
3. Then `L2_5_prime_collision_unconditional` = the already-proved
   `L2_5_prime_collision` instantiated at the witnesses (K = 1/c₀, L* = L₀)
   — one `obtain` + `exact` away.

## Build receipts
* M2a: green 8927 jobs. M2b: green 8927 jobs.
* Package sorries: Statements 2 (the M2c targets), Proofs 1 (hprim tail).
* Axioms receipts for the new M2a/M2b lemmas: not yet re-measured this
  session (the #print-axioms probe was SIGTERM-killed mid-import); the
  module sources use no native_decide and no custom axioms — re-measure
  on merge.
