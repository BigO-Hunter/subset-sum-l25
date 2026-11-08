/-
Base (a-kapila) Lemma A5 «one trial» and its Corollary A6 — the coverage step of
Theorem A.  This is the rung that consumes (F4) = OpenAI Lemma 2.5
(`Proofs/PrimeCollision.lean`) and Corollary D (`Proofs/CorD.lean`).

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` (sha256 b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298),
§5.4 (the constant `g_M`), §5.5 (Lemma A4, good sets), §5.6 (Lemma A5, Corollary
A6).  Verification against the primary text: `subset-sum-bridge/BRIDGE.md`
appendix row B3 («matches»).  Credit: the lemma is Base's.

Verbatim statement (PROOF_0.4877.tex §5.6):

    Lemma A5 (one trial).  Assume (LD), E_3, and the event of Lemma A4.  Fix s,
    an alias I ∈ A_s(P) with carry q, and one trial for (s, q).  After the
    trial, D_s contains the key of the class of I with probability at least
    2^{−g_M} n^{−6}.  The threshold for n does not depend on I, s, P or M.

    Corollary A6.  Assume (LD), E_3, and the event of Lemma A4.  Then, except
    with probability o(1), every alias class of every target is in its
    dictionary at the end of Step 4.

Supporting verbatim fragments this file formalizes:

    (§5.4)  g_M = −log E_V 2^{−d(V)},   e_M = E_V d(V).
    (§5.6 Step 1)  F is a uniform subset of M, so S is too.  Hence |S| = σ with
      probability C(m,σ)2^{−m} ≥ 1/(m+1).  Conditional on this event, S is a
      uniform σ-subset of M.
    (§5.6 Step 3)  Bad sets have probability at most 2^{−δn}.  … Since a_k ≤ 1,
      E_S[1_{S good} B_S/C(σ,k)] ≥ 2^{−g_M}/(v+1) − 2^{−δn} ≥ 2^{−g_M}/(2(v+1)).
    (§5.6 Step 4)  Its elements lie in (−nP, nP), so differences have at most
      ηn + log n + 3 bits.  For distinct x, x′ ∈ W_S, (F4) with L′ = ⌊γm⌋ gives
      Pr[P′ | x − x′] ≤ K₀n²2^{−γm} … Then the Cauchy–Schwarz inequality … shows
      that at least min(B_S, 2^{γm})/(4K₀n²) residues are occupied.  Since
      P′ < 2^{1+γm}, a uniform j′ hits an occupied residue with probability at
      least min(B_S2^{−γm},1)/(8K₀n²) ≥ B_S/(8K₀n²C(σ,k)).
    (§5.6 Step 6)  (1/(m+1))·E_S[1_good·(1/2)·B_S/(8K₀n²C(σ,k))]
      ≥ 2^{−g_M}/(32K₀n²(m+1)(v+1)) ≥ 2^{−g_M}n^{−6} for all large n.
    (Cor A6)  T ≥ n⁷2^{ĥF} ≥ n⁷2^{g_M} … all of them miss a fixed alias with
      probability at most (1 − 2^{−g_M}n^{−6})^T ≤ e^{−n}.

Translation notes (details in STMTS.md).  The rung is **conditional by
construction**: Lemma A5 quantifies over the algorithm's own objects (`D_s`,
keys, classes, records, the trial procedure), which this package does not
formalize.  As everywhere else in this ladder, the *algorithmic* steps become
named hypotheses and the mathematical content is proved:

* Steps 2 and 5 (the sign identity `c^F_i = ±c_i` on `S`, and «a hit is
  recovered»: a hit residue implies the key is inserted) are deterministic
  facts about the checksum and the record layout.  Step 2 survives as the shape
  of `B_S` (`hgood`: on a good `S`, `B_S ≥ a_k(S;c^I)·C(σ,k)`); Step 5 is the
  hypothesis `hstep5` mapping a hit to success.  Neither is an `axiom`.
* (LD), E_3 and the A4 event enter as the numeric bounds they are used for
  (A3(4)'s `2^{−δn} ≤ 2^{−g_M}/(2(v+1))` for Step 3; A3(1)'s `2^{ĥF} ≥ 2^{g_M}`
  for A6), each a named hypothesis.
* `2^{−g_M}` is written through `gM` so the paper's symbol survives verbatim;
  `two_pow_neg_gM` records the identity `2^{−g_M} = E_V 2^{−d(V)}`.
-/
import SubsetSumL25.Statements.Layers
import SubsetSumL25.Statements.CorD
import SubsetSumL25.Statements.PrimeCollision

namespace SubsetSumL25

variable {n : ℕ}

/-- `g_M = −log₂ E_V 2^{−d(V)}` (Base §5.4, verbatim «g_M = −log E_V 2^{−d(V)}»;
all paper logarithms are base 2). -/
noncomputable def gM (c : Fin n → ℤ) (M : Finset (Fin n)) (v : ℕ) : ℝ :=
  - Real.logb 2 ((M.powersetCard v).expect (fun V => (2 : ℝ) ^ (-(deficiency c V))))

-- `two_pow_neg_gM` is PROVED; statement-of-record in `Proofs/A5.lean`.

-- `middle_choose_div_two_pow_ge_inv` is PROVED; statement-of-record in `Proofs/A5.lean`.

/-- Step 1 identity (verbatim: «Conditional on this event, S is a uniform
σ-subset of M»): averaging over uniform subsets and conditioning on the
cardinality `σ` is the same as averaging over uniform `σ`-subsets, scaled by
`C(m,σ)2^{−m}`. -/
theorem powerset_expect_ite_card (M : Finset (Fin n)) {σ : ℕ}
    (g : Finset (Fin n) → ℝ) :
    ((Nat.choose M.card σ : ℝ) / 2 ^ M.card) * (M.powersetCard σ).expect g
      = (M.powerset).expect (fun F => if F.card = σ then g F else 0) := by
  sorry

-- `expect_bad_indicator_ge` is PROVED; statement-of-record in `Proofs/A5.lean`.

/-- Ordered colliding pairs of `W` modulo `p`: the count whose expectation Step 4
bounds with (F4).  The paper's second moment is `Σ_y z_y² = |W| +
collisionPairs W p`. -/
def collisionPairs (W : Finset ℤ) (p : ℕ) : ℕ :=
  ((W.product W).filter (fun q => q.1 ≠ q.2 ∧ (p : ℤ) ∣ (q.1 - q.2))).card

-- `expect_dvd_eq_badPrimes` is PROVED; statement-of-record in `Proofs/A5.lean`.

-- `pair_collision_le` is PROVED; statement-of-record in `Proofs/A5.lean`.

/-- Step 4 second moment (verbatim: «Then E_{P′} Σ_y z_y² ≤ B_S +
K₀n²B_S²2^{−γm}»), in the collision form: each of the at most `|W|²` ordered
pairs contributes at most the (F4) per-pair bound. -/
theorem collisionPairs_expect_le (W : Finset ℤ) {L : ℕ} {K₀ : ℝ}
    (hpair : ∀ x ∈ W, ∀ x' ∈ W, x ≠ x' →
      (primesInterval L).expect (fun (p : ℕ) => if (↑p : ℤ) ∣ (x - x') then (1 : ℝ) else 0)
        ≤ K₀ / (2 : ℝ) ^ L) :
    (primesInterval L).expect (fun p => (collisionPairs W p : ℝ))
      ≤ (W.card : ℝ) ^ 2 * (K₀ / (2 : ℝ) ^ L) := by
  sorry

/-- Step 4 occupancy (the combinatorial core of «at least
min(B_S, 2^{γm})/(4K₀n²) residues are occupied»): colliding pairs are the only
thing that reduces the number of occupied residue classes. -/
theorem occupied_ge_card_sub_collisions (W : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    W.card ≤ (W.image (fun x => x % (p : ℤ))).card + collisionPairs W p := by
  sorry

/-- Step 4 end (verbatim: «a uniform j′ hits an occupied residue with
probability at least min(B_S2^{−γm},1)/(8K₀n²)»): a uniform `j′ ∈ [0,P′)`
hits an occupied class with probability `#occupied / P′`. -/
theorem hit_prob_eq_occupied (W : Finset ℤ) {p : ℕ} (hp : 0 < p) :
    (Finset.range p).expect
        (fun j => if ∃ x ∈ W, x % (p : ℤ) = (j : ℤ) then (1 : ℝ) else 0)
      = ((W.image (fun x => x % (p : ℤ))).card : ℝ) / p := by
  sorry

/-- Step 3 assembly: with Corollary D's bound (`hcorD`), the good sets dominating
`a_k` (`hgood`, Step 2), `B_S ≤ C(σ,k)` and the A4 bad fraction (`hbad`,
`hδ`), the good-hit average keeps half of `2^{−g_M}/(v+1)`:

    E_S[1_good B_S/C(σ,k)] ≥ 2^{−g_M}/(v+1) − 2^{−δn} ≥ 2^{−g_M}/(2(v+1)).

`B` is the paper's `B_S` and `Csk` its `C(σ,k)`. -/
theorem good_hit_expect_ge (c : Fin n → ℤ) {M : Finset (Fin n)} {k σ v δn : ℕ}
    (B : Finset (Fin n) → ℕ) (good : Finset (Fin n) → Prop) [DecidablePred good]
    (hCpos : (0 : ℝ) < (Nat.choose σ k : ℝ))
    (hBle : ∀ S, B S ≤ Nat.choose σ k)
    (hgood : ∀ S ∈ M.powersetCard σ, good S →
      layerDensity c S k ≤ (B S : ℝ) / (Nat.choose σ k : ℝ))
    (hcorD : (2 : ℝ) ^ (-(gM c M v)) / ((v : ℝ) + 1)
      ≤ (M.powersetCard σ).expect (fun S => layerDensity c S k))
    (hδ : (2 : ℝ) ^ (-(δn : ℝ)) ≤ (2 : ℝ) ^ (-(gM c M v)) / (2 * ((v : ℝ) + 1)))
    (hbad : ((M.powersetCard σ).filter (fun S => ¬ good S)).card
      ≤ (2 : ℝ) ^ (-(δn : ℝ)) * (M.powersetCard σ).card) :
    (2 : ℝ) ^ (-(gM c M v)) / (2 * ((v : ℝ) + 1))
      ≤ (M.powersetCard σ).expect
          (fun S => if good S then (B S : ℝ) / (Nat.choose σ k : ℝ) else 0) := by
  sorry

-- `lem_A5_product` is PROVED; statement-of-record in `Proofs/A5.lean`.

-- `lem_A5_threshold` is PROVED; statement-of-record in `Proofs/A5.lean`.

-- `cor_A6_per_alias` is PROVED; statement-of-record in `Proofs/A5.lean`.

end SubsetSumL25
