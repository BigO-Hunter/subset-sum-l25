/-
M6 (DS): Lemma A7 — §5.7's expected-work ledger (the seven-step cost
accounting with the (C2)–(C7) clause discharges).  This file is the
statement-of-record for what is proved; the verbatim source and the milestone
ladder live in `Statements/DS.lean`.

Primary source: `a-kapila/maths-proofs` @ 44c34961,
`subset-sum/PROOF_0.4877.tex` §5.7 (sha256
b397531cc5997e88c439d5290774861b46a34aa32d9cd71fa7dcced130359298).

DS-M6 Lemma A7 — verbatim:
    «Lemma A7. Assume (LD) and E_3. Condition on M, L and Step 3, and average
    over P and the trials; the phases are arbitrary. Then the uncapped
    procedure takes in expectation at most
        (b+2) 2^{(τ₀ − ε₀ + ζ)n + O(n^{0.6})} steps.
    Proof. Recall T ≤ 2n⁷2^{F̂}, and that there are O(n³) pairs (s, q).
    Polynomial factors go into 2^{O(n^{0.6})}.  We bound each kind of step.
    1. Value maps and Step 3: 2^{|L|} + 2^{|R|} + n²2^v steps.  The exponents
       l, r and μ(1−2a) are below τ₀ − ε₀, by (C6) and (C7).
    2. Masks: each trial lists C(m,k) + C(m,σ−k) ≤ 2^{h(1/2−a)m+2} masks and
       sorts them into classes.  By Lemma A3(4) and (S5), the total is
       2^{(h(1/2−a)μ + 1/2 − τ₀ + ζ)n + O(n^{0.6})}.  By (C5) the exponent is
       below (τ₀ − ε₀ + ζ)n.
    3. Small primes: each trial tests at most n³ candidates, each by at most
       2^{γm/2 + 1} divisions.  The total is
       2^{(1/2 − τ₀ + ζ + γμ/2)n + O(n^{0.6})}, far below the bound.
    4. Sorting keys by residue: each trial sorts at most
       (n+1)(2^{|L|−d(L)} + 2^{|R|}) keys.  By Lemma A3(3) and (4), the total
       is at most 2^{ln + O(n^{0.6})} + 2^{(r + 1/2 − τ₀ + ζ)n + O(n^{0.6})}.
    5. Left records: for fixed choices other than j′, a pair (κ_L, X) is
       listed with probability 1/P′, and 1/P′ ≤ 2^{1−γm}.  So a trial lists
       at most (n+1)2^{|L|−d(L)}C(m,k)2^{1−γm} left records in expectation.
       With Lemma A3(3), the total is 2^{(l + (h(a)−γ)μ)n + O(n^{0.6})}.
       Use (C2).
    6. Right class records: by Lemma A2, a trial handles at most
       (2m+1)2^{m−d(M)} classes.  It lists at most
       (n+1)2^{|R|}(2m+1)2^{m−d(M)}2^{1−γm} class records in expectation.
       With Lemma A3(2), the total is at most
       2^{(r + (1−γ)μ)n + O(n^{0.6})} + 2^{μn + O(n^{0.6})}.  Use (C3), and
       μ < τ₀ − ε₀.
    7. Visits and expansions: … the total over all trials is
       (b + log n) 2^{(1 − μ + (h(a)+h(1/2−a)−γ)μ − η)n + O(n^{0.6})}.  By
       (C4) the exponent is below (τ₀ − ε₀)n.
    Every item is at most (b+2) 2^{(τ₀ − ε₀ + ζ)n + O(n^{0.6})}.»

Structure (the O8/B5 op-bound style): each of the seven items gets its own
theorem, plus the shared discharge form and the envelope.  Where the item's
internal mechanism is countable arithmetic, the assembly is PROVED from
finer displays:

  * item 2 derives the per-trial mask display 2^{h(1/2−a)m+2} from the (S5)
    pair C(m,k) ≤ 2^{h(a)m}, C(m,σ−k) ≤ 2^{h(1/2−a)m+1} and h(a) ≤ h(1/2−a),
    then multiplies by the A3(4) trial bound T ≤ 2n⁷2^{F̂} and discharges the
    exponent by (C5);
  * item 4 is where Lemma A3(3) earns its keep: F̂ ≤ d(L) + O(n^{0.6})
    CANCELS the 2^{−d(L)} of 2^{|L|−d(L)} — the paper's first summand
    2^{ln+O} is exactly this cancellation, proved here;
  * item 5 is the same cancellation carrying (S5)'s C(m,k) ≤ 2^{h(a)m} into
    the (C2) exponent l + (h(a)−γ)μ (the −γμ leaf is the 1/P′ ≤ 2^{1−γm}
    bound, moved to the μn scale through the sizes row m ≥ μn − 2);
  * item 6's first summand is the A3(2) cancellation F̂ ≤ d(M) + O(n^{0.6})
    against 2^{m−d(M)} (the −γμ leaf via the same sizes row); the second
    summand (the paper's 2^{μn+O} mop-up for the (2m+1)2^{m−d(M)} class
    handling) is taken display-verbatim — the paper does not display its
    T-factor pairing, so the mop-up's internal split stays at the boundary;
  * item 3's n³ candidate count is the algorithm's display (D7 boundary);
    its «far below the bound» discharge `1/2 + γμ/2 ≤ 2τ₀ − ε₀` is a §2.2
    numeric that is NOT one of the eight Arb-certified clauses — a
    (C1)-routed derivation (γ < h(2a)/2 plus (S4)) would drag entropy
    numerics and is left at the D7 boundary per the ladder.

The clause discharges all use the ε₀-slack form: ε₀ is the paper's «least
slack in (C1)–(C8)», so each clause is stated with slack ε₀ (e.g. (C6) as
l + ε₀ ≤ τ₀).  Two further discharges are §2.2-table numerics rather than
named clauses — item 4's `hnum4 : r + 1/2 ≤ 2τ₀ − ε₀` (r = 1−μ−l = 0.04323
against 2τ₀ ≈ 0.9754) and item 6's `hmu : μ + ε₀ ≤ τ₀` (μ = 0.473 against
τ₀ ≈ 0.4877; the paper's «and μ < τ₀ − ε₀») — named hypotheses, flagged.
Instance arithmetic enters as hypotheses per the ledger scope.

The O(n^{0.6}) of every display is the explicit slack parameter δ (the
per-item polynomial factors sit inside 2^δ by hypothesis, the paper's
«polynomial factors go into 2^{O(n^{0.6})}»).  The envelope consumes B5's
proved `a7_envelope` (Proofs/Presearch.lean) by name: seven items within
(b+2)·2^K sum to (b+2)·2^{K+3} — the paper's closing line, the O(·)
absorbing the 7.

Cast-discipline: ℝ for the exponents and step totals, ℕ for the trial and
mask counts; `Nat.cast_*` at the ℕ↔ℝ boundary only.
-/
import Mathlib
import SubsetSumL25.Statements.DS
import SubsetSumL25.Proofs.Presearch

namespace SubsetSumL25

/-! ### Small machinery -/

/-- The rpow-product join with both exponents pinned (the anonymous `rw
[← Real.rpow_add]` form instantiates from the first match and can rewrite the
wrong product when both sides are rpow products). -/
theorem a7_two_pow_add {p q : ℝ} : (2 : ℝ) ^ p * 2 ^ q = 2 ^ (p + q) :=
  (Real.rpow_add (by norm_num : (0 : ℝ) < 2)).symm

/-- Numeral rpow facts (pinned as named lemmas — the isolated goals are what
`norm_num` provably closes at this pin, per O8's `show … from by norm_num`). -/
theorem a7_two_pow_one : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num

theorem a7_two_pow_two : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num

theorem a7_two_pow_three : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num

theorem a7_two_pow_four : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num

theorem a7_two_pow_five : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num

/-- One ledger item's discharge: a total of the form `poly · 2^{exp·n}` with
`exp ≤ K` (the clause) and `poly ≤ 2^δ` (the paper's «polynomial factors go
into 2^{O(n^{0.6})}») lands inside the per-item cap `(b+2)·2^{K·n+δ}`
(`b ≥ 0` gives `b + 2 ≥ 1`). -/
theorem a7_item_form {b K exp δ poly n : ℝ} (hb : 0 ≤ b)
    (hpoly : poly ≤ 2 ^ δ) (hexp : exp ≤ K) :
    poly * 2 ^ (exp * n) ≤ (b + 2) * 2 ^ (K * n + δ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hδ0 : (0 : ℝ) ≤ 2 ^ δ := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) δ
  have hx0 : (0 : ℝ) ≤ 2 ^ (exp * n) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (exp * n)
  have hmono : 2 ^ (exp * n) ≤ 2 ^ (K * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hjoin : 2 ^ δ * 2 ^ (K * n) = 2 ^ (K * n + δ) := (Real.rpow_add h2).symm
  have hstep : poly * 2 ^ (exp * n) ≤ 2 ^ (K * n + δ) := by
    calc poly * 2 ^ (exp * n) ≤ 2 ^ δ * 2 ^ (K * n) := mul_le_mul hpoly hmono hδ0 hx0
      _ = 2 ^ (K * n + δ) := hjoin
  have hxb : (1 : ℝ) ≤ b + 2 := by linarith
  have hcap0 : (0 : ℝ) ≤ 2 ^ (K * n + δ) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  calc poly * 2 ^ (exp * n) ≤ 2 ^ (K * n + δ) := hstep
    _ ≤ (b + 2) * 2 ^ (K * n + δ) := mul_le_mul_of_nonneg_right hxb hcap0

/-- Exponent-scale transfer: `m ≤ μ·n` lifts `c·m ≤ c·μ·n` for `c ≥ 0`. -/
theorem a7_scale_mono {c m μ n : ℝ} (hnn : 0 ≤ c) (h : m ≤ μ * n) (hn : 0 ≤ n) :
    c * m ≤ c * μ * n :=
  mul_le_mul (mul_le_mul_of_nonneg_left h hnn) (le_refl _) hnn hn

/-! ### Item 1 — value maps and Step 3 (the (C6)/(C7) chain) -/

/-- §5.7 item 1: `2^{|L|} + 2^{|R|} + n²·2^v ≤ (b+2)·2^{(τ₀−ε₀+ζ)n+δ}`.
Inputs are the §2.2 sizes rows in exponent form (`|L| = ⌊ln⌋ ≤ ln`;
`|R| = n − m − |L| ≤ rn + 3` — the two floors; `v = m − 2k ≤ (1−2a)μn + 2`)
and the clause chain: (C7) μ(1−2a) ≤ l with (C6)'s slack l + ε₀ ≤ τ₀ gives
μ(1−2a) ≤ τ₀ − ε₀ — the paper's «by (C6) and (C7)».  The constants 8 = 2³ and
4 = 2² are the sizes' floor slack, absorbed by δ together with the n² factor
(n ≥ 1 — the paper's «for all large n»). -/
theorem a7_item1_value_maps {b l r μ a τ₀ ε₀ ζ δ n Lc Rc vc : ℝ}
    (hC6l : l + ε₀ ≤ τ₀) (hC6r : r + ε₀ ≤ τ₀) (hC7 : μ * (1 - 2 * a) ≤ l)
    (hζ : 0 ≤ ζ) (hn : 1 ≤ n)
    (hL : Lc ≤ l * n) (hR : Rc ≤ r * n + 3) (hv : vc ≤ μ * (1 - 2 * a) * n + 2)
    (hpoly : (20 : ℝ) * n ^ 2 ≤ 2 ^ δ) (hb : 0 ≤ b) :
    2 ^ Lc + 2 ^ Rc + n ^ 2 * 2 ^ vc ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hl : l ≤ τ₀ - ε₀ := by linarith
  have hr : r ≤ τ₀ - ε₀ := by linarith
  have hmu2 : μ * (1 - 2 * a) ≤ τ₀ - ε₀ := le_trans hC7 hl
  have hKge : τ₀ - ε₀ ≤ τ₀ - ε₀ + ζ := by linarith
  have hn2 : (1 : ℝ) ≤ n ^ 2 := le_mul_of_one_le_right (by positivity) hn
  have hcap0 : (0 : ℝ) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hcapmono : ∀ e : ℝ, e ≤ τ₀ - ε₀ → 2 ^ (e * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    intro e he
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right (le_trans he hKge) (le_of_lt hn))
  have e1 : 2 ^ Lc ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hL).trans (hcapmono l hl)
  have e2 : 2 ^ Rc ≤ 8 * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    calc 2 ^ Rc ≤ 2 ^ (r * n + 3) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hR
      _ = 2 ^ (r * n) * 2 ^ (3 : ℝ) := by
          rw [a7_two_pow_add (p := r * n) (q := 3)]
      _ = 8 * 2 ^ (r * n) := by rw [a7_two_pow_three]; ring
      _ ≤ 8 * 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
          mul_le_mul_of_nonneg_left (hcapmono r hr) (by norm_num)
  have e3 : n ^ 2 * 2 ^ vc ≤ 4 * n ^ 2 * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    calc n ^ 2 * 2 ^ vc ≤ n ^ 2 * 2 ^ (μ * (1 - 2 * a) * n + 2) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hv)
            (by positivity)
      _ = 2 ^ (μ * (1 - 2 * a) * n) * 2 ^ (2 : ℝ) * n ^ 2 := by
          rw [a7_two_pow_add (p := μ * (1 - 2 * a) * n) (q := 2)]; ring
      _ = 4 * n ^ 2 * 2 ^ (μ * (1 - 2 * a) * n) := by rw [a7_two_pow_two]; ring
      _ ≤ 4 * n ^ 2 * 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
          mul_le_mul_of_nonneg_left (hcapmono _ hmu2) (by norm_num)
  have hsum : 2 ^ Lc + 2 ^ Rc + n ^ 2 * 2 ^ vc
      ≤ (20 : ℝ) * n ^ 2 * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    calc 2 ^ Lc + 2 ^ Rc + n ^ 2 * 2 ^ vc
        ≤ 1 * 2 ^ ((τ₀ - ε₀ + ζ) * n) + 8 * 2 ^ ((τ₀ - ε₀ + ζ) * n)
            + 4 * n ^ 2 * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by linarith [e1, e2, e3]
      _ = (9 + 4 * n ^ 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by ring
      _ ≤ (20 : ℝ) * n ^ 2 * 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
          mul_le_mul_of_nonneg_right (by linarith [hn2]) hcap0
  exact le_trans hsum (a7_item_form hb hpoly (le_refl _))

/-! ### Item 2 — masks ((S5) display derived; (C5) discharge) -/

/-- §5.7 item 2: the mask total.  The per-trial display
`C(m,k) + C(m,σ−k) ≤ 2^{h(1/2−a)m+2}` is DERIVED from the (S5) pair and
`h(a) ≤ h(1/2−a)` (entropy monotonicity on [0,1/2], the §2.2 numeric a ≤ 1/4
as hypothesis `hha`); the trial factor is A3(4)'s `T ≤ 2n⁷2^{F̂}` with
`F̂ ≤ (1/2−τ₀+ζ)n + 4n^{0.6} + 1`; the exponent discharges by (C5):
h(1/2−a)μ + 1/2 − τ₀ ≤ τ₀ − ε₀. -/
theorem a7_item2_masks {b m σ k : ℕ} {hA hB μ τ₀ ε₀ ζ δ n Fhat : ℝ} (T : ℕ)
    (hS5a : (Nat.choose m k : ℝ) ≤ 2 ^ (hA * (m : ℝ)))
    (hS5b : (Nat.choose m (σ - k) : ℝ) ≤ 2 ^ (hB * (m : ℝ) + 1))
    (hha : hA ≤ hB) (hBnn : 0 ≤ hB)
    (hT : (T : ℝ) ≤ 2 * n ^ 7 * 2 ^ Fhat)
    (hF : Fhat ≤ (1 / 2 - τ₀ + ζ) * n + 4 * n ^ (0.6 : ℝ) + 1)
    (hm : (m : ℝ) ≤ μ * n) (hC5 : hB * μ + 1 / 2 ≤ 2 * τ₀ - ε₀)
    (hζ : 0 ≤ ζ) (hn : 0 ≤ n) (hpoly : (16 : ℝ) * n ^ 7 * 2 ^ (4 * n ^ (0.6 : ℝ)) ≤ 2 ^ δ)
    (hb : 0 ≤ b) :
    (T : ℝ) * ((Nat.choose m k + Nat.choose m (σ - k) : ℕ) : ℝ)
      ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hTnn : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  -- per-trial: the (S5) pair into the paper's 2^{h(1/2−a)m+2}
  have htrial : ((Nat.choose m k + Nat.choose m (σ - k) : ℕ) : ℝ) ≤ 2 ^ (hB * (m : ℝ) + 2) := by
    have t1 : (Nat.choose m k : ℝ) ≤ 2 ^ (hB * (m : ℝ)) :=
      hS5a.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (mul_le_mul_of_nonneg_right hha (Nat.cast_nonneg m)))
    have hp0 : (0 : ℝ) ≤ 2 ^ (hB * (m : ℝ)) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    calc ((Nat.choose m k + Nat.choose m (σ - k) : ℕ) : ℝ)
        ≤ 2 ^ (hB * (m : ℝ)) + 2 ^ (hB * (m : ℝ) + 1) := add_le_add t1 hS5b
      _ = 2 ^ (hB * (m : ℝ)) + 2 ^ (hB * (m : ℝ)) * 2 ^ (1 : ℝ) := by
          rw [a7_two_pow_add (p := hB * (m : ℝ)) (q := 1)]
      _ = 3 * 2 ^ (hB * (m : ℝ)) := by rw [a7_two_pow_one]; ring
      _ ≤ 4 * 2 ^ (hB * (m : ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) hp0
      _ = 2 ^ (hB * (m : ℝ)) * 2 ^ (2 : ℝ) := by rw [a7_two_pow_two]; ring
      _ = 2 ^ (hB * (m : ℝ) + 2) := (a7_two_pow_add (p := hB * (m : ℝ)) (q := 2)).symm
  -- the trial product, one rpow: F̂ + hB·m + 2 ≤ ((1/2−τ₀+ζ) + hB·μ)n + 4q + 3
  have hmB : hB * (m : ℝ) ≤ hB * μ * n := a7_scale_mono hBnn hm hn
  have hexpsum : Fhat + (hB * (m : ℝ) + 2)
      ≤ ((1 / 2 - τ₀ + ζ) + hB * μ) * n + 4 * n ^ (0.6 : ℝ) + 3 := by
    have hsplit : (1 / 2 - τ₀ + ζ) * n + hB * μ * n
        = ((1 / 2 - τ₀ + ζ) + hB * μ) * n := by ring
    linarith [hF, hmB, hsplit]
  have hA3 : 2 ^ Fhat * 2 ^ (hB * (m : ℝ) + 2)
      ≤ 2 ^ (((1 / 2 - τ₀ + ζ) + hB * μ) * n + 4 * n ^ (0.6 : ℝ) + 3) := by
    rw [a7_two_pow_add (p := Fhat) (q := hB * (m : ℝ) + 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexpsum
  -- assemble and discharge (C5)
  have hC5exp : (1 / 2 - τ₀ + ζ) + hB * μ ≤ τ₀ - ε₀ + ζ := by linarith
  have hcapmono : 2 ^ (((1 / 2 - τ₀ + ζ) + hB * μ) * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hC5exp (le_of_lt hn))
  have hsplit : 2 ^ (((1 / 2 - τ₀ + ζ) + hB * μ) * n + 4 * n ^ (0.6 : ℝ) + 3)
      = 8 * 2 ^ (((1 / 2 - τ₀ + ζ) + hB * μ) * n) * 2 ^ (4 * n ^ (0.6 : ℝ)) := by
    rw [a7_two_pow_add (p := ((1 / 2 - τ₀ + ζ) + hB * μ) * n) (q := 4 * n ^ (0.6 : ℝ) + 3),
      a7_two_pow_add (p := 4 * n ^ (0.6 : ℝ)) (q := 3), a7_two_pow_three]
    ring
  have hpowpos : (0 : ℝ) ≤ 2 ^ (4 * n ^ (0.6 : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hkey : (T : ℝ) * ((Nat.choose m k + Nat.choose m (σ - k) : ℕ) : ℝ)
      ≤ (16 : ℝ) * n ^ 7 * 2 ^ (4 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    calc (T : ℝ) * ((Nat.choose m k + Nat.choose m (σ - k) : ℕ) : ℝ)
        ≤ (2 * n ^ 7 * 2 ^ Fhat) * 2 ^ (hB * (m : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = 2 * n ^ 7 * (2 ^ Fhat * 2 ^ (hB * (m : ℝ) + 2)) := by ring
      _ ≤ 2 * n ^ 7 * 2 ^ (((1 / 2 - τ₀ + ζ) + hB * μ) * n + 4 * n ^ (0.6 : ℝ) + 3) :=
          mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ = (16 : ℝ) * n ^ 7 * 2 ^ (4 * n ^ (0.6 : ℝ))
            * 2 ^ (((1 / 2 - τ₀ + ζ) + hB * μ) * n) := by rw [hsplit]; ring
      _ ≤ (16 : ℝ) * n ^ 7 * 2 ^ (4 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
          mul_le_mul_of_nonneg_left hcapmono (by nlinarith [hpowpos])
  exact le_trans hkey (a7_item_form hb hpoly (le_refl _))

/-! ### Item 3 — small primes (the «far below the bound» numeric row) -/

/-- §5.7 item 3: the small-prime division total, from the trial display
«n³ candidates, each by at most 2^{γm/2+1} divisions» (the candidate count is
the algorithm — D7 boundary) and the A3(4) trial factor.  The discharge needs
`1/2 + γμ/2 ≤ 2τ₀ − ε₀` — the paper's «far below the bound» (1/2 − τ₀ ≈ 0.012
and γμ/2 ≈ 0.029 against τ₀ ≈ 0.488), a §2.2-table numeric NOT among the
eight Arb-certified clauses (`hnum3`; a (C1)-routed derivation is left at the
D7 boundary per the ledger scope). -/
theorem a7_item3_primes {b m : ℕ} {μ γ τ₀ ε₀ ζ δ n Fhat : ℝ} (T : ℕ)
    (hγnn : 0 ≤ γ)
    (hT : (T : ℝ) ≤ 2 * n ^ 7 * 2 ^ Fhat)
    (hF : Fhat ≤ (1 / 2 - τ₀ + ζ) * n + 4 * n ^ (0.6 : ℝ) + 1)
    (hm : (m : ℝ) ≤ μ * n)
    (hnum3 : 1 / 2 + γ * μ / 2 ≤ 2 * τ₀ - ε₀)
    (hζ : 0 ≤ ζ) (hn : 0 ≤ n) (hpoly : (8 : ℝ) * n ^ 10 * 2 ^ (4 * n ^ (0.6 : ℝ)) ≤ 2 ^ δ)
    (hb : 0 ≤ b) :
    (T : ℝ) * (n ^ 3 * 2 ^ (γ * (m : ℝ) / 2 + 1))
      ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  -- the exponent bookkeeping: F̂ + (γm/2 + 1) ≤ ((1/2−τ₀+ζ) + γμ/2)n + 4q + 2
  have hmγ : γ * (m : ℝ) / 2 ≤ γ * μ * n / 2 := by
    have h := a7_scale_mono hγnn hm hn
    linarith
  have hexpsum : Fhat + (γ * (m : ℝ) / 2 + 1)
      ≤ ((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n + 4 * n ^ (0.6 : ℝ) + 2 := by
    have hsplit : (1 / 2 - τ₀ + ζ) * n + γ * μ * n / 2
        = ((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n := by ring
    linarith [hF, hmγ, hsplit]
  have hA3 : 2 ^ Fhat * 2 ^ (γ * (m : ℝ) / 2 + 1)
      ≤ 2 ^ (((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n + 4 * n ^ (0.6 : ℝ) + 2) := by
    rw [a7_two_pow_add (p := Fhat) (q := γ * (m : ℝ) / 2 + 1)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexpsum
  have hnum3exp : (1 / 2 - τ₀ + ζ) + γ * μ / 2 ≤ τ₀ - ε₀ + ζ := by linarith
  have hcapmono : 2 ^ (((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hnum3exp (le_of_lt hn))
  have hsplit : 2 ^ (((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n + 4 * n ^ (0.6 : ℝ) + 2)
      = 4 * 2 ^ (((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n) * 2 ^ (4 * n ^ (0.6 : ℝ)) := by
    rw [a7_two_pow_add (p := ((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n) (q := 4 * n ^ (0.6 : ℝ) + 2),
      a7_two_pow_add (p := 4 * n ^ (0.6 : ℝ)) (q := 2), a7_two_pow_two]
    ring
  have hpowpos : (0 : ℝ) ≤ 2 ^ (4 * n ^ (0.6 : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hkey : (T : ℝ) * (n ^ 3 * 2 ^ (γ * (m : ℝ) / 2 + 1))
      ≤ (8 : ℝ) * n ^ 10 * 2 ^ (4 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    calc (T : ℝ) * (n ^ 3 * 2 ^ (γ * (m : ℝ) / 2 + 1))
        ≤ (2 * n ^ 7 * 2 ^ Fhat) * (n ^ 3 * 2 ^ (γ * (m : ℝ) / 2 + 1)) :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = 2 * n ^ 7 * (n ^ 3 * (2 ^ Fhat * 2 ^ (γ * (m : ℝ) / 2 + 1))) := by ring
      _ ≤ 2 * n ^ 7 * (n ^ 3 * 2 ^ (((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n
            + 4 * n ^ (0.6 : ℝ) + 2)) := mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ = (8 : ℝ) * n ^ 10 * 2 ^ (4 * n ^ (0.6 : ℝ))
            * 2 ^ (((1 / 2 - τ₀ + ζ) + γ * μ / 2) * n) := by rw [hsplit]; ring
      _ ≤ (8 : ℝ) * n ^ 10 * 2 ^ (4 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
          mul_le_mul_of_nonneg_left hcapmono (by nlinarith [hpowpos])
  exact le_trans hkey (a7_item_form hb hpoly (le_refl _))

/-! ### Item 4 — sorting keys by residue (the A3(3) d(L)-cancel) -/

/-- §5.7 item 4: the key-sorting total, from the per-trial display
`(n+1)(2^{|L|−d(L)} + 2^{|R|})`.  Summand 1 is the A3(3) cancellation:
`F̂ ≤ d(L) + 5n^{0.6} + 1` cancels `2^{−d(L)}` and the exponent becomes `l`
(the paper's «2^{ln + O(n^{0.6})}»), discharged by (C6)'s slack.  Summand 2
uses A3(4) (`F̂ ≤ (1/2−τ₀+ζ)n + 4n^{0.6} + 1`) for the exponent
`r + 1/2 − τ₀ + ζ`, discharged by `hnum4 : r + 1/2 ≤ 2τ₀ − ε₀` — the §2.2
numeric r = 1−μ−l = 0.04323 against 2τ₀ ≈ 0.9754 (r + 1/2 ≈ 0.543), NOT one
of the eight named clauses — instance arithmetic as a named hypothesis. -/
theorem a7_item4_sorting {b l r τ₀ ε₀ ζ δ n dL Fhat Lc Rc : ℝ} (T : ℕ)
    (hC6l : l + ε₀ ≤ τ₀) (hnum4 : r + 1 / 2 ≤ 2 * τ₀ - ε₀) (hζ : 0 ≤ ζ) (hn : 0 ≤ n)
    (hA3_3 : Fhat ≤ dL + 5 * n ^ (0.6 : ℝ) + 1)
    (hA3_4 : Fhat ≤ (1 / 2 - τ₀ + ζ) * n + 4 * n ^ (0.6 : ℝ) + 1)
    (hL : Lc ≤ l * n) (hR : Rc ≤ r * n + 3)
    (hT : (T : ℝ) ≤ 2 * n ^ 7 * 2 ^ Fhat)
    (hpoly : (128 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) ≤ 2 ^ δ)
    (hb : 0 ≤ b) :
    (T : ℝ) * (n + 1) * (2 ^ (Lc - dL) + 2 ^ Rc)
      ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hsplit : (T : ℝ) * (n + 1) * (2 ^ (Lc - dL) + 2 ^ Rc)
      = (T : ℝ) * (n + 1) * 2 ^ (Lc - dL) + (T : ℝ) * (n + 1) * 2 ^ Rc := by ring
  -- summand 1: the d(L)-cancel — F̂ + (Lc − dL) ≤ l·n + 5n^{0.6} + 1
  have hcancel : Fhat + (Lc - dL) ≤ l * n + 5 * n ^ (0.6 : ℝ) + 1 := by
    have e1 : dL + 5 * n ^ (0.6 : ℝ) + 1 + (Lc - dL) = Lc + 5 * n ^ (0.6 : ℝ) + 1 := by ring
    linarith [hA3_3, hL, e1]
  have hjoin1 : 2 ^ Fhat * 2 ^ (Lc - dL) = 2 ^ (Fhat + (Lc - dL)) :=
    a7_two_pow_add (p := Fhat) (q := Lc - dL)
  have hC6exp : l ≤ τ₀ - ε₀ + ζ := le_trans hC6l (by linarith)
  have hcapmono : 2 ^ (l * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hC6exp (le_of_lt hn))
  have hpowpos : (0 : ℝ) ≤ 2 ^ (5 * n ^ (0.6 : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hstep1 : (T : ℝ) * (n + 1) * 2 ^ (Lc - dL)
      ≤ (4 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ (l * n) := by
    have h1 : (T : ℝ) * 2 ^ (Lc - dL) ≤ (2 * n ^ 7) * (2 ^ Fhat * 2 ^ (Lc - dL)) := by
      calc (T : ℝ) * 2 ^ (Lc - dL)
          ≤ (2 * n ^ 7 * 2 ^ Fhat) * 2 ^ (Lc - dL) :=
            mul_le_mul_of_nonneg_right hT (by positivity)
        _ = 2 * n ^ 7 * (2 ^ Fhat * 2 ^ (Lc - dL)) := by ring
    calc (T : ℝ) * (n + 1) * 2 ^ (Lc - dL) = (n + 1) * ((T : ℝ) * 2 ^ (Lc - dL)) := by ring
      _ ≤ (n + 1) * (2 * n ^ 7 * (2 ^ Fhat * 2 ^ (Lc - dL))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * n ^ 7 * (n + 1) * (2 ^ Fhat * 2 ^ (Lc - dL)) := by ring
      _ = 2 * n ^ 7 * (n + 1) * 2 ^ (Fhat + (Lc - dL)) := by rw [hjoin1]
      _ ≤ 2 * n ^ 7 * (n + 1) * 2 ^ (l * n + 5 * n ^ (0.6 : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hcancel)
              (by positivity)
      _ = 2 * n ^ 7 * (n + 1) * (2 ^ (l * n) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ (1 : ℝ)) := by
            rw [a7_two_pow_add (p := l * n) (q := 5 * n ^ (0.6 : ℝ) + 1),
              a7_two_pow_add (p := 5 * n ^ (0.6 : ℝ)) (q := 1)]
      _ = (4 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ (l * n) := by
            rw [a7_two_pow_one]; ring
  -- summand 2: the A3(4) trial factor — exponent r + 1/2 − τ₀ + ζ
  have hjoin2 : 2 ^ Fhat * 2 ^ Rc = 2 ^ (Fhat + Rc) := a7_two_pow_add (p := Fhat) (q := Rc)
  have hcancel2 : Fhat + Rc ≤ (r + 1 / 2 - τ₀ + ζ) * n + 4 * n ^ (0.6 : ℝ) + 4 := by
    have e1 : (1 / 2 - τ₀ + ζ) * n + r * n = (r + 1 / 2 - τ₀ + ζ) * n := by ring
    linarith [hA3_4, hR, e1]
  have hnum4exp : r + 1 / 2 - τ₀ + ζ ≤ τ₀ - ε₀ + ζ := by linarith
  have hcapmono2 : 2 ^ ((r + 1 / 2 - τ₀ + ζ) * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hnum4exp (le_of_lt hn))
  have hpowpos4 : (0 : ℝ) ≤ 2 ^ (4 * n ^ (0.6 : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hstep2 : (T : ℝ) * (n + 1) * 2 ^ Rc
      ≤ (32 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (4 * n ^ (0.6 : ℝ))
        * 2 ^ ((r + 1 / 2 - τ₀ + ζ) * n) := by
    have h1 : (T : ℝ) * 2 ^ Rc ≤ (2 * n ^ 7) * (2 ^ Fhat * 2 ^ Rc) := by
      calc (T : ℝ) * 2 ^ Rc ≤ (2 * n ^ 7 * 2 ^ Fhat) * 2 ^ Rc :=
            mul_le_mul_of_nonneg_right hT (by positivity)
        _ = 2 * n ^ 7 * (2 ^ Fhat * 2 ^ Rc) := by ring
    calc (T : ℝ) * (n + 1) * 2 ^ Rc = (n + 1) * ((T : ℝ) * 2 ^ Rc) := by ring
      _ ≤ (n + 1) * (2 * n ^ 7 * (2 ^ Fhat * 2 ^ Rc)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * n ^ 7 * (n + 1) * (2 ^ Fhat * 2 ^ Rc) := by ring
      _ = 2 * n ^ 7 * (n + 1) * 2 ^ (Fhat + Rc) := by rw [hjoin2]
      _ ≤ 2 * n ^ 7 * (n + 1) * 2 ^ ((r + 1 / 2 - τ₀ + ζ) * n + 4 * n ^ (0.6 : ℝ) + 4) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hcancel2)
              (by positivity)
      _ = 2 * n ^ 7 * (n + 1)
            * (2 ^ ((r + 1 / 2 - τ₀ + ζ) * n) * 2 ^ (4 * n ^ (0.6 : ℝ)) * 2 ^ (4 : ℝ)) := by
            rw [a7_two_pow_add (p := (r + 1 / 2 - τ₀ + ζ) * n)
              (q := 4 * n ^ (0.6 : ℝ) + 4),
              a7_two_pow_add (p := 4 * n ^ (0.6 : ℝ)) (q := 4)]
      _ = (32 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (4 * n ^ (0.6 : ℝ))
            * 2 ^ ((r + 1 / 2 - τ₀ + ζ) * n) := by rw [a7_two_pow_four]; ring
  -- the envelope: 4 ≤ 64, 32·2^{4q} ≤ 64·2^{5q}, sum ≤ 128P with P = n⁷(n+1)2^{5q}
  have hmono45 : 2 ^ (4 * n ^ (0.6 : ℝ)) ≤ 2 ^ (5 * n ^ (0.6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (4 * n ^ (0.6 : ℝ))])
  have hcapmonoK : 2 ^ (l * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) := hcapmono
  have hP : (T : ℝ) * (n + 1) * 2 ^ (Lc - dL)
        ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n) ∧
      (T : ℝ) * (n + 1) * 2 ^ Rc
        ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    have hPpos : (0 : ℝ) ≤ n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) := by
      nlinarith [hpowpos]
    constructor
    · calc (T : ℝ) * (n + 1) * 2 ^ (Lc - dL)
          ≤ (4 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ (l * n) := hstep1
        _ ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ))
              * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
            refine mul_le_mul (by norm_num) ?_ (by nlinarith [hpowpos]) (by nlinarith)
            · exact mul_le_mul_of_nonneg_left hcapmonoK (by nlinarith [hpowpos])
    · calc (T : ℝ) * (n + 1) * 2 ^ Rc
          ≤ (32 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (4 * n ^ (0.6 : ℝ))
              * 2 ^ ((r + 1 / 2 - τ₀ + ζ) * n) := hstep2
        _ ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ))
              * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
            have h1 : (32 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (4 * n ^ (0.6 : ℝ))
                ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) := by
              refine mul_le_mul (by norm_num) (mul_le_mul_of_nonneg_left hmono45
                (by nlinarith [hpowpos4])) (by nlinarith [hpowpos4]) (by nlinarith)
            calc (32 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (4 * n ^ (0.6 : ℝ))
                  * 2 ^ ((r + 1 / 2 - τ₀ + ζ) * n)
                ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ))
                    * 2 ^ ((r + 1 / 2 - τ₀ + ζ) * n) :=
                  mul_le_mul_of_nonneg_right h1 (by nlinarith [hpowpos4])
              _ ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ))
                    * 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
                  mul_le_mul_of_nonneg_left hcapmono2 (by nlinarith [hpowpos])
  have hcap0 : (0 : ℝ) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hsum : (T : ℝ) * (n + 1) * (2 ^ (Lc - dL) + 2 ^ Rc)
      ≤ (128 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    rw [hsplit]
    calc (T : ℝ) * (n + 1) * 2 ^ (Lc - dL) + (T : ℝ) * (n + 1) * 2 ^ Rc
        ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ)) * 2 ^ ((τ₀ - ε₀ + ζ) * n)
            + (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ))
              * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by linarith [hP.1, hP.2]
      _ = (128 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ))
            * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by ring
  exact le_trans hsum (a7_item_form hb hpoly (le_refl _))

/-! ### Item 5 — left records (the A3(3) cancel carrying (C2)) -/

/-- §5.7 item 5: the left-record total.  The per-trial expectation display
«(n+1)2^{|L|−d(L)}C(m,k)2^{1−γm}» enters as `hpert` (the 1/P′-listing
expectation transfer is the named boundary, as in M5's trial transfer); the
assembly is proved: the A3(3) cancellation `F̂ ≤ d(L) + 5n^{0.6} + 1`
collapses `2^{|L|−d(L)}`, (S5)'s `C(m,k) ≤ 2^{h(a)m}` moves to the μn scale,
and the −γμ leaf of `2^{1−γm}` comes from the sizes row `m ≥ μn − 2`
(`hm2`).  The exponent `l + (h(a)−γ)μ` discharges by (C2). -/
theorem a7_item5_left_records {b m k : ℕ} {l hA γ μ τ₀ ε₀ ζ δ n dL Fhat Lc perT : ℝ}
    (T : ℕ)
    (hS5a : (Nat.choose m k : ℝ) ≤ 2 ^ (hA * (m : ℝ))) (hAnn : 0 ≤ hA) (hγnn : 0 ≤ γ)
    (hA3_3 : Fhat ≤ dL + 5 * n ^ (0.6 : ℝ) + 1)
    (hL : Lc ≤ l * n)
    (hT : (T : ℝ) ≤ 2 * n ^ 7 * 2 ^ Fhat)
    (hm : (m : ℝ) ≤ μ * n) (hm2 : μ * n - 2 ≤ (m : ℝ))
    (hC2 : l + (hA - γ) * μ ≤ τ₀ - ε₀) (hζ : 0 ≤ ζ) (hn : 0 ≤ n)
    (hpert : perT ≤ (n + 1) * 2 ^ (Lc - dL) * (Nat.choose m k : ℝ) * 2 ^ (1 - γ * (m : ℝ)))
    (hpoly : (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ) + 2 * γ) ≤ 2 ^ δ)
    (hb : 0 ≤ b) :
    (T : ℝ) * perT ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  -- the exponent bookkeeping: F̂ + (Lc−dL) + h(a)·m + (1−γm) ≤ (l+(h(a)−γ)μ)n + 5q + 2 + 2γ
  have hAm : hA * (m : ℝ) ≤ hA * μ * n := a7_scale_mono hAnn hm hn
  have hγm : 1 - γ * (m : ℝ) ≤ 1 - (γ * μ * n - 2 * γ) := by
    have hge : γ * (μ * n - 2) ≤ γ * (m : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) hγnn
    linarith
  have hexpsum : Fhat + (Lc - dL) + (hA * (m : ℝ) + (1 - γ * (m : ℝ)))
      ≤ (l + (hA - γ) * μ) * n + 5 * n ^ (0.6 : ℝ) + 2 + 2 * γ := by
    have e1 : dL + 5 * n ^ (0.6 : ℝ) + 1 + (Lc - dL) = Lc + 5 * n ^ (0.6 : ℝ) + 1 := by ring
    have e2 : (l + (hA - γ) * μ) * n = l * n + hA * μ * n - γ * μ * n := by ring
    linarith [hA3_3, hL, hAm, hγm, e1, e2]
  have hjoin : 2 ^ Fhat * 2 ^ (Lc - dL) * 2 ^ (hA * (m : ℝ)) * 2 ^ (1 - γ * (m : ℝ))
      = 2 ^ (Fhat + (Lc - dL) + (hA * (m : ℝ) + (1 - γ * (m : ℝ)))) := by
    rw [a7_two_pow_add (p := Fhat) (q := Lc - dL),
      a7_two_pow_add (p := Fhat + (Lc - dL)) (q := hA * (m : ℝ)),
      a7_two_pow_add (p := Fhat + (Lc - dL) + hA * (m : ℝ)) (q := 1 - γ * (m : ℝ))]
  have hC2exp : l + (hA - γ) * μ ≤ τ₀ - ε₀ + ζ := le_trans hC2 (by linarith)
  have hcapmono : 2 ^ ((l + (hA - γ) * μ) * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hC2exp (le_of_lt hn))
  have hsplit : 2 ^ ((l + (hA - γ) * μ) * n + 5 * n ^ (0.6 : ℝ) + 2 + 2 * γ)
      = 4 * 2 ^ ((l + (hA - γ) * μ) * n) * 2 ^ (5 * n ^ (0.6 : ℝ) + 2 * γ) := by
    rw [a7_two_pow_add (p := (l + (hA - γ) * μ) * n) (q := 5 * n ^ (0.6 : ℝ) + 2 + 2 * γ),
      a7_two_pow_add (p := 5 * n ^ (0.6 : ℝ)) (q := 2 + 2 * γ), a7_two_pow_two]
    ring
  have hpowpos : (0 : ℝ) ≤ 2 ^ (5 * n ^ (0.6 : ℝ) + 2 * γ) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hkey : (T : ℝ) * perT
      ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ) + 2 * γ)
        * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
    have h1 : (T : ℝ) * 2 ^ Fhat * ((n + 1) * 2 ^ (Lc - dL) * (Nat.choose m k : ℝ)
        * 2 ^ (1 - γ * (m : ℝ)))
        ≤ (2 * n ^ 7) * ((n + 1) * (2 ^ Fhat * 2 ^ (Lc - dL) * 2 ^ (hA * (m : ℝ))
          * 2 ^ (1 - γ * (m : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left hS5a (by positivity)
    calc (T : ℝ) * perT
        ≤ (T : ℝ) * 2 ^ Fhat * ((n + 1) * 2 ^ (Lc - dL) * (Nat.choose m k : ℝ)
            * 2 ^ (1 - γ * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT (by positivity))
            (by positivity)
      _ ≤ 2 * n ^ 7 * ((n + 1) * (2 ^ Fhat * 2 ^ (Lc - dL) * 2 ^ (hA * (m : ℝ))
            * 2 ^ (1 - γ * (m : ℝ)))) := h1
      _ = 2 * n ^ 7 * (n + 1) * 2 ^ (Fhat + (Lc - dL) + (hA * (m : ℝ)
            + (1 - γ * (m : ℝ)))) := by rw [hjoin]; ring
      _ ≤ 2 * n ^ 7 * (n + 1) * 2 ^ ((l + (hA - γ) * μ) * n + 5 * n ^ (0.6 : ℝ)
            + 2 + 2 * γ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexpsum)
              (by positivity)
      _ = (8 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ) + 2 * γ)
            * 2 ^ ((l + (hA - γ) * μ) * n) := by rw [hsplit]; ring
      _ ≤ (64 : ℝ) * n ^ 7 * (n + 1) * 2 ^ (5 * n ^ (0.6 : ℝ) + 2 * γ)
            * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
            refine mul_le_mul (by norm_num) ?_ (by nlinarith [hpowpos]) (by nlinarith)
            · exact mul_le_mul_of_nonneg_left hcapmono (by nlinarith [hpowpos])
  exact le_trans hkey (a7_item_form hb hpoly (le_refl _))

/-! ### Item 6 — right class records (the A3(2) d(M)-cancel + the μn mop-up) -/

/-- §5.7 item 6: the right-record total.  The first summand is the per-trial
expectation display «(n+1)2^{|R|}(2m+1)2^{m−d(M)}2^{1−γm}» (`hpert6`; the
expectation transfer is the named boundary) with the A3(2) cancellation
`F̂ ≤ d(M) + 3n^{0.6} + 1` collapsing `2^{m−d(M)}` into the (C3) exponent
`r + (1−γ)μ` (the −γμ leaf via the sizes row `m ≥ μn − 2`) — proved.  The
second summand is the paper's «2^{μn+O(n^{0.6})}» mop-up for the
(2m+1)2^{m−d(M)} class handling, taken display-verbatim (`hS6b`): the paper
does not display its T-factor pairing, so the mop-up's internal split stays
at the boundary.  The discharges are (C3) and the §2.2 numeric
`hmu : μ + ε₀ ≤ τ₀` (μ = 0.473 < τ₀ ≈ 0.4877; the paper's «and μ < τ₀ − ε₀»),
flagged as instance arithmetic. -/
theorem a7_item6_right_records {b m : ℕ} {r γ μ τ₀ ε₀ ζ δ n dM Fhat Rc mdM perT S6b : ℝ}
    (T : ℕ)
    (hA3_2 : Fhat ≤ dM + 3 * n ^ (0.6 : ℝ) + 1)
    (hR : Rc ≤ r * n + 3) (hmdM : mdM ≤ (m : ℝ)) (hγnn : 0 ≤ γ)
    (hm : (m : ℝ) ≤ μ * n) (hm2 : μ * n - 2 ≤ (m : ℝ))
    (hpert6 : perT ≤ (n + 1) * 2 ^ Rc * (2 * (m : ℝ) + 1) * 2 ^ mdM * 2 ^ (1 - γ * (m : ℝ)))
    (hT : (T : ℝ) ≤ 2 * n ^ 7 * 2 ^ Fhat)
    (hC3 : r + (1 - γ) * μ ≤ τ₀ - ε₀) (hmu : μ + ε₀ ≤ τ₀) (hζ : 0 ≤ ζ) (hn : 0 ≤ n)
    (hpoly : (256 : ℝ) * n ^ 7 * (n + 1) * (2 * (m : ℝ) + 1)
      * 2 ^ (3 * n ^ (0.6 : ℝ) + 5 + 2 * γ) ≤ 2 ^ δ)
    (hb : 0 ≤ b) (hS6b : S6b ≤ 2 ^ (μ * n + δ)) :
    (T : ℝ) * perT + S6b ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + (δ + 1)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  -- first summand: the A3(2) cancel — the −γμ leaf via the sizes row m ≥ μn − 2
  have hγm : 1 - γ * (m : ℝ) ≤ 1 - (γ * μ * n - 2 * γ) := by
    have hge : γ * (μ * n - 2) ≤ γ * (m : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) hγnn
    linarith
  have hcancel : Fhat + (Rc + (mdM + (1 - γ * (m : ℝ))))
      ≤ (r + (1 - γ) * μ) * n + 3 * n ^ (0.6 : ℝ) + 5 + 2 * γ := by
    have e1 : (r + (1 - γ) * μ) * n = r * n + μ * n - γ * μ * n := by ring
    linarith [hA3_2, hR, hmdM, hγm, hm, e1]
  have hjoin : 2 ^ Fhat * 2 ^ Rc * 2 ^ mdM * 2 ^ (1 - γ * (m : ℝ))
      = 2 ^ (Fhat + (Rc + (mdM + (1 - γ * (m : ℝ))))) := by
    rw [a7_two_pow_add (p := Fhat) (q := Rc),
      a7_two_pow_add (p := Fhat + Rc) (q := mdM),
      a7_two_pow_add (p := Fhat + Rc + mdM) (q := 1 - γ * (m : ℝ))]
  have hC3exp : r + (1 - γ) * μ ≤ τ₀ - ε₀ + ζ := le_trans hC3 (by linarith)
  have hcapmono : 2 ^ ((r + (1 - γ) * μ) * n) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hC3exp (le_of_lt hn))
  have hsplit : 2 ^ ((r + (1 - γ) * μ) * n + 3 * n ^ (0.6 : ℝ) + 5 + 2 * γ)
      = 32 * 2 ^ ((r + (1 - γ) * μ) * n) * 2 ^ (3 * n ^ (0.6 : ℝ) + 2 * γ) := by
    rw [a7_two_pow_add (p := (r + (1 - γ) * μ) * n) (q := 3 * n ^ (0.6 : ℝ) + 5 + 2 * γ),
      a7_two_pow_add (p := 3 * n ^ (0.6 : ℝ)) (q := 5 + 2 * γ), a7_two_pow_five]
    ring
  have hpowpos : (0 : ℝ) ≤ 2 ^ (3 * n ^ (0.6 : ℝ) + 2 * γ) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have s1 : (T : ℝ) * perT ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := by
    have h1 : (T : ℝ) * 2 ^ Fhat * ((n + 1) * 2 ^ Rc * (2 * (m : ℝ) + 1) * 2 ^ mdM
        * 2 ^ (1 - γ * (m : ℝ)))
        ≤ (2 * n ^ 7) * ((n + 1) * (2 * (m : ℝ) + 1)
          * (2 ^ Fhat * 2 ^ Rc * 2 ^ mdM * 2 ^ (1 - γ * (m : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact le_refl _
    have hkey : (T : ℝ) * perT
        ≤ (256 : ℝ) * n ^ 7 * (n + 1) * (2 * (m : ℝ) + 1)
          * 2 ^ (3 * n ^ (0.6 : ℝ) + 5 + 2 * γ) * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
      calc (T : ℝ) * perT
          ≤ (T : ℝ) * 2 ^ Fhat * ((n + 1) * 2 ^ Rc * (2 * (m : ℝ) + 1) * 2 ^ mdM
              * 2 ^ (1 - γ * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT (by positivity))
              (by positivity)
        _ ≤ 2 * n ^ 7 * ((n + 1) * (2 * (m : ℝ) + 1)
              * (2 ^ Fhat * 2 ^ Rc * 2 ^ mdM * 2 ^ (1 - γ * (m : ℝ)))) := h1
        _ = 2 * n ^ 7 * (n + 1) * (2 * (m : ℝ) + 1) * 2 ^ (Fhat + (Rc + (mdM
              + (1 - γ * (m : ℝ))))) := by rw [hjoin]; ring
        _ ≤ 2 * n ^ 7 * (n + 1) * (2 * (m : ℝ) + 1) * 2 ^ ((r + (1 - γ) * μ) * n
              + 3 * n ^ (0.6 : ℝ) + 5 + 2 * γ) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hcancel)
                (by positivity)
        _ = (64 : ℝ) * n ^ 7 * (n + 1) * (2 * (m : ℝ) + 1) * 2 ^ (3 * n ^ (0.6 : ℝ) + 2 * γ)
              * 2 ^ ((r + (1 - γ) * μ) * n) := by rw [hsplit]; ring
        _ ≤ (256 : ℝ) * n ^ 7 * (n + 1) * (2 * (m : ℝ) + 1)
              * 2 ^ (3 * n ^ (0.6 : ℝ) + 5 + 2 * γ) * 2 ^ ((τ₀ - ε₀ + ζ) * n) := by
              refine mul_le_mul (by norm_num) ?_ (by nlinarith [hpowpos]) (by nlinarith)
              · refine mul_le_mul_of_nonneg_left ?_ (by nlinarith [hpowpos])
                exact mul_le_mul_of_nonneg_left hcapmono (by nlinarith [hpowpos])
    exact le_trans hkey (a7_item_form hb hpoly (le_refl _))
  -- second summand: the display-verbatim mop-up, discharged by the μ numeric
  have hmuexp : μ ≤ τ₀ - ε₀ + ζ := by linarith
  have s2 : S6b ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := by
    have hform : 2 ^ (μ * n + δ) = 2 ^ δ * 2 ^ (μ * n) :=
      (a7_two_pow_add (p := μ * n) (q := δ)).symm
    calc S6b ≤ 2 ^ (μ * n + δ) := hS6b
      _ = 2 ^ δ * 2 ^ (μ * n) := hform
      _ ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) := a7_item_form hb (le_refl _) hmuexp
  -- the pair sums within (b+2)·2^{K·n+(δ+1)} — the second δ absorbs the 2
  have htwo : (2 : ℝ) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ)
      = 2 ^ ((τ₀ - ε₀ + ζ) * n + (δ + 1)) := by
    have h1 : (2 : ℝ) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ)
        = 2 ^ (1 + ((τ₀ - ε₀ + ζ) * n + δ)) := by
      rw [← a7_two_pow_add (p := 1) (q := (τ₀ - ε₀ + ζ) * n + δ), a7_two_pow_one]
    rw [h1]
    congr 1
    ring
  have hcap0 : (0 : ℝ) ≤ 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  calc (T : ℝ) * perT + S6b
      ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) + (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ) :=
        add_le_add s1 s2
    _ = (2 : ℝ) * ((b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ)) := by ring
    _ ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + (δ + 1)) := by
        have hb2 : (0 : ℝ) ≤ b + 2 := by linarith
        rw [htwo]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_of_lt h2) hb2) hb2

/-! ### Item 8 — matching, dictionaries and output (the exec-side mop-up) -/

/-- §5.7's eighth category («Matching, dictionaries and output: polynomial
work for each left record, each class record, each visited tuple and each
dictionary key») — the exec-side D7 boundary: the count itself is the
algorithm and enters as the parameter `S8`; the ledger step is its absorption
into the cap (the paper's «polynomial factors go into 2^{O(n^{0.6})}»). -/
theorem a7_item8_poly {b K n δ : ℝ} (hb : 0 ≤ b) (S8 : ℝ) (hpoly : S8 ≤ 2 ^ δ) :
    S8 ≤ (b + 2) * 2 ^ (K * n + δ) := by
  have h0 : (0 : ℝ) * n = 0 := by ring
  have h := a7_item_form (b := b) (K := K) (exp := 0) (δ := δ) (poly := S8) (n := n) hb
    hpoly (le_refl 0)
  rw [h0, Real.rpow_zero, mul_one] at h
  exact h

/-! ### The ledger — §5.7's closing line -/

/-- Lemma A7's closing line: the seven-step ledger assembled — seven items
each within `(b+2)·2^{(τ₀−ε₀+ζ)n+δ}` sum to `(b+2)·2^{(τ₀−ε₀+ζ)n+(δ+3)}` —
the paper's «Every item is at most (b+2) 2^{(τ₀−ε₀+ζ)n+O(n^{0.6})}» with the
O(n^{0.6}) explicit as δ+3.  Consumes B5's proved `a7_envelope`
(Proofs/Presearch.lean): the 7 ≤ 2³ absorption. -/
theorem a7_expected_work {b τ₀ ε₀ ζ n δ : ℝ} (hb : 0 ≤ b)
    (hK : 0 ≤ (τ₀ - ε₀ + ζ) * n + δ)
    (S : ℕ → ℝ)
    (hitem : ∀ i ∈ Finset.range 7, S i ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + δ)) :
    ∑ i ∈ Finset.range 7, S i ≤ (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3)) := by
  have h := a7_envelope hb hK S hitem
  calc ∑ i ∈ Finset.range 7, S i ≤ (b + 2) * 2 ^ (((τ₀ - ε₀ + ζ) * n + δ) + 3) := h
    _ = (b + 2) * 2 ^ ((τ₀ - ε₀ + ζ) * n + (δ + 3)) := by
        rw [show ((τ₀ - ε₀ + ζ) * n + δ) + 3 = (τ₀ - ε₀ + ζ) * n + (δ + 3) from by ring]

end SubsetSumL25
