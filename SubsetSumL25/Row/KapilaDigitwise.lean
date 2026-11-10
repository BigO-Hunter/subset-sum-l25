/-
`KapilaWide`'s residual (i), **re-specified as the digitwise comparison**.

`KapilaWide` proved the obstruction and it is not a missing lemma:
`numAt_not_word` shows a stride-`k` read's numerator exceeds `2^w`, so «the loop's
per-iteration read becomes the k-word summing read» cannot be implemented in the
`BitVec w` state at all.  Its §W3 named the two shapes that can carry the wide
test — (a) a top-down **digitwise** comparison, (b) a multi-word output block with
its own carry chain — and left (i) as "a comparison re-shaping, not a read
widening".  This module is (a), finished as far as the arithmetic goes: the
**decision lemma**, plus the shape of the program segment that would implement it.
The segment's correctness proof is deliberately not here (§D7 states what it must
show and why the arithmetic had to come first).

## §D1 — the exact decision predicate, stated before it is decided

§6.2 carries the estimates at `F = fracBits` fractional bits, so a payload word
`x` is worth `x / 2^F` and §7 step 7's `1/2` test is the **integer** statement

  `2^(F-1) ≤ |numV − numA|`,  `numV = numAt w f addrV stride`,  `F ≥ 1`,

because `|V̂ − Â| = |numV − numA| / 2^F` and the `1/2` threshold is the single bit
`F−1`.  `halfTest_iff_wordDiff` is that equivalence, derived from the landed
`hitWord_eq_ratTest` (`h = 2^(F−1)`) and `hitWord_eq_one_iff` rather than
re-proved, so the predicate here *is* the predicate the landed exit folds use.

**Where the walk starts is not the top digit — that is what stating the predicate
first forces.**  The `1/2` bit sits at bit `F−1`, i.e. inside digit
`p = (F−1)/w` at bit `r = (F−1) mod w`, not at the top digit `stride−1`.  With
`F ≤ w·stride` (so `payloadStride_mul_spec`'s `+ 1` carry word is the headroom
above the scale) the digits *above* `p` are the carry word and are zero for a
payload that fits the scale.  Hence the walk reads **one digit from each side** at
`p`, and only when those differ by exactly `2^r` does it descend into a top-down
walk over the low digits (`cmpDigitsFrom`).  A walk that started at `stride−1`
and compared digit-by-digit with a first-difference rule would be **wrong**: at
`|δ| = 1` on the top digit the difference can still be as small as `1`, far below
`2^(F−1)`.  The correction is in the predicate, and it is the reason (i) is
"re-specify" rather than "widen".

The scale-fit hypothesis (`numV < 2^F`, `numA < 2^F`) is the paper's own regime —
an estimate is a fraction of the complex square sum, `V̂ ∈ [0,1)`.  It is named
(`hVb`, `hAb`) rather than assumed silently: without it one more digit is in play
above `p` and the walk's first stage becomes a comparison of the high digit
*blocks* against `2^r`, which is the same lemma one level up.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaLoop
import SubsetSumL25.Row.KapilaEstimate
import SubsetSumL25.Row.KapilaWide

set_option maxHeartbeats 1600000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### §D1 — the predicate, and the ℚ ↔ integer bridge

The predicate is not new mathematics: it is `hitWord_eq_ratTest`'s own inequality,
which the landed exit folds already test.  What the walk needs is its integer
form, `2^(F-1) ≤ |numV − numA|`, so the two are tied here once. -/

/-- **The `1/2` test is an integer comparison.**  With `h = 2^(F−1)` and both
operands at `F` fractional bits, §7 step 7's test is `2^(F−1) ≤ |V − A|` — no
rounding, no second denominator.  Derived from the landed `hitWord_eq_ratTest`
composed with `hitWord_eq_one_iff`, so the predicate the walk decides is literally
the predicate `wideExit_eq_binSum` folds. -/
theorem halfTest_iff_wordDiff {F : Nat} (hF : 1 ≤ F) (V A : Nat) :
    ((1 / 2 : ℚ) ≤ |(V : ℚ) / (2 : ℚ) ^ F - (A : ℚ) / (2 : ℚ) ^ F|)
      ↔ 2 ^ (F - 1) ≤ wordDiff V A :=
  (hitWord_eq_ratTest hF V A).symm.trans (hitWord_eq_one_iff Nat.one_le_two_pow)

/-- **The reader over the one shared scale is the place value at an address.**
The `placeValue` case is landed (`placeValue_eq_scale_numAt`); this is the same
statement for the address-indexed read the carry chain and the walk both use. -/
theorem placeValueAt_eq_scale_numAt {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (addr stride fracBits : Nat) :
    placeValueAt (memOf w f) addr stride fracBits
      = (numAt w f addr stride : ℚ) / (2 : ℚ) ^ fracBits := by
  have h := numAt_eq_placeValueAt_scale f hfit addr stride fracBits
  rw [eq_div_iff (ne_of_gt (by positivity : (0 : ℚ) < (2 : ℚ) ^ fracBits))]
  exact h.symm

/-! ### §D2 — the two bounds the walk consumes

`numAt_lt_pow` is the digit bound (`stride` digits of `w` bits hold less than
`2^(w·stride)`), and `numAt_eq_of_lt` is the reason a scale-fitting numerator has
zeros above digit `p`: **a read that is below `2^(w·m)` cannot have a nonzero
digit at position `≥ m`**, so the whole block collapses to its first `m` digits.
`numAt_split` is the consequence the walk is built on — the reader *is* one digit
at place `p` plus a low read, and that is `sum_base_digits`' exactness seen from
the top instead of from the bottom. -/

/-- **`n` digits of `w` bits hold less than `2^(w·n)`.**  Stated with `+ 1` so the
induction never touches truncated subtraction. -/
theorem numAt_add_one_le (w : Nat) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (addr n : Nat) :
    numAt w f addr n + 1 ≤ 2 ^ (w * n) := by
  induction n with
  | zero => simp [numAt]
  | succ m ih =>
    have hf : f (addr + m) + 1 ≤ 2 ^ w := hfit (addr + m)
    rw [numAt_succ, Nat.mul_succ, Nat.pow_add]
    calc numAt w f addr m + f (addr + m) * 2 ^ (w * m) + 1
        ≤ (numAt w f addr m + 1) + f (addr + m) * 2 ^ (w * m) := by omega
      _ ≤ 2 ^ (w * m) + f (addr + m) * 2 ^ (w * m) := Nat.add_le_add_right ih _
      _ = (f (addr + m) + 1) * 2 ^ (w * m) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * m) := Nat.mul_le_mul_right _ hf
      _ = 2 ^ (w * m) * 2 ^ w := Nat.mul_comm _ _

/-- The digit bound, in the strict form the comparisons want. -/
theorem numAt_lt_pow (w : Nat) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (addr n : Nat) :
    numAt w f addr n < 2 ^ (w * n) :=
  Nat.lt_of_succ_le (numAt_add_one_le w f hfit addr n)

/-- **A read below `2^(w·m)` has no digits above `m`.**  So it *is* its own
`m`-digit prefix — the collapse that puts the whole block inside digit `p`. -/
theorem numAt_eq_of_lt {w : Nat} (f : Nat → Nat) (addr : Nat) :
    ∀ (m stride : Nat), m ≤ stride → numAt w f addr stride < 2 ^ (w * m) →
      numAt w f addr stride = numAt w f addr m := by
  intro m stride
  induction stride with
  | zero =>
    intro hm _
    have hm0 : m = 0 := by omega
    subst hm0
    rfl
  | succ k ih =>
    intro hm hlt
    rcases Nat.eq_or_lt_of_le hm with heq | hltm
    · rw [← heq]
    · have hmk : m ≤ k := by omega
      have hzk : f (addr + k) = 0 := by
        by_contra hne
        have hge1 : 1 ≤ f (addr + k) := Nat.one_le_iff_ne_zero.mpr hne
        have h1 : 2 ^ (w * k) ≤ f (addr + k) * 2 ^ (w * k) := by
          calc 2 ^ (w * k) = 1 * 2 ^ (w * k) := (one_mul _).symm
            _ ≤ f (addr + k) * 2 ^ (w * k) := Nat.mul_le_mul_right _ hge1
        have h2 : 2 ^ (w * m) ≤ 2 ^ (w * k) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hmk)
        rw [numAt_succ] at hlt
        omega
      have hstep : numAt w f addr (k + 1) = numAt w f addr k := by
        rw [numAt_succ, hzk, Nat.zero_mul, Nat.add_zero]
      rw [hstep]
      exact ih hmk (by rw [hstep] at hlt; exact hlt)

/-- **The reader splits at digit `p`.**  Below `2^(w·(p+1))` the block is exactly
its digit at `p` times `2^(w·p)` plus the low `p`-digit read — the top-down
counterpart of the carry chain's `placeValueAt_succ`. -/
theorem numAt_split {w : Nat} (f : Nat → Nat) {addr stride p : Nat} (hp : p + 1 ≤ stride)
    (h : numAt w f addr stride < 2 ^ (w * (p + 1))) :
    numAt w f addr stride = f (addr + p) * 2 ^ (w * p) + numAt w f addr p := by
  have h1 : numAt w f addr stride = numAt w f addr (p + 1) :=
    numAt_eq_of_lt f addr (p + 1) stride hp h
  rw [h1, numAt_succ, Nat.add_comm]

/-! ### §D3 — the digit comparison, and the low-digit walk

`cmpDigitsFrom` is the top-down walk over the low digits: at each step it reads the
digit pair at the *next lower* address, and an equal pair defers to the walk
below it.  Its content is one arithmetic fact — comparing two numbers whose low
parts fit below `P` is comparing their quotients, and on equal quotients their
remainders (`mul_add_le_iff`).  That lemma is the walk's whole mechanism: no cell
ever holds a sum of two digits. -/

/-- **Comparing at digit granularity.**  If the two low parts are below `P`, then
`Y + b·P ≤ X + a·P` is decided by the high digits `b, a` and, only on `b = a`, by
the low parts.  This is the step rule of the walk — and of the *comparison*, not
of a subtraction: nothing here bounds `a` and `b` by `P`, so they may be any
digits the caller reads. -/
theorem mul_add_le_iff {P X Y a b : Nat} (hX : X < P) (hY : Y < P) :
    (Y + b * P ≤ X + a * P) ↔ (b < a ∨ (b = a ∧ Y ≤ X)) := by
  constructor
  · intro h
    have hba : b ≤ a := by
      by_contra hc
      have hab : a < b := by omega
      have h1 : a + 1 ≤ b := hab
      have h2 : (a + 1) * P ≤ b * P := Nat.mul_le_mul_right P h1
      rw [Nat.succ_mul] at h2
      omega
    rcases Nat.lt_or_eq_of_le hba with hlt | heq
    · exact Or.inl hlt
    · have hYX : Y ≤ X := by
        have h' := h
        rw [heq] at h'
        omega
      exact Or.inr ⟨heq, hYX⟩
  · rintro (hlt | ⟨heq, hYX⟩)
    · have h1 : b + 1 ≤ a := hlt
      have h2 : (b + 1) * P ≤ a * P := Nat.mul_le_mul_right P h1
      rw [Nat.succ_mul] at h2
      omega
    · subst heq
      omega

/-- **The low-digit walk.**  Reads the digit pair at `addrV + n` and `addrA + n`
for `n` descending from `stride-1` to `0`, and answers `true` iff the V-side low
block is at least the A-side one.  An equal pair defers to the walk below; the
first difference decides.  No accumulator: the state is the two digits just read. -/
def cmpDigitsFrom (f g : Nat → Nat) (addrV addrA : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    if f (addrV + n) = g (addrA + n) then cmpDigitsFrom f g addrV addrA n
    else decide (g (addrA + n) < f (addrV + n))

/-- **The walk decides the block comparison.**  `cmpDigitsFrom` returns `true`
exactly when the low block read is no smaller on the V side — i.e. it *is* the
digitwise form of `numAt w g addrA p ≤ numAt w f addrV p`, with no numerator ever
formed. -/
theorem cmpDigitsFrom_iff {w : Nat} (f g : Nat → Nat) (hf : ∀ z, f z < 2 ^ w)
    (hg : ∀ z, g z < 2 ^ w) (addrV addrA : Nat) :
    ∀ n, cmpDigitsFrom f g addrV addrA n = true
      ↔ numAt w g addrA n ≤ numAt w f addrV n := by
  intro n
  induction n with
  | zero => simp [cmpDigitsFrom, numAt]
  | succ m ih =>
    have hltV := numAt_lt_pow w f hf addrV m
    have hltA := numAt_lt_pow w g hg addrA m
    have hkey := mul_add_le_iff (P := 2 ^ (w * m)) (X := numAt w f addrV m)
      (Y := numAt w g addrA m) (a := f (addrV + m)) (b := g (addrA + m)) hltV hltA
    rw [cmpDigitsFrom, numAt_succ, numAt_succ]
    by_cases hc : f (addrV + m) = g (addrA + m)
    · rw [if_pos hc, ih]
      omega
    · have hfg : g (addrA + m) ≠ f (addrV + m) := fun hh => hc hh.symm
      rw [if_neg hc, decide_eq_true_iff, hkey]
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | ⟨he, _⟩)
        · exact h
        · exact absurd he.symm hc

/-! ### §D4 — the decision lemma

`digHalf` is the walk's first stage: one digit from each side at position `p`, the
position where the `1/2` bit lives, compared against `2^r`; the four outcomes are
*hit*, *miss*, and the two exact ties, which are the only cases that descend into
`cmpDigitsFrom`.  The four arithmetic facts it rests on are proved separately
(`hit_of_above`, `hit_of_below`, `tie_hit_iff`, `miss_of_close`) so each is
readable on its own. -/

/-- **V's digit is more than `2^r` above A's: hit.**  The digit gap alone exceeds
the threshold, whatever the low parts do. -/
theorem hit_of_above {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P) (hAlo : Alo < P)
    (h : ap + 2 ^ r < vp) :
    T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo) := by
  have hmul : (ap + 2 ^ r + 1) * P ≤ vp * P := Nat.mul_le_mul_right P (by omega)
  have hexp : (ap + 2 ^ r + 1) * P = ap * P + T + P := by
    rw [Nat.add_mul, Nat.add_mul, one_mul, ← hT]
  have hkey : ap * P + Alo + T ≤ vp * P + Vlo := by
    have h1 : ap * P + Alo + T ≤ ap * P + T + P := by omega
    calc ap * P + Alo + T ≤ ap * P + T + P := h1
      _ = (ap + 2 ^ r + 1) * P := hexp.symm
      _ ≤ vp * P := hmul
      _ ≤ vp * P + Vlo := Nat.le_add_right _ _
  rw [wordDiff_of_ge (by omega)]
  omega

/-- **A's digit is more than `2^r` above V's: hit**, by the same argument on the
other side. -/
theorem hit_of_below {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P) (hVlo : Vlo < P)
    (h : vp + 2 ^ r < ap) :
    T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo) := by
  have hmul : (vp + 2 ^ r + 1) * P ≤ ap * P := Nat.mul_le_mul_right P (by omega)
  have hexp : (vp + 2 ^ r + 1) * P = vp * P + T + P := by
    rw [Nat.add_mul, Nat.add_mul, one_mul, ← hT]
  have hkey : vp * P + Vlo + T ≤ ap * P + Alo := by
    have h1 : vp * P + Vlo + T ≤ vp * P + T + P := by omega
    calc vp * P + Vlo + T ≤ vp * P + T + P := h1
      _ = (vp + 2 ^ r + 1) * P := hexp.symm
      _ ≤ ap * P := hmul
      _ ≤ ap * P + Alo := Nat.le_add_right _ _
  rw [wordDiff_of_lt (by omega)]
  omega

/-- **V's digit is exactly `2^r` above A's.**  Then the difference is `T` plus the
low-part difference, whose magnitude is below `P ≤ T` — so the sign is fixed and
the test is exactly `Alo ≤ Vlo`: the tie is decided by the low walk. -/
theorem tie_hit_iff {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P)
    (_hVlo : Vlo < P) (hAlo : Alo < P) (h : vp = ap + 2 ^ r) :
    (T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo)) ↔ Alo ≤ Vlo := by
  subst h
  have hPT : P ≤ T := by
    rw [hT]
    calc P = 1 * P := (one_mul P).symm
      _ ≤ 2 ^ r * P := Nat.mul_le_mul_right P Nat.one_le_two_pow
  have hNV : (ap + 2 ^ r) * P + Vlo = ap * P + T + Vlo := by
    rw [Nat.add_mul, ← hT]
  rw [hNV, wordDiff_of_ge (by omega)]
  omega

/-- **A's digit is exactly `2^r` above V's**: the mirror tie, decided by the low
walk with the two sides exchanged (`cmpDigitsFrom g f`). -/
theorem tieA_hit_iff {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P)
    (hVlo : Vlo < P) (_hAlo : Alo < P) (h : ap = vp + 2 ^ r) :
    (T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo)) ↔ Vlo ≤ Alo := by
  subst h
  have hPT : P ≤ T := by
    rw [hT]
    calc P = 1 * P := (one_mul P).symm
      _ ≤ 2 ^ r * P := Nat.mul_le_mul_right P Nat.one_le_two_pow
  have hNA : (vp + 2 ^ r) * P + Alo = vp * P + T + Alo := by
    rw [Nat.add_mul, ← hT]
  rw [hNA, wordDiff_of_lt (by omega)]
  omega

/-- **Neither digit is `2^r` above the other: miss.**  The digit gap is at most
`2^r − 1`, so the whole difference is at most `(2^r−1)·P + (P−1) = T−1`, strictly
below the threshold — whatever the low parts do.  This is the branch that makes
the walk *one digit deep* in the common case. -/
theorem miss_of_close {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P)
    (hVlo : Vlo < P) (hAlo : Alo < P) (h1 : vp < ap + 2 ^ r) (h2 : ap < vp + 2 ^ r) :
    ¬ (T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo)) := by
  have h1' : vp ≤ ap + (2 ^ r - 1) := by omega
  have h2' : ap ≤ vp + (2 ^ r - 1) := by omega
  have hPle : P ≤ 2 ^ r * P := by
    calc P = 1 * P := (one_mul P).symm
      _ ≤ 2 ^ r * P := Nat.mul_le_mul_right P Nat.one_le_two_pow
  have hsub : (2 ^ r - 1) * P = 2 ^ r * P - P := by rw [Nat.sub_mul, one_mul]
  have hTeq : (2 ^ r - 1) * P + P = T := by
    rw [hsub, hT]
    omega
  have hNVle : vp * P + Vlo + 1 ≤ ap * P + Alo + T := by
    have hmul : vp * P ≤ (ap + (2 ^ r - 1)) * P := Nat.mul_le_mul_right P h1'
    have hexp : (ap + (2 ^ r - 1)) * P = ap * P + (2 ^ r - 1) * P := Nat.add_mul _ _ _
    omega
  have hNAle : ap * P + Alo + 1 ≤ vp * P + Vlo + T := by
    have hmul : ap * P ≤ (vp + (2 ^ r - 1)) * P := Nat.mul_le_mul_right P h2'
    have hexp : (vp + (2 ^ r - 1)) * P = vp * P + (2 ^ r - 1) * P := Nat.add_mul _ _ _
    omega
  have hsmall : wordDiff (vp * P + Vlo) (ap * P + Alo) + 1 ≤ T := by
    by_cases hc : vp * P + Vlo < ap * P + Alo
    · rw [wordDiff_of_lt hc]
      omega
    · rw [wordDiff_of_ge hc]
      omega
  omega

/-- **The digitwise half test.**  One digit from each side at position `p` — the
digit holding the `1/2` bit — compared against `2^r`; the two exact ties descend
into the low-digit walk, and nothing else does.  Cells touched: the two digit
reads and one add.  No numerator is formed, so `numAt_not_word`'s obstruction does
not apply: `digHalf` decides a comparison, not a value. -/
def digHalf (f g : Nat → Nat) (addrV addrA p r : Nat) : Bool :=
  if g (addrA + p) + 2 ^ r < f (addrV + p) then true
  else if f (addrV + p) + 2 ^ r < g (addrA + p) then true
  else if f (addrV + p) = g (addrA + p) + 2 ^ r then cmpDigitsFrom f g addrV addrA p
  else if g (addrA + p) = f (addrV + p) + 2 ^ r then cmpDigitsFrom g f addrA addrV p
  else false

/-- **THE DECISION LEMMA.**  For a scale-fitting stride-`k` read (`numV`,
`numA < 2^F`, `F ≥ 1`, `w ≥ 1`, and a block long enough to contain digit `p`),
the digitwise walk decides §7 step 7's integer test — **without materialising
either numerator**.  The walk reads one digit from each side and, on an exact tie,
walks the low digits; the four arithmetic facts above are the whole proof. -/
theorem digHalf_eq_threshold {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F) (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {addrV addrA stride : Nat}
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f addrV stride < 2 ^ F) (hAb : numAt w g addrA stride < 2 ^ F) :
    (digHalf f g addrV addrA ((F - 1) / w) ((F - 1) % w) = true)
      ↔ 2 ^ (F - 1) ≤ wordDiff (numAt w f addrV stride) (numAt w g addrA stride) := by
  have hrw : (F - 1) % w < w := Nat.mod_lt _ (by omega)
  have hFr : w * ((F - 1) / w) + (F - 1) % w = F - 1 := Nat.div_add_mod (F - 1) w
  have hWs : w * ((F - 1) / w + 1) = w * ((F - 1) / w) + w := Nat.mul_succ w _
  have hFle : F ≤ w * ((F - 1) / w + 1) := by omega
  have hV2 : numAt w f addrV stride < 2 ^ (w * ((F - 1) / w + 1)) :=
    lt_of_lt_of_le hVb (Nat.pow_le_pow_right (by norm_num) hFle)
  have hA2 : numAt w g addrA stride < 2 ^ (w * ((F - 1) / w + 1)) :=
    lt_of_lt_of_le hAb (Nat.pow_le_pow_right (by norm_num) hFle)
  have hVs := numAt_split f hp hV2
  have hAs := numAt_split g hp hA2
  have hVlo : numAt w f addrV ((F - 1) / w) < 2 ^ (w * ((F - 1) / w)) :=
    numAt_lt_pow w f hf addrV _
  have hAlo : numAt w g addrA ((F - 1) / w) < 2 ^ (w * ((F - 1) / w)) :=
    numAt_lt_pow w g hg addrA _
  have hT : 2 ^ (F - 1) = 2 ^ ((F - 1) % w) * 2 ^ (w * ((F - 1) / w)) := by
    conv_lhs => rw [← hFr]
    rw [Nat.pow_add, Nat.mul_comm]
  rw [hVs, hAs, digHalf]
  by_cases h1 : g (addrA + (F - 1) / w) + 2 ^ ((F - 1) % w) < f (addrV + (F - 1) / w)
  · rw [if_pos h1]
    exact ⟨fun _ => hit_of_above hT hAlo h1, fun _ => rfl⟩
  · rw [if_neg h1]
    by_cases h2 : f (addrV + (F - 1) / w) + 2 ^ ((F - 1) % w) < g (addrA + (F - 1) / w)
    · rw [if_pos h2]
      exact ⟨fun _ => hit_of_below hT hVlo h2, fun _ => rfl⟩
    · rw [if_neg h2]
      by_cases h3 : f (addrV + (F - 1) / w) = g (addrA + (F - 1) / w) + 2 ^ ((F - 1) % w)
      · rw [if_pos h3, cmpDigitsFrom_iff f g hf hg addrV addrA ((F - 1) / w)]
        exact (tie_hit_iff hT hVlo hAlo h3).symm
      · rw [if_neg h3]
        by_cases h4 : g (addrA + (F - 1) / w) = f (addrV + (F - 1) / w) + 2 ^ ((F - 1) % w)
        · rw [if_pos h4, cmpDigitsFrom_iff g f hg hf addrA addrV ((F - 1) / w)]
          exact (tieA_hit_iff hT hVlo hAlo h4).symm
        · rw [if_neg h4]
          have hlt1 : f (addrV + (F - 1) / w) < g (addrA + (F - 1) / w) + 2 ^ ((F - 1) % w) :=
            by omega
          have hlt2 : g (addrA + (F - 1) / w) < f (addrV + (F - 1) / w) + 2 ^ ((F - 1) % w) :=
            by omega
          refine ⟨fun hc => (Bool.false_ne_true hc).elim,
            fun hbad => (miss_of_close hT hVlo hAlo hlt1 hlt2 hbad).elim⟩

/-- **The decision lemma in §7 step 7's own vocabulary.**  `true` exactly when
`(1/2 : ℚ) ≤ |V̂ − Â|` on the two place values — the walk decides the paper's test
itself, and `halfTest_iff_wordDiff` is the bridge that makes the statement literal
rather than an integer proxy. -/
theorem digHalf_eq_ratTest {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F) (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {addrV addrA stride : Nat}
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f addrV stride < 2 ^ F) (hAb : numAt w g addrA stride < 2 ^ F) :
    (digHalf f g addrV addrA ((F - 1) / w) ((F - 1) % w) = true)
      ↔ (1 / 2 : ℚ) ≤ |placeValueAt (memOf w f) addrV stride F
          - placeValueAt (memOf w g) addrA stride F| := by
  rw [placeValueAt_eq_scale_numAt f hf, placeValueAt_eq_scale_numAt g hg,
    halfTest_iff_wordDiff hF]
  exact digHalf_eq_threshold hw hF f g hf hg hp hVb hAb

/-- **The decision lemma at estimate `s`.**  The walk on the two payload blocks
falls on §7 step 7's comparison of the estimates themselves — `placeV` and
`placeA` in the paper's own two-letter form, i.e. the objects `dAt_eq_reader`
names as `dAt`. -/
theorem digHalf_eq_placeValueTest {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F) (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {baseV baseA stride s : Nat}
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f (baseV + s * stride) stride < 2 ^ F)
    (hAb : numAt w g (baseA + s * stride) stride < 2 ^ F) :
    (digHalf f g (baseV + s * stride) (baseA + s * stride) ((F - 1) / w) ((F - 1) % w)
        = true)
      ↔ (1 / 2 : ℚ) ≤ |placeValue (memOf w f) baseV stride F s
          - placeValue (memOf w g) baseA stride F s| := by
  rw [placeValue_eq_placeValueAt, placeValue_eq_placeValueAt]
  exact digHalf_eq_ratTest hw hF f g hf hg hp hVb hAb

/-- **Spot checks, kernel-checked.**  Three concrete payloads at `w = 2`, `F = 4`
(so `p = 1`, `r = 1`, threshold `2^3 = 8`), reading `V` at address `0` and `A` at
address `10`: a decided hit (digits `3,3` vs `0,0` — `|15 − 0| = 15 ≥ 8`), a
decided miss (`3,1` vs `0,0` — `|7 − 0| = 7 < 8`), and an **exact tie at digit
`p`** (`0,2` vs `1,0` — `|8 − 1| = 7 < 8`, resolved by the low walk, which is the
only path that descends: `f 0 = 0 < 1 = g 10`, so the walk answers miss).
`decide`, not `native_decide`: the house banner admits no `Lean.ofReduceBool`. -/
theorem digHalf_spot_checks :
    digHalf (fun z => if z = 0 then 3 else if z = 1 then 3 else 0) (fun _ => 0) 0 10 1 1 = true ∧
    digHalf (fun z => if z = 0 then 3 else if z = 1 then 1 else 0) (fun _ => 0) 0 10 1 1 = false ∧
    digHalf (fun z => if z = 0 then 0 else if z = 1 then 2 else 0)
        (fun z => if z = 10 then 1 else 0) 0 10 1 1 = false := by
  decide

/-! ### §D5 — the program segment's shape, **stated**

The arithmetic above fixes what the segment has to compute; this fixes its
*shape*, in the vocabulary the row's `Instr` set speaks (`Statement.lean`: `load`,
`add`, `sub`, `rem`, `one`, `blt`).  What is stated is the skeleton and its fuel.
**What is deliberately not here is the segment proof** — that `exec` reaches the
stated cell values — because the arithmetic had to be settled first: a segment
proof against a wrong decision predicate would be a *new* `K + 3`-versus-`K + 7`
mistake wearing a loop.  The obligation it must meet is written out in this
section's docstring so the next mind inherits it exactly.

Register map (the segment's precondition, discharged by the caller):

| cell | meaning |
|---|---|
| 0 | address of V's digit `p`, advanced **down** by the walk |
| 1 | address of A's digit `p`, advanced down |
| 2 | digits still to compare |
| 3, 4 | the digit pair just read |
| 5 | scratch |
| 6 | **the verdict** (`1` = hit) |
| 7 | `0` (constant) |
| 8 | `1` (constant) |
| 9 | `2^r` (the `1/2` bit's value inside digit `p`) |
| 10 | swap scratch (the A-side tie enters the walk with the sides exchanged) |

The obligation, precisely: from that precondition and fuel `cmpSegFuel p`, the run
reaches `cont` with cell `6 = digHalf`'s verdict as a word (`1` for `true`, `0` for
`false`), touching no other cell of the caller's.  Three facts are proved below
because they are pure shape — the program's length, the fuel's linearity, and the
fuel's relation to the stride-`k` read charge; the reachability part is the
deferred segment proof. -/

/-- **The compare segment's instruction skeleton.**  Prologue `0–11` reads the two
digits at `p` and branches four ways on `2^r`; `12–15` are the two decided exits;
`16–18` swaps the pointer cells for the A-side tie; `19–28` is the low-digit walk
(`9` instructions per digit plus its terminal test).  Exits jump to `cont`. -/
def cmpSeg (cont : Nat) : List Instr :=
  [ .load 3 0                    --  0  v := [[0]]           (V's digit at p)
  , .load 4 1                    --  1  a := [[1]]           (A's digit at p)
  , .add 5 4 9                   --  2  [5] := a + 2^r
  , .blt 3 5 8                   --  3  v < a+2^r ? → 8
  , .blt 5 3 12                  --  4  a+2^r < v ? → 12      HIT
  , .add 6 7 8                   --  5  [6] := 1             (tie, V side)
  , .blt 7 8 19                  --  6  → 19                 (low walk, no swap)
  , .blt 7 8 19                  --  7  → 19                 (unreachable)
  , .add 5 3 9                   --  8  [5] := v + 2^r
  , .blt 4 5 14                  --  9  a < v+2^r ? → 14      MISS
  , .blt 5 4 12                  -- 10  v+2^r < a ? → 12      HIT
  , .blt 7 8 16                  -- 11  → 16                 (tie, A side: swap)
  , .one 6                       -- 12  [6] := 1             HIT
  , .blt 7 8 cont                -- 13  → cont
  , .rem 6 7 7                   -- 14  [6] := 0             MISS
  , .blt 7 8 cont                -- 15  → cont
  , .add 10 0 7                  -- 16  [10] := [0]
  , .add 0 1 7                   -- 17  [0] := [1]
  , .add 1 10 7                  -- 18  [1] := [10]          (exchange the sides)
  , .sub 0 0 8                   -- 19  ptrV −= 1            WALK head
  , .sub 1 1 8                   -- 20  ptrA −= 1
  , .load 3 0                    -- 21  v := [[0]]
  , .load 4 1                    -- 22  a := [[1]]
  , .blt 3 4 14                  -- 23  v < a ? → 14          MISS
  , .sub 5 3 4                   -- 24  d := v − a
  , .blt 7 5 12                  -- 25  0 < d ? → 12          HIT
  , .sub 2 2 8                   -- 26  n −= 1
  , .blt 7 2 19                  -- 27  0 < n ? → 19          (next digit)
  , .blt 7 8 12                  -- 28  → 12                   (all equal: hit)
  ]

/-- **The skeleton is a fixed program.**  Its length does not depend on the stride
— the walk's repetitiveness is a back-edge, not unrolled code, so the `Instr` list
is one constant the row's `D7.program` can name. -/
theorem cmpSeg_length (cont : Nat) : (cmpSeg cont).length = 29 := rfl

/-- **The fuel shape.**  Worst case is the A-side tie: `11` instructions to the
walk entry, the walk's `9` per digit, its terminal test, and the exit.  The
decided cases are *constant* (`7` and `8`), which is the shape's point: the walk is
`O(p)` only on an exact tie at digit `p`. -/
def cmpSegFuel (p : Nat) : Nat := 13 + 9 * p

/-- **The fuel is linear in `p`, not in `stride` squared and not exponential** —
the statement residual (iv) inherits. -/
theorem cmpSegFuel_linear (p : Nat) : cmpSegFuel p ≤ 13 * (p + 1) := by
  unfold cmpSegFuel
  omega

/-- **The decided cases cost a constant.**  Stated as the fuel at `p = 0` — the
tie can only descend when there is a digit below `p` to descend into. -/
theorem cmpSegFuel_zero : cmpSegFuel 0 = 13 := rfl

end SubsetSumL25.Row
