/-
Guard coverage for `ss/kapila 0.4877` — **where the row's arithmetic meets the
machine model**.

Two conditions meet here and are usually left implicit:

* the trusted statement's input class, `x.bits ≤ n ^ c` (polynomial-bit inputs,
  one `c` fixed at a time, `P` not allowed to see it);
* §7's own guard, `10⁶⌈log₂(b+1)⌉ ≤ n` (`guardOk`, the `decide`d `Bool` that
  routes an input to §6.3's exact meet-in-the-middle).

The row theorem charges §7's envelope only on the main branch, so the guard's
routing must be *finite*: finitely many inputs in the statement's class may take
the fallback, and every other one satisfies the guard.  That is what this module
proves, and it is purely arithmetic on `Nat.log2` — no probability, no program.

The only real ingredient is that `log₂` is eventually below `n / k` for *every*
fixed `k` (`log2_mul_le_self`, threshold `2k²`), which is the formal content of
«a polynomial-bit input is, for large `n`, inside the paper's bit-guard».
-/
import Mathlib
import SubsetSumL25.Row.KapilaAlgo

namespace SubsetSumL25.Row

/-! ### The one analysis fact -/

/-- `2·m² < 2^(2m)` for `m ≥ 4` — "polynomial below exponential" with explicit
constants, so that `2k²` can serve as an explicit threshold below. -/
theorem two_mul_sq_lt_two_pow : ∀ m : ℕ, 4 ≤ m → 2 * m ^ 2 < 2 ^ (2 * m) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : 2 * (j + 1) ^ 2 ≤ 8 * j ^ 2 := by nlinarith
    have h2 : 8 * j ^ 2 = 4 * (2 * j ^ 2) := by ring
    have h3 : 4 * (2 * j ^ 2) < 4 * (2 ^ (2 * j)) := by nlinarith
    have h4 : 4 * (2 ^ (2 * j)) = 2 ^ (2 * (j + 1)) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
      norm_num
      ring
    linarith

/-- **`log₂ n · k ≤ n` past `2k²`** — i.e. `log₂` is below `n / k` eventually,
for every fixed `k`.  Strong induction: the recursion
`log₂ n = log₂ (n/2) + 1` charges one unit per halving, and halving a number
above `4k²` leaves it above `2k²`, so the induction reaches the base window
`[2k², 4k²)` where `log₂ n ≤ 2k ≤ n/k` outright (`two_mul_sq_lt_two_pow`
supplies `4k² < 2^(2k+1)`). -/
theorem log2_mul_le_self {k : ℕ} (hk : 4 ≤ k) :
    ∀ n : ℕ, 2 * k ^ 2 ≤ n → Nat.log2 n * k ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (4 * k ^ 2) with hsmall | hbig
    · -- base window: `2k² ≤ n < 4k²`
      have hlt : Nat.log 2 n < 2 * k + 1 := by
        rw [Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) (by omega : n ≠ 0)]
        have h4 : 4 * k ^ 2 < 2 ^ (2 * k + 1) := by
          have h := two_mul_sq_lt_two_pow k hk
          calc 4 * k ^ 2 = 2 * (2 * k ^ 2) := by ring
            _ < 2 * 2 ^ (2 * k) := by nlinarith
            _ = 2 ^ (2 * k + 1) := by rw [pow_succ']
        omega
      have hlog2 : Nat.log2 n ≤ 2 * k := by
        rw [Nat.log2_eq_log_two]
        omega
      have hmul : Nat.log2 n * k ≤ (2 * k) * k := Nat.mul_le_mul_right k hlog2
      have hkk : (2 * k) * k = 2 * k ^ 2 := by ring
      omega
    · -- step: halve and recurse
      have h2n : 2 ≤ n := by nlinarith
      have hhalf : 2 * k ^ 2 ≤ n / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        nlinarith
      have ih' : Nat.log2 (n / 2) * k ≤ n / 2 := ih (n / 2) (by omega) hhalf
      have hlog : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
        rw [Nat.log2_def, if_pos h2n]
      have hkn : k ≤ n / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        nlinarith
      rw [hlog, Nat.add_mul, Nat.one_mul]
      omega

/-! ### Guard coverage -/

/-- **Guard coverage.**  For every fixed `c` there is `N` beyond which every
input the statement allows (`b ≤ n^c`) satisfies §7's bit-guard
`10⁶⌈log₂(b+1)⌉ ≤ n` — which is `guardOk n b`, since
`⌈log₂(b+1)⌉ = ⌊log₂ b⌋ + 1 = Nat.log2 b + 1` for `b ≥ 1`, and `log₂ 0 = 0`.

Why this is the row's missing link.  `SolvedInTime` quantifies over *all*
`b ≤ n^c`, but §7's algorithm is only analysed on inputs the guard admits; the
rest take §6.3's exact fallback, whose *correctness* is free
(`correctAt_of_fallback_det`) but whose *cost* is not the charged envelope.
This theorem says the uncovered set is finite in `n` for each `c`: below `N` the
fallback may fire and the finitely many `n` are absorbed into the horizon
constant exactly as `kapila_row`'s small-`n` branch absorbs them; above `N` the
guard holds, the main branch runs, and `Routines.WithinEnvelope` is the charge
that applies.  No input in the statement's class sits in an uncovered regime. -/
theorem guardOk_eventually (c : ℕ) :
    ∃ N : ℕ, ∀ n b : ℕ, N ≤ n → b ≤ n ^ c → guardOk n b := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- `c = 0`: `b ≤ 1`, so `log₂ b = 0` and the guard is `10⁶ ≤ n`
    subst hc
    refine ⟨1000000, fun n b hn hb => ?_⟩
    have hb1 : b ≤ 1 := by simpa using hb
    have hb0 : Nat.log2 b = 0 := by interval_cases b <;> rfl
    unfold guardOk
    rw [hb0]
    omega
  · -- `c ≥ 1`: `k = 4·10⁶·c`, threshold `max (2k²) (8·10⁶·(c+1))`
    set k : ℕ := 4 * 1000000 * c with hk
    have hk4 : 4 ≤ k := by omega
    refine ⟨max (2 * k ^ 2) (8 * 1000000 * (c + 1)), fun n b hn hb => ?_⟩
    have hn1 : 2 * k ^ 2 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : 8 * 1000000 * (c + 1) ≤ n := le_trans (le_max_right _ _) hn
    set A : ℕ := Nat.log2 n with hA
    -- (1) `log₂ b ≤ log₂ (n^c)`
    have hmono : Nat.log2 b ≤ Nat.log2 (n ^ c) := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right hb
    -- (2) `log₂ (n^c) ≤ c·(log₂ n + 1)`
    have hpow : Nat.log2 (n ^ c) ≤ c * (A + 1) := by
      have hlogA : Nat.log 2 n = A := by rw [← Nat.log2_eq_log_two, ← hA]
      have hnpos : 0 < n := by nlinarith
      have hlt : n < 2 ^ (A + 1) := by
        have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
        rwa [hlogA] at h
      have hlt2 : Nat.log 2 (n ^ c) < (A + 1) * c + 1 := by
        rw [Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) (by positivity : n ^ c ≠ 0)]
        calc n ^ c < (2 ^ (A + 1)) ^ c := Nat.pow_lt_pow_left hlt (by omega)
          _ = 2 ^ ((A + 1) * c) := by rw [← pow_mul]
          _ < 2 ^ ((A + 1) * c + 1) :=
              Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [Nat.log2_eq_log_two]
      have h2 := hlt2
      rw [Nat.mul_comm (A + 1) c] at h2
      omega
    rw [guardOk]
    -- (3) `10⁶·c·A ≤ n/4` and `10⁶·(c+1) ≤ n/4`, from the log bound
    have hkA : A * k ≤ n := log2_mul_le_self hk4 n hn1
    have hA4 : 1000000 * c * A ≤ n / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
      have he : 1000000 * c * A * 4 = A * k := by rw [hk]; ring
      rw [he]
      exact hkA
    have hB4 : 1000000 * (c + 1) ≤ n / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
      nlinarith
    have hdiv : n / 4 + n / 4 ≤ n := by
      have h := Nat.div_add_mod n 4
      omega
    have hlogb : Nat.log2 b ≤ c * (A + 1) := le_trans hmono hpow
    nlinarith
