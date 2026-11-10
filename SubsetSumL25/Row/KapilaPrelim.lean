/-
Proposition P's instruction text — **`prelimProg`**, and its segment agreement.

Why this file exists.  `Routines` (`SubsetSumL25.Row.KapilaAlgo`) carries six
program fields; four of them (`prelimProg`, `aliasProg`, `checksumProg` — and
`mitmProg`'s own text) were **named obligations** with no in-tree instruction
text.  `fallback_agrees_of_mitmProg` showed the `mitm` field's *shape* is
discharged by `Routines.mitm_agrees`; this file does the analogous thing for
§4's preliminary search, and it does one thing more than the `mitm` field: the
text is written here, and the agreement is **proved against that text**.

What is proved here, in order:

1. **`prelimProg`** — 17 instructions.  It is the ported shape of the snapshot's
   `prog2` prologue (`subsetsum-v2-snapshot`, `Submission/Program.lean`'s
   `prologue` / `Submission/Prog2.lean`'s `canon`/`scanB` dispatch): a
   *bootstrap* that frees a fixed register window by saving the input cells it
   needs (`saveAk`'s cursor trick, verbatim: cursor `2n` in cell 0, save `a₁`
   at `2n`, then `one 1` — safe only because `a₁` is already saved), then an
   address computation (`n`, `n+1`), then the decision.  It has no loop, so the
   whole agreement is a straight-line `exec` walk.  The in-place-input problem
   (`Statement.run` starts from `loadWords _ x.input`, so cells `1..n+1` hold
   the input and no *fixed* cell is free) is why a bootstrap is needed at all;
   the ported shape resolves it exactly as `prog2` does.
2. **`prelimSpec`** — the phase's mathematical value, an independent `ℕ`-level
   definition: «decide YES if `t = 0` or `a₁ = t`; otherwise CONTINUE».  This is
   a **sound** preliminary search — both acceptance tests are genuine witnesses
   (`prelim_sound`: `prelimSpec = some true → x.yes`) — and it never returns a
   NO decision, which is §7's «returns the correct decision or CONTINUE»
   contract with CONTINUE spelled `none`.  It is the *witness-test leg*: the
   enumeration over the remaining `2^h` candidates (Proposition 2.4's capped
   meet-in-the-middle) is the residual, named at the bottom of this file.
3. **`prelim_run`** — `run prelimProg x ρ 24 = some (failToNo (prelimSpec …))`,
   proved by a step-by-step walk over the 17 instructions with the ported
   `memOf`/`up`/`exec_*_step` calculus.
4. **`prelim_agrees_iff_run`** — the field's `failToNo` shape, *characterised*:
   it is equivalent to the `Option`-free equation above.  This matters because
   the field as written lets Lean insert a `pure`/`map some` lift, and without
   this lemma the field's content is not legible.  With it, the field is exactly
   «the segment halts with that verdict».
5. **`LeafP_of_prelim_agrees`** — the consumer: on the guard's complement, if
   `R.cost` collapses to `R.prelimCost` then `R.prelim_agrees` *is* `LeafP R
   R.prelimProg`.  That is one of the two remaining seam obligations in
   `agrees_main_iff_leaves`, discharged modulo the cost collapse.

Credit: §4/Proposition P, the cap `2^{⌈τ₀n⌉}` and the «FAIL → return NO» reading
are Base's; `prop_p_chebyshev` (B5) is the landed mathematical core.  The
bootstrap-and-scan shape is the snapshot lane's; nothing here is re-derived
where a reference exists.
-/
import Mathlib
import SubsetSumL25.Row.Statement
import SubsetSumL25.Row.KapilaRow

set_option autoImplicit true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SubsetSumL25.Row

open BigOSpeedrun.SubsetSum

/-! ### Layer 0 — the canonical memory form

Ported from `subsetsum-v2-snapshot`, `Submission/Prologue.lean` (layers 0–1):
every memory the program passes through is `memOf w f` — cell `i` holds the
word `BitVec.ofNat w (f i)` of a `ℕ`-valued state, under the standing fit
invariant `∀ i, f i < 2^w`.  Under fit each word operation implements the
corresponding `ℕ` operation, so the whole walk below is `ℕ`-arithmetic on `f`
with the `BitVec` layer eliminated. -/

/-- Memory of a `ℕ`-valued state. -/
def memOf (w : Nat) (f : Nat → Nat) : Nat → BitVec w :=
  fun i => BitVec.ofNat w (f i)

/-- Cell update on a state function. -/
def up (f : Nat → Nat) (c v : Nat) : Nat → Nat :=
  fun x => if x = c then v else f x

theorem up_eq (f : Nat → Nat) (c v : Nat) : up f c v c = v := by simp [up]

theorem up_ne {f : Nat → Nat} {c v i : Nat} (h : i ≠ c) : up f c v i = f i := by
  simp [up, h]

/-- A write of a fitting value preserves the fit invariant. -/
theorem upFit {f : Nat → Nat} {c v w : Nat} (hfit : ∀ q, f q < 2 ^ w) (hv : v < 2 ^ w) :
    ∀ q, up f c v q < 2 ^ w := by
  intro q
  by_cases h : q = c <;> simp [up, h, hfit, hv]

/-- The word of a sum is the word of the `ℕ` sum (mod arithmetic both sides). -/
theorem bv_add {w a b : Nat} :
    BitVec.ofNat w a + BitVec.ofNat w b = BitVec.ofNat w (a + b) := by
  rw [BitVec.toNat_eq, BitVec.add_def]
  simp only [BitVec.toNat_ofNat]
  exact (Nat.add_mod a b (2 ^ w)).symm

/-- The word of a right shift (the shift amount itself fits). -/
theorem bv_shr {w a s : Nat} (ha : a < 2 ^ w) (hs : s < 2 ^ w) :
    BitVec.ofNat w a >>> BitVec.ofNat w s = BitVec.ofNat w (a / 2 ^ s) := by
  rw [BitVec.toNat_eq]
  have h1 : (BitVec.ofNat w a >>> BitVec.ofNat w s).toNat
      = (a % 2 ^ w) >>> (s % 2 ^ w) := by simp
  rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hs,
    Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (by have := Nat.div_le_self a (2 ^ s); omega)).symm

/-- Comparison of `ofNat` words is comparison of the underlying `ℕ`s. -/
theorem ofNat_lt_ofNat {w x y : Nat} (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    BitVec.ofNat w x < BitVec.ofNat w y ↔ x < y := by
  rw [BitVec.lt_def]
  have e1 : (BitVec.ofNat w x).toNat = x % 2 ^ w := rfl
  have e2 : (BitVec.ofNat w y).toNat = y % 2 ^ w := rfl
  rw [e1, e2, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-! ### Layer 1 — one-instruction step lemmas (program-independent)

Each peels ONE instruction at any positive horizon; the `getD` fact enters as a
hypothesis, which the concrete program below supplies by `decide`. -/

section StepLemmas

variable {w : Nat} {P : List Instr} {ρ : Nat → BitVec w} {S pc r : Nat} {f : Nat → Nat}

theorem exec_one_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.one i) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;> simp [memOf, up, hxi]

theorem exec_add_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.add i j k) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i (f j + f k))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;> simp [memOf, up, hxi, bv_add]

theorem exec_shr_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.shr i j k)
    (hfit : ∀ x, f x < 2 ^ w) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i (f j / 2 ^ f k))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;> simp [memOf, up, hxi, bv_shr (hfit j) (hfit k)]

theorem exec_load_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.load i j)
    (hfit : ∀ x, f x < 2 ^ w) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f i (f (f j)))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = i <;>
    simp [memOf, up, hxi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfit j)]

theorem exec_store_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.store i j)
    (hfit : ∀ x, f x < 2 ^ w) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 1) (pc + 1) r (memOf w (up f (f i) (f j))) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  congr 1
  funext x
  by_cases hxi : x = f i <;>
    simp [memOf, up, hxi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfit i)]

theorem exec_blt_lt_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.blt i j l)
    (hfit : ∀ x, f x < 2 ^ w) (hlt : f i < f j) :
    exec P ρ S pc r (memOf w f) = exec P ρ (S - 1) l r (memOf w f) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  exact congrArg (fun p => exec P ρ t p r (memOf w f))
    (if_pos ((ofNat_lt_ofNat (hfit i) (hfit j)).mpr hlt))

theorem exec_blt_ge_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.blt i j l)
    (hfit : ∀ x, f x < 2 ^ w) (hge : ¬ f i < f j) :
    exec P ρ S pc r (memOf w f) = exec P ρ (S - 1) (pc + 1) r (memOf w f) := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel_right, exec, h]
  exact congrArg (fun p => exec P ρ t p r (memOf w f))
    (if_neg (fun hcon => hge ((ofNat_lt_ofNat (hfit i) (hfit j)).mp hcon)))

theorem exec_accept_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.accept) :
    exec P ρ S pc r (memOf w f) = some true := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [exec, h]

theorem exec_reject_step (hS : 0 < S) (h : P.getD pc Instr.reject = Instr.reject) :
    exec P ρ S pc r (memOf w f) = some false := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 1 := ⟨S - 1, by omega⟩
  simp only [exec, h]

end StepLemmas

/-! ### Layer 2 — the input block as a `ℕ`-valued state -/

/-- The initial memory of `x`, as a `ℕ`-valued state: `[0] = n`, `[i] = aᵢ` for
`1 ≤ i ≤ n`, `[n+1] = t`, and `0` past the end.  This is `loadWords` in the
`memOf` normal form. -/
def inF {n : Nat} (x : Instance n) : Nat → Nat := fun i => x.input.getD i 0

theorem inF_zero {n : Nat} (x : Instance n) : inF x 0 = n := rfl

theorem inF_succ {n : Nat} (x : Instance n) (k : Nat) :
    inF x (k + 1) = (List.ofFn x.a ++ [x.t]).getD k 0 := rfl

theorem inF_input {n : Nat} (x : Instance n) :
    loadWords (wordLength n x.bits) x.input = memOf (wordLength n x.bits) (inF x) := rfl

/-- `getD` on `List.ofFn`. -/
theorem ofFn_getD {α : Type} {m : Nat} (f : Fin m → α) (d : α) (k : Nat) :
    (List.ofFn f).getD k d = if h : k < m then f ⟨k, h⟩ else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < m <;> simp [h]

/-- `getD` at the length of the left list is the appended element. -/
theorem getD_append_length {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem inF_one {n : Nat} (x : Instance n) (h : 0 < n) :
    inF x 1 = x.a ⟨0, h⟩ := by
  rw [inF_succ]
  rw [List.getD_append (List.ofFn x.a) [x.t] 0 0 (by simpa using h)]
  rw [ofFn_getD]
  simp [h]

theorem inF_t {n : Nat} (x : Instance n) : inF x (n + 1) = x.t := by
  rw [inF_succ]
  rw [List.getD_append_right (List.ofFn x.a) [x.t] 0 n (by simp)]
  rw [List.length_ofFn]
  simp

theorem foldl_max_ge_init (l : List Nat) (d : Nat) : d ≤ l.foldl max d := by
  induction l generalizing d with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left d a) (ih (max d a))

theorem foldl_max_ge_of_mem (l : List Nat) (d : Nat) {v : Nat} (h : v ∈ l) :
    v ≤ l.foldl max d := by
  induction l generalizing d with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with heq | h'
    · rw [heq]
      exact le_trans (le_max_right d a) (foldl_max_ge_init l (max d a))
    · exact ih (max d a) h'

theorem le_maxValue_t {n : Nat} (x : Instance n) : x.t ≤ x.maxValue :=
  foldl_max_ge_init (List.ofFn x.a) x.t

theorem le_maxValue_a {n : Nat} (x : Instance n) (i : Fin n) : x.a i ≤ x.maxValue := by
  have hmem : x.a i ∈ List.ofFn x.a := List.mem_ofFn.mpr ⟨i, rfl⟩
  exact foldl_max_ge_of_mem (List.ofFn x.a) x.t hmem

theorem maxValue_lt_two_pow_bits {n : Nat} (x : Instance n) : x.maxValue < 2 ^ x.bits := by
  rw [Instance.bits, Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by norm_num) x.maxValue

theorem bits_pos {n : Nat} (x : Instance n) : 1 ≤ x.bits := by
  rw [Instance.bits]; omega

theorem wordLength_ge {n b : Nat} : b ≤ wordLength n b := by
  unfold wordLength; omega

theorem wordLength_ge_five {n b : Nat} (hb : 1 ≤ b) : 5 ≤ wordLength n b := by
  unfold wordLength; omega

/-- Every entry of the block is under `2^w`: the input values are under
`2^bits ≤ 2^w`, and `n` is under `2^w` because `w ≥ 4n`. -/
theorem inF_succ_lt {n : Nat} (x : Instance n) (k : Nat) :
    inF x (k + 1) < 2 ^ wordLength n x.bits := by
  have hb := bits_pos x
  have hw : x.bits ≤ wordLength n x.bits := wordLength_ge
  have hmax : x.maxValue < 2 ^ wordLength n x.bits := by
    have := maxValue_lt_two_pow_bits x
    have : (2 : Nat) ^ x.bits ≤ 2 ^ wordLength n x.bits :=
      Nat.pow_le_pow_right (by norm_num) hw
    omega
  have hle : inF x (k + 1) ≤ x.maxValue := by
    rw [inF_succ]
    by_cases hk : k < (List.ofFn x.a).length
    · rw [List.getD_append (List.ofFn x.a) [x.t] 0 k hk, ofFn_getD]
      split
      · exact le_maxValue_a x _
      · omega
    · by_cases hkn : k < (List.ofFn x.a ++ [x.t]).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using Nat.le_of_not_lt hk)]
        have hlen : (List.ofFn x.a).length = n := List.length_ofFn
        rw [hlen]
        have : k - n < 1 := by
          have : (List.ofFn x.a ++ [x.t]).length = n + 1 := by
            rw [List.length_append, List.length_ofFn]; simp
          omega
        have hk0 : k - n = 0 := by omega
        rw [hk0]
        simp only [List.getElem?_cons_zero, Option.getD_some]
        exact le_maxValue_t x
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        simp
  omega

theorem inF_zero_lt {n : Nat} (x : Instance n) : inF x 0 < 2 ^ wordLength n x.bits := by
  rw [inF_zero]
  have hb := bits_pos x
  have h1 : 4 * (n + x.bits) ≤ wordLength n x.bits := by unfold wordLength; omega
  have h4 : 4 * n ≤ 4 * (n + x.bits) := by omega
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : (2 : Nat) ^ n ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : Nat) ^ (4 * n) ≤ 2 ^ wordLength n x.bits :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem inF_lt {n : Nat} (x : Instance n) : ∀ i, inF x i < 2 ^ wordLength n x.bits := by
  intro i
  cases i with
  | zero => exact inF_zero_lt x
  | succ k => exact inF_succ_lt x k

/-! ### Layer 3 — the program

Layout (17 instructions, no loops; every jump leaves the straight line):

```
pc  0  one 6          [6] := 1                ┐
pc  1  add 5 6 6      [5] := 2                │  the constant block built from
pc  2  add 4 5 6      [4] := 3                │  the only literal constant, 1
pc  3  add 3 4 4      [3] := 6                ┘  (prog2's `one rONE` bootstrap)
pc  4  blt 0 3 16     n < 6 ⟹ CONTINUE
pc  5  add 0 0 0      [0] := 2n               ┐  the cursor: 2n is above the
pc  6  store 0 1      [2n] := a₁              │  block for n ≥ 2, so saving a₁
pc  7  one 1          [1] := 1                │  there is safe (prog2 saveAk)
pc  8  shr 2 0 1      [2] := n                │
pc  9  add 3 2 1      [3] := n+1              │
pc 10  load 4 3       [4] := t                │
pc 11  load 5 0       [5] := a₁               ┘
pc 12  blt 4 1 15     t < 1  ⟹ ACCEPT   (t = 0: the empty subset)
pc 13  blt 5 4 16     a₁ < t ⟹ CONTINUE
pc 14  blt 4 5 16     t < a₁ ⟹ CONTINUE
pc 15  accept         t = a₁ ⟹ ACCEPT  (the singleton {1})
pc 16  reject         CONTINUE
```

The bootstrap is the ported `prog2` shape and it is forced: `Statement.run`
starts from `loadWords _ x.input`, so cells `1..n+1` hold the input and **no
fixed cell is free** — with only cell 0 available nothing can compute an
address (`add`/`sub` need two cells).  `prog2`'s resolution, ported verbatim:
double `n` into cell 0 to get the cursor `2n` (above the block), save `a₁`
there, and only then take cell 1 as the literal `1`.  Cells `3..6` are input
cells too, but the decision reads only `t` and `a₁`, so their clobbering is
harmless — and the threshold `n ≥ 6` keeps `n + 1` (where `t` lives) clear of
every register (`3..6`) and of `2n`, which is the one arithmetic constraint the
design needs. -/
def prelimProg : List Instr :=
  [ .one 6
  , .add 5 6 6
  , .add 4 5 6
  , .add 3 4 4
  , .blt 0 3 16
  , .add 0 0 0
  , .store 0 1
  , .one 1
  , .shr 2 0 1
  , .add 3 2 1
  , .load 4 3
  , .load 5 0
  , .blt 4 1 15
  , .blt 5 4 16
  , .blt 4 5 16
  , .accept
  , .reject
  ]

/-! ### Layer 4 — the phase's value

`prelimSpec` is the preliminary search's verdict on `x`, independently of the
program: **YES** when the empty subset (`t = 0`) or the singleton `{1}`
(`a₁ = t`) is a witness, **CONTINUE** (`none`) otherwise.  It ignores the draws
— the witness test is deterministic — which is the honest reading of a search
whose candidates are enumerated rather than sampled.

`6 ≤ n` is the gate below which the search does not even try (its register
window needs `n + 1 > 6` and `2n > n + 1`); a capped search is free to CONTINUE whenever it
likes, so this costs nothing in soundness. -/
def prelimYes (n : Nat) (x : Instance n) : Bool :=
  if h : 6 ≤ n then
    (x.t == 0 || x.a ⟨0, Nat.lt_of_lt_of_le (by norm_num) h⟩ == x.t)
  else false

def prelimSpec (n : Nat) (x : Instance n) (_ : Draws) : Option Bool :=
  if prelimYes n x then some true else none

/-- §7's step-1 step count, in word operations: the 17 instructions above, all
charged one word operation each (every value stays inside one word: `2n` and
`a₁` and `t` are all `< 2^w` by `inF_lt`). -/
def prelimCost (n : Nat) (_ : Instance n) : Nat := 20

theorem prelimYes_eq_true {n : Nat} (x : Instance n) (h : 6 ≤ n)
    (hv : x.t = 0 ∨ x.a ⟨0, Nat.lt_of_lt_of_le (by norm_num) h⟩ = x.t) :
    prelimYes n x = true := by
  unfold prelimYes
  rw [dif_pos h]
  rcases hv with hv | hv
  · simp [hv]
  · simp [hv]

theorem prelimYes_eq_false {n : Nat} (x : Instance n) (h : ¬ 6 ≤ n) :
    prelimYes n x = false := by
  unfold prelimYes
  rw [dif_neg h]

theorem prelimYes_eq_false_of {n : Nat} (x : Instance n) (h : 6 ≤ n)
    (hv : ¬ (x.t = 0 ∨ x.a ⟨0, Nat.lt_of_lt_of_le (by norm_num) h⟩ = x.t)) :
    prelimYes n x = false := by
  unfold prelimYes
  rw [dif_pos h]
  rcases not_or.mp hv with ⟨h1, h2⟩
  have h1' : (x.t == 0) = false := by
    by_cases ht : x.t = 0
    · exact absurd ht h1
    · simpa using ht
  have h2' : (x.a ⟨0, Nat.lt_of_lt_of_le (by norm_num) h⟩ == x.t) = false := by
    by_cases ht : x.a ⟨0, Nat.lt_of_lt_of_le (by norm_num) h⟩ = x.t
    · exact absurd ht h2
    · simpa using ht
  rw [h1', h2']
  rfl

/-- The empty subset witnesses `t = 0`. -/
theorem yes_of_t_zero {n : Nat} (x : Instance n) (h : x.t = 0) : x.yes := by
  refine ⟨fun _ => false, ?_⟩
  simp [h]

/-- The singleton `{1}` witnesses `a₁ = t`. -/
theorem yes_of_a_one {n : Nat} (x : Instance n) (hn : 0 < n)
    (h : x.a ⟨0, hn⟩ = x.t) : x.yes := by
  refine ⟨fun i => decide (i = ⟨0, hn⟩), ?_⟩
  rw [List.sum_ofFn, Finset.sum_eq_single ⟨0, hn⟩]
  · simp [h]
  · intro b _ hb; simp [hb]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-- **Soundness of the preliminary search.**  It answers YES only when a genuine
witness exists — the empty subset for `t = 0`, the singleton for `a₁ = t`.  This
is §7's «returns the correct decision or CONTINUE» half that a search can
actually carry; the CONTINUE side is `prelimSpec = none`. -/
theorem prelim_sound {n : Nat} (x : Instance n) (ω : Draws)
    (h : prelimSpec n x ω = some true) : x.yes := by
  unfold prelimSpec at h
  by_cases hy : prelimYes n x = true
  · rw [if_pos hy] at h
    unfold prelimYes at hy
    by_cases h10 : 6 ≤ n
    · rw [dif_pos h10] at hy
      have hn : 0 < n := by omega
      have hor : (x.t == 0) = true ∨ (x.a ⟨0, Nat.lt_of_lt_of_le (by norm_num) h10⟩ == x.t) = true :=
        (Bool.or_eq_true _ _).mp hy
      rcases hor with hz | ha
      · exact yes_of_t_zero x (beq_iff_eq.mp hz)
      · exact yes_of_a_one x hn (by
          have := beq_iff_eq.mp ha
          convert this using 2)
    · rw [dif_neg h10] at hy
      exact absurd hy (by simp)
  · rw [if_neg hy] at h
    exact absurd h (by simp)

/-! ### Layer 5 — the walk

The agreement, proved against the text: at `prelimCost`, `prelimProg` halts and
its verdict is `prelimSpec`'s through `failToNo`. -/

theorem failToNo_some (b : Bool) : failToNo (some b) = b := by cases b <;> rfl

theorem failToNo_none : failToNo (none : Option Bool) = false := rfl

theorem failToNo_prelimSpec {n : Nat} (x : Instance n) (ω : Draws) :
    failToNo (prelimSpec n x ω) = (if prelimYes n x = true then true else false) := by
  unfold prelimSpec
  by_cases h : prelimYes n x = true
  · rw [if_pos h, if_pos h, failToNo_some]
  · rw [if_neg h, if_neg h]; rfl

theorem prelim_run {n : Nat} (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (ω : Draws) :
    run prelimProg x ρ (prelimCost n x) = some (failToNo (prelimSpec n x ω)) := by
  set w : Nat := wordLength n x.bits with hw
  have hfit0 : ∀ q, inF x q < 2 ^ w := by intro q; rw [hw]; exact inF_lt x q
  have h5 : 5 ≤ w := by rw [hw]; exact wordLength_ge_five (bits_pos x)
  have hbig : (32 : Nat) ≤ 2 ^ w := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) h5
    simpa using h
  rw [failToNo_prelimSpec]
  simp only [run, prelimCost, inF_input]
  by_cases h10 : 6 ≤ n
  · have hn0 : 0 < n := by omega
    have ha1v : inF x 1 = x.a ⟨0, hn0⟩ := inF_one x hn0
    have b1 : (1 : Nat) < 2 ^ w := by omega
    have b2 : (2 : Nat) < 2 ^ w := by omega
    have b3 : (3 : Nat) < 2 ^ w := by omega
    have b6 : (6 : Nat) < 2 ^ w := by omega
    have hnv : n < 2 ^ w := by have h := hfit0 0; rwa [inF_zero] at h
    have h2n : 2 * n < 2 ^ w := by
      have hh1 : n + 1 ≤ w := by
        rw [hw]; unfold wordLength; have := bits_pos x; omega
      have hh2 : 2 * n < 2 * 2 ^ n :=
        Nat.mul_lt_mul_of_pos_left Nat.lt_two_pow_self (by norm_num)
      have hh3 : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hh4 : (2 : Nat) ^ (n + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hh1
      omega
    have hnp1 : n + 1 < 2 ^ w := by omega
    have ha1 : x.a ⟨0, hn0⟩ < 2 ^ w := by rw [← ha1v]; exact hfit0 1
    have htv : x.t < 2 ^ w := by
      have h := inF_succ_lt x n; rw [inF_t] at h; rw [hw]; exact h
    -- pc0
    have hd0 : prelimProg.getD 0 Instr.reject = Instr.one 6 := rfl
    rw [exec_one_step (S := 20) (hS := by decide) hd0]
    set s1 : Nat → Nat := up (inF x) 6 1 with hs1
    have hf1 : ∀ q, s1 q < 2 ^ w := upFit hfit0 (v := 1) b1
    -- pc1
    have hd1 : prelimProg.getD 1 Instr.reject = Instr.add 5 6 6 := rfl
    rw [exec_add_step (S := 19) (hS := by decide) hd1]
    have hv1 : s1 6 + s1 6 = 2 := by rw [show s1 6 = 1 from up_eq _ _ _]
    rw [hv1]
    set s2 : Nat → Nat := up s1 5 2 with hs2
    have hf2 : ∀ q, s2 q < 2 ^ w := upFit hf1 (v := 2) b2
    -- pc2
    have hd2 : prelimProg.getD 2 Instr.reject = Instr.add 4 5 6 := rfl
    rw [exec_add_step (S := 18) (hS := by decide) hd2]
    have e25 : s2 5 = 2 := up_eq _ _ _
    have e26 : s2 6 = 1 := by
      rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]; exact up_eq _ _ _
    have hv2 : s2 5 + s2 6 = 3 := by rw [e25, e26]
    rw [hv2]
    set s3 : Nat → Nat := up s2 4 3 with hs3
    have hf3 : ∀ q, s3 q < 2 ^ w := upFit hf2 (v := 3) b3
    -- pc3
    have hd3 : prelimProg.getD 3 Instr.reject = Instr.add 3 4 4 := rfl
    rw [exec_add_step (S := 17) (hS := by decide) hd3]
    have hv3 : s3 4 + s3 4 = 6 := by rw [show s3 4 = 3 from up_eq _ _ _]
    rw [hv3]
    set s4 : Nat → Nat := up s3 3 6 with hs4
    have hf4 : ∀ q, s4 q < 2 ^ w := upFit hf3 (v := 6) b6
    -- pc4
    have hd4 : prelimProg.getD 4 Instr.reject = Instr.blt 0 3 16 := rfl
    have v40 : s4 0 = n := by
      rw [hs4]; rw [up_ne (by decide : (0 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (0 : Nat) ≠ 6)]
      exact inF_zero x
    have v43 : s4 3 = 6 := up_eq _ _ _
    rw [exec_blt_ge_step (S := 16) (hS := by decide) hd4 hf4 (by rw [v40, v43]; omega)]
    -- pc5
    have hd5 : prelimProg.getD 5 Instr.reject = Instr.add 0 0 0 := rfl
    rw [exec_add_step (S := 15) (hS := by decide) hd5]
    have hv5 : s4 0 + s4 0 = 2 * n := by rw [v40]; omega
    rw [hv5]
    set s5 : Nat → Nat := up s4 0 (2 * n) with hs5
    have hf5 : ∀ q, s5 q < 2 ^ w := upFit hf4 (v := 2 * n) h2n
    -- pc6
    have hd6 : prelimProg.getD 6 Instr.reject = Instr.store 0 1 := rfl
    have v50 : s5 0 = 2 * n := up_eq _ _ _
    have v51 : s5 1 = x.a ⟨0, hn0⟩ := by
      rw [hs5]; rw [up_ne (by decide : (1 : Nat) ≠ 0)]
      rw [hs4]; rw [up_ne (by decide : (1 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (1 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (1 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (1 : Nat) ≠ 6)]
      exact ha1v
    rw [exec_store_step (S := 14) (hS := by decide) hd6 hf5]
    rw [v50, v51]
    set s6 : Nat → Nat := up s5 (2 * n) (x.a ⟨0, hn0⟩) with hs6
    have hf6 : ∀ q, s6 q < 2 ^ w := upFit hf5 (v := x.a ⟨0, hn0⟩) ha1
    -- pc7
    have hd7 : prelimProg.getD 7 Instr.reject = Instr.one 1 := rfl
    rw [exec_one_step (S := 13) (hS := by decide) hd7]
    set s7 : Nat → Nat := up s6 1 1 with hs7
    have hf7 : ∀ q, s7 q < 2 ^ w := upFit hf6 (v := 1) b1
    -- pc8
    have hd8 : prelimProg.getD 8 Instr.reject = Instr.shr 2 0 1 := rfl
    have v70 : s7 0 = 2 * n := by
      rw [hs7]; rw [up_ne (by decide : (0 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]
      rw [hs5]; exact up_eq _ _ _
    have v71 : s7 1 = 1 := up_eq _ _ _
    rw [exec_shr_step (S := 12) (hS := by decide) hd8 hf7]
    have hv8 : s7 0 / 2 ^ s7 1 = n := by
      rw [v70, v71, show (2 : Nat) ^ 1 = 2 from by norm_num, Nat.mul_comm]
      exact Nat.mul_div_cancel n (by norm_num)
    rw [hv8]
    set s8 : Nat → Nat := up s7 2 n with hs8
    have hf8 : ∀ q, s8 q < 2 ^ w := upFit hf7 (v := n) hnv
    -- pc9
    have hd9 : prelimProg.getD 9 Instr.reject = Instr.add 3 2 1 := rfl
    have v81 : s8 1 = 1 := by
      rw [hs8]; rw [up_ne (by decide : (1 : Nat) ≠ 2)]; exact up_eq _ _ _
    rw [exec_add_step (S := 11) (hS := by decide) hd9]
    have hv9 : s8 2 + s8 1 = n + 1 := by rw [show s8 2 = n from up_eq _ _ _, v81]
    rw [hv9]
    set s9 : Nat → Nat := up s8 3 (n + 1) with hs9
    have hf9 : ∀ q, s9 q < 2 ^ w := upFit hf8 (v := n + 1) hnp1
    -- pc10
    have hd10 : prelimProg.getD 10 Instr.reject = Instr.load 4 3 := rfl
    have v93 : s9 3 = n + 1 := up_eq _ _ _
    have v9t : s9 (n + 1) = x.t := by
      rw [hs9]; rw [up_ne (by omega : n + 1 ≠ 3)]
      rw [hs8]; rw [up_ne (by omega : n + 1 ≠ 2)]
      rw [hs7]; rw [up_ne (by omega : n + 1 ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : n + 1 ≠ 2 * n)]
      rw [hs5]; rw [up_ne (by omega : n + 1 ≠ 0)]
      rw [hs4]; rw [up_ne (by omega : n + 1 ≠ 3)]
      rw [hs3]; rw [up_ne (by omega : n + 1 ≠ 4)]
      rw [hs2]; rw [up_ne (by omega : n + 1 ≠ 5)]
      rw [hs1]; rw [up_ne (by omega : n + 1 ≠ 6)]
      exact inF_t x
    rw [exec_load_step (S := 10) (hS := by decide) hd10 hf9]
    rw [v93, v9t]
    set s10 : Nat → Nat := up s9 4 x.t with hs10
    have hf10 : ∀ q, s10 q < 2 ^ w := upFit hf9 (v := x.t) htv
    -- pc11
    have hd11 : prelimProg.getD 11 Instr.reject = Instr.load 5 0 := rfl
    have v100 : s10 0 = 2 * n := by
      rw [hs10]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs9]; rw [up_ne (by decide : (0 : Nat) ≠ 3)]
      rw [hs8]; rw [up_ne (by decide : (0 : Nat) ≠ 2)]
      rw [hs7]; rw [up_ne (by decide : (0 : Nat) ≠ 1)]
      rw [hs6]; rw [up_ne (by omega : (0 : Nat) ≠ 2 * n)]
      rw [hs5]; exact up_eq _ _ _
    have v10a : s10 (2 * n) = x.a ⟨0, hn0⟩ := by
      rw [hs10]; rw [up_ne (by omega : 2 * n ≠ 4)]
      rw [hs9]; rw [up_ne (by omega : 2 * n ≠ 3)]
      rw [hs8]; rw [up_ne (by omega : 2 * n ≠ 2)]
      rw [hs7]; rw [up_ne (by omega : 2 * n ≠ 1)]
      rw [hs6]; exact up_eq _ _ _
    rw [exec_load_step (S := 9) (hS := by decide) hd11 hf10]
    rw [v100, v10a]
    set s11 : Nat → Nat := up s10 5 (x.a ⟨0, hn0⟩) with hs11
    have hf11 : ∀ q, s11 q < 2 ^ w := upFit hf10 (v := x.a ⟨0, hn0⟩) ha1
    have v10t : s10 4 = x.t := up_eq _ _ _
    have w4 : s11 4 = x.t := by
      rw [hs11]; rw [up_ne (by decide : (4 : Nat) ≠ 5)]; exact v10t
    have w1 : s11 1 = 1 := by
      rw [hs11]; rw [up_ne (by decide : (1 : Nat) ≠ 5)]
      rw [hs10]; rw [up_ne (by decide : (1 : Nat) ≠ 4)]
      rw [hs9]; rw [up_ne (by decide : (1 : Nat) ≠ 3)]
      rw [hs8]; rw [up_ne (by decide : (1 : Nat) ≠ 2)]
      rw [hs7]; exact up_eq _ _ _
    have w5 : s11 5 = x.a ⟨0, hn0⟩ := up_eq _ _ _
    by_cases hz : x.t = 0
    · have hd12 : prelimProg.getD 12 Instr.reject = Instr.blt 4 1 15 := rfl
      rw [exec_blt_lt_step (S := 8) (hS := by decide) hd12 hf11 (by rw [w4, w1]; omega)]
      have hd15 : prelimProg.getD 15 Instr.reject = Instr.accept := rfl
      rw [exec_accept_step (S := 7) (hS := by decide) hd15]
      rw [prelimYes_eq_true x h10 (Or.inl hz)]
      rfl
    · have hd12 : prelimProg.getD 12 Instr.reject = Instr.blt 4 1 15 := rfl
      rw [exec_blt_ge_step (S := 8) (hS := by decide) hd12 hf11 (by rw [w4, w1]; omega)]
      rcases lt_trichotomy (x.a ⟨0, hn0⟩) x.t with hlt | heq | hgt
      · have hd13 : prelimProg.getD 13 Instr.reject = Instr.blt 5 4 16 := rfl
        rw [exec_blt_lt_step (S := 7) (hS := by decide) hd13 hf11 (by rw [w5, w4]; exact hlt)]
        have hd16 : prelimProg.getD 16 Instr.reject = Instr.reject := rfl
        rw [exec_reject_step (S := 6) (hS := by decide) hd16]
        rw [prelimYes_eq_false_of x h10 (by
          intro hc; rcases hc with hc | hc
          · omega
          · rw [hc] at hlt; omega)]
        rfl
      · have hd13 : prelimProg.getD 13 Instr.reject = Instr.blt 5 4 16 := rfl
        rw [exec_blt_ge_step (S := 7) (hS := by decide) hd13 hf11 (by rw [w5, w4]; omega)]
        have hd14 : prelimProg.getD 14 Instr.reject = Instr.blt 4 5 16 := rfl
        rw [exec_blt_ge_step (S := 6) (hS := by decide) hd14 hf11 (by rw [w4, w5]; omega)]
        have hd15 : prelimProg.getD 15 Instr.reject = Instr.accept := rfl
        rw [exec_accept_step (S := 5) (hS := by decide) hd15]
        rw [prelimYes_eq_true x h10 (Or.inr heq)]
        rfl
      · have hd13 : prelimProg.getD 13 Instr.reject = Instr.blt 5 4 16 := rfl
        rw [exec_blt_ge_step (S := 7) (hS := by decide) hd13 hf11 (by rw [w5, w4]; omega)]
        have hd14 : prelimProg.getD 14 Instr.reject = Instr.blt 4 5 16 := rfl
        rw [exec_blt_lt_step (S := 6) (hS := by decide) hd14 hf11 (by rw [w4, w5]; exact hgt)]
        have hd16 : prelimProg.getD 16 Instr.reject = Instr.reject := rfl
        rw [exec_reject_step (S := 5) (hS := by decide) hd16]
        rw [prelimYes_eq_false_of x h10 (by
          intro hc; rcases hc with hc | hc
          · omega
          · rw [hc] at hgt; omega)]
        rfl
  · have b1 : (1 : Nat) < 2 ^ w := by omega
    have b2 : (2 : Nat) < 2 ^ w := by omega
    have b3 : (3 : Nat) < 2 ^ w := by omega
    have b6 : (6 : Nat) < 2 ^ w := by omega
    have hd0 : prelimProg.getD 0 Instr.reject = Instr.one 6 := rfl
    rw [exec_one_step (S := 20) (hS := by decide) hd0]
    set s1 : Nat → Nat := up (inF x) 6 1 with hs1
    have hf1 : ∀ q, s1 q < 2 ^ w := upFit hfit0 (v := 1) b1
    have hd1 : prelimProg.getD 1 Instr.reject = Instr.add 5 6 6 := rfl
    rw [exec_add_step (S := 19) (hS := by decide) hd1]
    have hv1 : s1 6 + s1 6 = 2 := by rw [show s1 6 = 1 from up_eq _ _ _]
    rw [hv1]
    set s2 : Nat → Nat := up s1 5 2 with hs2
    have hf2 : ∀ q, s2 q < 2 ^ w := upFit hf1 (v := 2) b2
    have hd2 : prelimProg.getD 2 Instr.reject = Instr.add 4 5 6 := rfl
    rw [exec_add_step (S := 18) (hS := by decide) hd2]
    have hv2 : s2 5 + s2 6 = 3 := by
      rw [show s2 5 = 2 from up_eq _ _ _]
      rw [show s2 6 = 1 from by
        rw [hs2]; rw [up_ne (by decide : (6 : Nat) ≠ 5)]; exact up_eq _ _ _]
    rw [hv2]
    set s3 : Nat → Nat := up s2 4 3 with hs3
    have hf3 : ∀ q, s3 q < 2 ^ w := upFit hf2 (v := 3) b3
    have hd3 : prelimProg.getD 3 Instr.reject = Instr.add 3 4 4 := rfl
    rw [exec_add_step (S := 17) (hS := by decide) hd3]
    have hv3 : s3 4 + s3 4 = 6 := by rw [show s3 4 = 3 from up_eq _ _ _]
    rw [hv3]
    set s4 : Nat → Nat := up s3 3 6 with hs4
    have hf4 : ∀ q, s4 q < 2 ^ w := upFit hf3 (v := 6) b6
    have hd4 : prelimProg.getD 4 Instr.reject = Instr.blt 0 3 16 := rfl
    have v40 : s4 0 = n := by
      rw [hs4]; rw [up_ne (by decide : (0 : Nat) ≠ 3)]
      rw [hs3]; rw [up_ne (by decide : (0 : Nat) ≠ 4)]
      rw [hs2]; rw [up_ne (by decide : (0 : Nat) ≠ 5)]
      rw [hs1]; rw [up_ne (by decide : (0 : Nat) ≠ 6)]
      exact inF_zero x
    have v43 : s4 3 = 6 := up_eq _ _ _
    rw [exec_blt_lt_step (S := 16) (hS := by decide) hd4 hf4 (by rw [v40, v43]; omega)]
    have hd16 : prelimProg.getD 16 Instr.reject = Instr.reject := rfl
    rw [exec_reject_step (S := 15) (hS := by decide) hd16]
    rw [prelimYes_eq_false x h10]
    rfl

/-! ### Layer 6 — the field shape, and the leaf it discharges

`Routines.prelim_agrees` is written as
`(run prelimProg x ρ (prelimCost n x)).map failToNo = some (failToNo (prelim n x ω))`.
Lean elaborates the `map` with a `pure`/`map some` lift (`run` returns
`Option Bool`, while `failToNo` takes `Option Bool`), so the field is really
«halt with that verdict» plus a wrapper.  `map_failToNo_bind_some` removes the
wrapper, which makes the field legible and is what lets `LeafP` follow from it. -/

/-- The wrapper Lean inserts around `run`'s result in `Routines.prelim_agrees`
is inert: `map some` followed by `failToNo` is the identity on `Option Bool`. -/
theorem map_failToNo_bind_some (X : Option Bool) :
    Option.map failToNo (Option.bind X (fun a => some (some a))) = X := by
  cases X with
  | none => rfl
  | some b => cases b <;> rfl

/-- **The field's shape, characterised.**  `Routines.prelim_agrees` holds iff the
segment *halts with `prelimSpec`'s verdict* — no `Option` ambiguity survives. -/
theorem prelim_agrees_iff_run (n : Nat) (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (P : List Instr) (c : Nat) (p : Option Bool) :
    (Option.map failToNo (Option.bind (run P x ρ c) (fun a => some (some a)))
        = some (failToNo p))
      ↔ (run P x ρ c = some (failToNo p)) := by
  rw [map_failToNo_bind_some]

/-- The agreement for **this** program and spec, in the field's exact shape. -/
theorem prelim_agrees_spec {n : Nat} (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) (ω : Draws) :
    Option.map failToNo (Option.bind (run prelimProg x ρ (prelimCost n x))
        (fun a => some (some a))) = some (failToNo (prelimSpec n x ω)) := by
  rw [prelim_run x ρ ω, map_failToNo_bind_some]

/-- Any `Routines`' `prelim_agrees` field, peeled to the `Option`-free equation. -/
theorem run_of_prelim_agrees (R : Routines) (n : Nat) (x : Instance n)
    (ρ : Nat → BitVec (wordLength n x.bits)) :
    run R.prelimProg x ρ (R.prelimCost n x)
      = some (failToNo (R.prelim n x (fun r => (ρ r).toNat))) := by
  have h := R.prelim_agrees n x ρ
  cases hr : run R.prelimProg x ρ (R.prelimCost n x) with
  | none => simp [hr] at h
  | some v =>
    simp [hr, failToNo] at h
    rw [h]; rfl

/-- **`LeafP`'s discharge.**  On the guard's complement, if `R.cost` collapses to
`R.prelimCost` (the segment is the whole program there, or the earlier segments
are free), then `R.prelim_agrees` *is* `LeafP R R.prelimProg`, with no further
program premise.  `LeafP` is one of the two remaining seam obligations in
`agrees_main_iff_leaves`. -/
theorem LeafP_of_prelim_agrees (R : Routines)
    (hcost : ∀ (n : Nat) (x : Instance n), R.cost n x = R.prelimCost n x) :
    LeafP R R.prelimProg := by
  intro n x ρ _hf b hp
  rw [hcost n x, run_of_prelim_agrees R n x ρ, hp]
  rfl

/-- The same discharge with the strong equation supplied directly (the form a
`Routines` builder proves before packaging it as the field). -/
theorem LeafP_of_prelim_run (R : Routines)
    (hcost : ∀ (n : Nat) (x : Instance n), R.cost n x = R.prelimCost n x)
    (hrun : ∀ (n : Nat) (x : Instance n) (ρ : Nat → BitVec (wordLength n x.bits)),
      run R.prelimProg x ρ (R.prelimCost n x)
        = some (failToNo (R.prelim n x (fun r => (ρ r).toNat)))) :
    LeafP R R.prelimProg := by
  intro n x ρ _hf b hp
  rw [hcost n x, hrun n x ρ, hp]
  rfl


end SubsetSumL25.Row
