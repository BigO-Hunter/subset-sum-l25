#!/usr/bin/env python3
"""Stride-`k` payload read — the fold's program shape, simulated BEFORE it is stated.

Round-19's next action: `cmpSeg` reads ONE word per index (`addrV + p`) while §6.2's
estimates sit in `stride`-word blocks, so the test segment's read at estimate `i` must
be the fold of `stride` loads at `baseV + i·stride + j` with weights `2^{w·j}` — which
is `numAt` (`strideFold_eq_numAt`).  The ARITHMETIC of that (the fold *is* `numAt`; the
segment's verdict is the `1/2` test on the two folds; the charge is `blockLen·(20+9p)`
with `p` FIXED) is what the Lean module lands this round.

What is NOT landed is the program: the loop's counter currently carries TWO roles —
the digit address offset (`addrV + p`) and the digit position `p` itself (`blt 7 2 19`,
`.sub 2 2 8`).  At `stride = 1` those coincide; at `stride = k` they do not, and the
counter must carry `i·k + p` while the digit position stays the constant `p`.

The lane rule is simulate-first, and this file is that simulation.  Five arms:

  D1  THE READ IS THE FOLD'S TERMS.  With the counter at `i·k + p` and cell 2 reloaded
      from the `p` constant, iteration `i` reads the digit pair at
      `(baseV + i·k + p, baseA + i·k + p)` — the fold's `p`-th term at estimate `i`'s
      address — and every load stays inside one of the two blocks.  Measured.

  D2  THE COLLAPSE DEFECT.  Keep the landed reload `.add 2 13 7` (cell 2 = counter) at
      stride k > 1: the walk's counter then starts at `i·k + p`, so it walks `i·k + p`
      digits instead of `p` — the span grows with the estimate index and reaches back to
      estimate 0's block.  It stays *inside* the blocks, which is why this defect is
      arithmetic (a wrong comparison) and not a crash.  Measured as a span.

  D3  THE LIMIT DEFECT.  The guard compares the counter against cell 14.  With the
      counter carrying `i·k + p`, the limit is `blockLen·k + p`; passing `blockLen`
      (the stride-1 shape) stops the run early.  Measured as an iteration count.

  D4  THE COST.  The stride advance is ONE instruction (`.add 13 13 <k>`) and the reload
      is still three adds, so the per-comparison charge is `cmpSegCost + 6` unchanged.
      Measured against `cmpSegCost + 6` summed over the estimates (plus the halting step).

  D5  THE VERDICT IS THE FOLD'S TEST.  The accumulator equals the number of estimates
      whose `digHalf` at the estimate's own address is `true` — the program's verdict is
      the per-estimate `1/2` test on the two folds, not on a sliding window.

Exit status 0 iff every arm passes.  Nothing here is Lean evidence; it is the
measurement that the statement being authored is about the program that exists.
"""

import sys

W = 8


def one(i): return ("one", i, 0, 0)
def add(i, j, k): return ("add", i, j, k)
def sub(i, j, k): return ("sub", i, j, k)
def rem(i, j, k): return ("rem", i, j, k)
def load(i, j): return ("load", i, j)
def blt(i, j, l): return ("blt", i, j, l)
ACCEPT = ("accept", 0, 0, 0)
REJECT = ("reject", 0, 0, 0)


def cmpSeg(cont):
    return [load(3, 0), load(4, 1), add(5, 4, 9), blt(3, 5, 8), blt(5, 3, 12),
            add(6, 7, 8), blt(7, 2, 19), blt(7, 8, 12), add(5, 3, 9), blt(4, 5, 14),
            blt(5, 4, 12), blt(7, 2, 16), one(6), blt(7, 8, cont), rem(6, 7, 7),
            blt(7, 8, cont), add(10, 0, 7), add(0, 1, 7), add(1, 10, 7),
            sub(0, 0, 8), sub(1, 1, 8), load(3, 0), load(4, 1), blt(3, 4, 14),
            sub(5, 3, 4), blt(7, 5, 12), sub(2, 2, 8), blt(7, 2, 19), blt(7, 8, 12)]


SEG_LEN = 29
ACC = 15          # the counting accumulator
KCELL = 16        # the stride constant
PCELL = 17        # the digit-position constant (cell 2 is destroyed by the walk)


def stride_tail(k, p, from_counter=True):
    """The counting tail at stride `k`, `p` the fixed digit position.

    `from_counter=True` is the CORRECT shape: cell 2 is reloaded from the `p`
    constant.  `False` is the landed stride-1 shape (cell 2 from the counter)."""
    digit_src = PCELL if from_counter else 13
    return ([add(ACC, ACC, 6)] + [add(13, 13, KCELL)]
            + [add(0, 11, 13), add(1, 12, 13), add(2, digit_src, 7)]
            + [blt(13, 14, 0)])


def _step(P, pc, mem):
    instr = P[pc] if pc < len(P) else REJECT
    kind = instr[0]
    if kind == "accept":
        return None, True
    if kind == "reject":
        return None, False
    if kind == "one":
        mem[instr[1]] = 1
        return pc + 1, None
    if kind in ("add", "sub", "rem"):
        i, j, k = instr[1], instr[2], instr[3]
        a, b = mem.get(j, 0), mem.get(k, 0)
        v = {"add": a + b, "sub": a - b, "rem": (a % b) if b else a}[kind]
        mem[i] = v % (1 << W)
        return pc + 1, None
    if kind == "load":
        mem[instr[1]] = mem.get(mem.get(instr[2], 0), 0)
        return pc + 1, None
    if kind == "blt":
        return (instr[3] if mem.get(instr[1], 0) < mem.get(instr[2], 0) else pc + 1), None
    raise AssertionError(kind)


def run_traced(P, fuel, mem, pc=0):
    """Run; record every executed `load` as (iteration, address), where an iteration
    begins at the segment's first instruction (pc 0).  Returns (steps, halt, mem)."""
    mem = dict(mem)
    loads = []
    it = 0
    steps = 0
    for _ in range(fuel):
        instr = P[pc] if pc < len(P) else REJECT
        if pc == 0 and instr[0] == "load":
            it += 1
        if instr[0] == "load":
            loads.append((it, mem.get(instr[2], 0)))
        npc, halt = _step(P, pc, mem)
        steps += 1
        if halt is not None:
            return steps, halt, mem, loads
        pc = npc
    return steps, None, mem, loads


def cmpDigitsFrom(f, g, addrV, addrA, n):
    if n == 0:
        return True
    m = n - 1
    if f(addrV + m) == g(addrA + m):
        return cmpDigitsFrom(f, g, addrV, addrA, m)
    return g(addrA + m) < f(addrV + m)


def digHalf(f, g, addrV, addrA, p, r):
    if g(addrA + p) + 2 ** r < f(addrV + p):
        return True
    if f(addrV + p) + 2 ** r < g(addrA + p):
        return True
    if f(addrV + p) == g(addrA + p) + 2 ** r:
        return cmpDigitsFrom(f, g, addrV, addrA, p)
    if g(addrA + p) == f(addrV + p) + 2 ** r:
        return cmpDigitsFrom(g, f, addrA, addrV, p)
    return False


def walkCost(h, addrV, addrA, n):
    if n == 0:
        return 7
    m = n - 1
    if h(addrV + m) == h(addrA + m):
        return 12 if m == 0 else 9 + walkCost(h, addrV, addrA, m)
    return 7 if h(addrV + m) < h(addrA + m) else 9


def cmpSegCost(h, addrV, addrA, p, r):
    v, a = h(addrV + p), h(addrA + p)
    if v < a + 2 ** r:
        if a < v + 2 ** r:
            return 8
        if v + 2 ** r < a:
            return 9
        return 10 if p == 0 else 11 + walkCost(h, addrA, addrV, p)
    if a + 2 ** r < v:
        return 7
    return 10 if p == 0 else 7 + walkCost(h, addrV, addrA, p)


def h_of(baseV, baseA, dv, da, r, p, stride, k):
    def h(z):
        if z == 7: return 0
        if z == 8: return 1
        if z == 9: return 1 << r
        if z == 11: return baseV
        if z == 12: return baseA
        if z == KCELL: return k
        if z == PCELL: return p
        if ACC <= z < ACC + 1: return 0
        if baseV <= z < baseV + stride: return dv[z - baseV]
        if baseA <= z < baseA + stride: return da[z - baseA]
        return 0
    return h


def block_state(baseV, baseA, dv, da, p, r, k, stride, limit):
    m = {0: baseV + p, 1: baseA + p, 2: p, 7: 0, 8: 1, 9: 1 << r,
         11: baseV, 12: baseA, 13: p, 14: limit, ACC: 0,
         KCELL: k, PCELL: p}
    for i, d in enumerate(dv):
        m[baseV + i] = d
    for i, d in enumerate(da):
        m[baseA + i] = d
    return m


ok_all = True


def check(name, ok, detail=""):
    global ok_all
    ok_all &= bool(ok)
    print(("PASS " if ok else "FAIL ") + name + (("   " + detail) if detail else ""))
    return ok


# (label, baseV, baseA, k(stride), p, r) — one block, blockLen estimates of k words.
# Every case is built with a V-side TIE at digit `p` of every estimate and equal low
# digits, so the walk runs at EVERY comparison: the expensive path, which is where a
# stride defect shows.  `V = A + 2^r` at the p-digit; `V = A` elsewhere.
SPECS = [
    ("k=2 p=1 r=1 (4 est)", 40, 80, 2, 1, 1, 4),
    ("k=3 p=2 r=2 (3 est)", 40, 90, 3, 2, 2, 3),
    ("k=4 p=3 r=3 (2 est)", 50, 100, 4, 3, 3, 2),
]

CASES = []
for label, bV, bA, k, p, r, blockLen in SPECS:
    stride = blockLen * k
    dv, da = [], []
    for i in range(blockLen):
        for j in range(k):
            base = (i + 1) * 3 + j          # a low digit, equal on both sides
            da.append(base)
            dv.append(base + (2 ** r if j == p else 0))
    CASES.append((label, bV, bA, k, p, r, dv, da, blockLen))


for label, bV, bA, k, p, r, dv, da, blockLen in CASES:
    stride = len(dv)

    limit = blockLen * k + p
    h = h_of(bV, bA, dv, da, r, p, stride, k)

    # ---- D1 / D4 / D5: the correct shape
    P = cmpSeg(SEG_LEN) + stride_tail(k, p, from_counter=True)
    st = block_state(bV, bA, dv, da, p, r, k, stride, limit)
    steps, halt, endmem, loads = run_traced(P, 800, st)

    inside = all(bV <= a < bV + stride or bA <= a < bA + stride for (_i, a) in loads)
    check(f"D1 all loads inside a block [{label}]", inside,
          f"loads={len(loads)} steps={steps} halt={halt}")

    # first pair of each iteration == the fold's p-th term at that estimate's address
    firstpair = {}
    for (i, a) in loads:
        firstpair.setdefault(i, []).append(a)
    got = [(v[0], v[1]) for i, v in sorted(firstpair.items()) if len(v) >= 2]
    want = [(bV + i * k + p, bA + i * k + p) for i in range(blockLen)]
    check(f"D1 p-th term at estimate's address [{label}]", got == want,
          f"got={got} want={want}")

    budget = sum(cmpSegCost(h, bV + i * k, bA + i * k, p, r) + 6 for i in range(blockLen))
    check(f"D4 charge == cmpSegCost+6 per comparison [{label}]", steps == budget + 1,
          f"steps={steps} budget+halt={budget + 1}")

    hits = sum(1 for i in range(blockLen)
               if digHalf(h, h, bV + i * k, bA + i * k, p, r))
    check(f"D5 accumulator == per-estimate digHalf count [{label}]", endmem.get(ACC, 0) == hits,
          f"acc={endmem.get(ACC, 0)} hits={hits}")

    # ---- D2: the landed collapse — the walk's span grows with the estimate index
    if k > 1:
        P2 = cmpSeg(SEG_LEN) + stride_tail(k, p, from_counter=False)
        st2 = block_state(bV, bA, dv, da, p, r, k, stride, limit)
        _s2, _h2, mem2, loads2 = run_traced(P2, 800, st2)
        span = {}
        for (i, a) in loads2:
            span[i] = span.get(i, 0) + 1
        # the correct shape reads 2 + 2·(digits walked below p) per iteration;
        # the collapse reads 2 + 2·(i·k + p) at iteration i, i.e. strictly more for i ≥ 1
        Pc = cmpSeg(SEG_LEN) + stride_tail(k, p, from_counter=True)
        _s3, _h3, _m3, loads3 = run_traced(Pc, 800,
                                           block_state(bV, bA, dv, da, p, r, k, stride, limit))
        span_ok = {}
        for (i, _a) in loads3:
            span_ok[i] = span_ok.get(i, 0) + 1
        grew = any(span.get(i, 0) > span_ok.get(i, 0) for i in span_ok if i >= 2)
        check(f"D2 collapse grows the walk span [{label}]", grew,
              f"collapse={dict(sorted(span.items()))} correct={dict(sorted(span_ok.items()))}")

    # ---- D3: the stride-1 limit under-runs
    if k > 1:
        st3 = block_state(bV, bA, dv, da, p, r, k, stride, blockLen)   # WRONG limit
        _s4, _h4, _m4, loads4 = run_traced(cmpSeg(SEG_LEN) + stride_tail(k, p, True),
                                           800, st3)
        n4 = len({i for (i, _a) in loads4})
        check(f"D3 stride-1 limit under-runs [{label}]", n4 < blockLen,
              f"comparisons={n4} of blockLen={blockLen}")

print()

# ---- D6: a bounded sweep — the correct shape's accumulator is ALWAYS the per-estimate
# digHalf count; the collapse's is reported against it.  Mixed ties and misses, fixed seed.
import random
rng = random.Random(20261111)
sweep_ok = True
collapse_diff = 0
runs = 0
for _trial in range(60):
    k = rng.choice([2, 3, 4])
    p = rng.randint(1, k - 1)
    r = rng.randint(0, min(3, 8 - 1))
    blockLen = rng.randint(1, 4)
    stride = blockLen * k
    bV = rng.choice([40, 50, 60])
    bA = bV + 60
    da, dv = [], []
    for i in range(blockLen):
        for j in range(k):
            a = rng.randint(0, 200 - 2 ** r)
            da.append(a)
            roll = rng.random()
            if j == p and roll < 0.6:
                dv.append(a + 2 ** r)            # V-side tie at p
            elif j == p and roll < 0.8:
                dv.append(a)                     # exact equality at p
            else:
                dv.append(rng.randint(0, 200 - 2 ** r))
    h = h_of(bV, bA, dv, da, r, p, stride, k)
    limit = blockLen * k + p
    _s, _hh, mem_good, _l = run_traced(cmpSeg(SEG_LEN) + stride_tail(k, p, True), 3000,
                                       block_state(bV, bA, dv, da, p, r, k, stride, limit))
    want = sum(1 for i in range(blockLen) if digHalf(h, h, bV + i * k, bA + i * k, p, r))
    if mem_good.get(ACC, 0) != want:
        sweep_ok = False
        print(f"  MISMATCH good k={k} p={p} r={r} L={blockLen} acc={mem_good.get(ACC,0)} want={want}")
    _s2, _h2, mem_bad, _l2 = run_traced(cmpSeg(SEG_LEN) + stride_tail(k, p, False), 3000,
                                        block_state(bV, bA, dv, da, p, r, k, stride, limit))
    runs += 1
    if mem_bad.get(ACC, 0) != want:
        collapse_diff += 1
check("D6 sweep: correct shape == per-estimate digHalf", sweep_ok, f"runs={runs}")
print(f"     note: the collapse's accumulator differed from the per-estimate count "
      f"on {collapse_diff}/{runs} swept blocks")

print()
# ---- D2b: the collapse's VERDICT, on a block built so the spill decides.
# k=2, p=1, r=2, blockLen=2.  (`digHalf` tests |V−A| ≥ 2^r, so BOTH directions are hits;
# a MISS needs a close, unequal pair.)
#   Estimate 0: V[1]=5, A[1]=6  -> |diff| = 1 < 4, unequal, no tie  -> MISS.
#   Estimate 1: V[3]=9, A[3]=5  -> 9 = 5 + 2^r (V-side tie), V[2]=A[2]=5 -> HIT.
# Correct: acc = 1.  The collapse at estimate 1 walks 1·2+1 = 3 digits down from
#   baseV+3, reaches estimate 0's p-digit (5 < 6) and answers MISS  -> acc = 0.
bV, bA, k, p, r, blockLen = 50, 130, 2, 1, 2, 2
stride = blockLen * k
dv = [5, 5, 5, 9]
da = [5, 6, 5, 5]
h = h_of(bV, bA, dv, da, r, p, stride, k)
limit = blockLen * k + p
want = sum(1 for i in range(blockLen) if digHalf(h, h, bV + i * k, bA + i * k, p, r))
_s, _hh, mem_good, _l = run_traced(cmpSeg(SEG_LEN) + stride_tail(k, p, True), 800,
                                   block_state(bV, bA, dv, da, p, r, k, stride, limit))
_s2, _h2, mem_bad, _l2 = run_traced(cmpSeg(SEG_LEN) + stride_tail(k, p, False), 800,
                                    block_state(bV, bA, dv, da, p, r, k, stride, limit))
check("D2b correct shape == per-estimate digHalf", mem_good.get(ACC, 0) == want == 1,
      f"acc={mem_good.get(ACC, 0)} want={want}")
check("D2b collapse answers differently", mem_bad.get(ACC, 0) != want,
      f"collapse_acc={mem_bad.get(ACC, 0)} want={want}")

print()
print("ALL ARMS PASS" if ok_all else "SOME ARMS FAILED")
sys.exit(0 if ok_all else 1)

