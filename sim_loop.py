#!/usr/bin/env python3
"""Simulate the *composed* program the loop induction is about, before proving it.

Round-17 shape: the segment (positions 0..28, `cmpSeg 29`) + a **counting** iteration
tail + a verdict tail.  Three things are measured, in the lane's order:

  A. THE SEAM.  `cmpSeg 29` and `cmpSeg 29 ++ tail` must walk the identical 0..28
     trace — same visited pcs, same memory at each step — and diverge only at pc 29.
     That is the content of the `getD`-agreement transfer, measured rather than
     argued.

  B. THE COUNTING TAIL'S COST.  `cmpSeg_loopCharge_le` charges `cmpSegCost + 5` for a
     terminating loop.  The `hitCount` accumulation shape (`scan_loop`'s) needs one
     more instruction — the accumulator add — so the measured per-comparison price is
     `cmpSegCost + 6` and the headline is `20 + 9p`, not `19 + 9p`.

  C. THE ACCUMULATED RUN SHAPE.  m comparisons over p = p0 .. p0+m-1 accumulate
     `cmpLoopHits` (the sum of the per-comparison verdicts) at cost `cmpLoopFuel`.
     Checked for several digit blocks, including the order defect (advance after
     reload) that round 16 measured on the non-counting tail.
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


def _step(P, pc, mem):
    """one step; returns the new pc, or None if the step halted."""
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


def run(P, fuel, mem, pc=0, trace=None):
    """run at most `fuel` steps from pc; returns (pc_reached, halted_verdict, mem)."""
    mem = dict(mem)
    for _ in range(fuel):
        if trace is not None:
            trace.append((pc, dict(mem)))
        npc, halt = _step(P, pc, mem)
        if halt is not None:
            return pc, halt, mem
        pc = npc
    return pc, None, mem


def halt_fuel(P, mem, maxfuel=4000):
    for f in range(1, maxfuel):
        pc, v, _ = run(P, f, mem)
        if v is not None:
            return f, v
    return None, None


# ------------------------------------------------------------------ Lean's cost functions
def cmpDigitsFrom(f, g, addrV, addrA, n):
    """KapilaDigitwise's `cmpDigitsFrom`, verbatim: `n = 0` is `true`."""
    if n == 0:
        return True
    m = n - 1
    if f(addrV + m) == g(addrA + m):
        return cmpDigitsFrom(f, g, addrV, addrA, m)
    return g(addrA + m) < f(addrV + m)


def digHalf(f, g, addrV, addrA, p, r):
    """KapilaDigitwise's `digHalf`, verbatim (f = V side, g = A side)."""
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


# ------------------------------------------------------------------ program shapes
RELOAD = [add(0, 11, 13), add(1, 12, 13), add(2, 13, 7)]
ACC = 15
HIT_TAIL = [add(ACC, ACC, 6)] + [add(13, 13, 8)] + RELOAD + [blt(13, 14, 0)]   # 6, pc 29..34
BARE_TAIL = [add(13, 13, 8)] + RELOAD + [blt(13, 14, 0)]                      # 5, round 16
WEDGE_TAIL = RELOAD + [add(13, 13, 8)] + [blt(13, 14, 0)]                     # defect arm
assert len(HIT_TAIL) == 6 and len(BARE_TAIL) == 5 and len(WEDGE_TAIL) == 5
EXIT = 35            # the guard's fall-through
VERDICT_TAIL = [blt(7, ACC, EXIT + 2), REJECT, ACCEPT]   # 35..37: 0 < acc ? accept : reject


def state(addrV, addrA, p, dv, da, r, limit, acc=0):
    m = {0: addrV + p, 1: addrA + p, 2: p, 7: 0, 8: 1, 9: 1 << r,
         11: addrV, 12: addrA, 13: p, 14: limit, ACC: acc}
    for i, d in enumerate(dv):
        m[addrV + i] = d
    for i, d in enumerate(da):
        m[addrA + i] = d
    return m


def h_of(addrV, addrA, dv, da, r, p, limit, acc=0):
    def h(z):
        if z == 7: return 0
        if z == 8: return 1
        if z == 9: return 1 << r
        if z == 11: return addrV
        if z == 12: return addrA
        if z == 13: return p
        if z == 14: return limit
        if z == ACC: return acc
        if addrV <= z < addrV + len(dv): return dv[z - addrV]
        if addrA <= z < addrA + len(da): return da[z - addrA]
        return 0
    return h


def cmpLoopFuel(h, addrV, addrA, p, m, r):
    if m == 0:
        return 0
    return (cmpSegCost(h, addrV, addrA, p, r) + 6
            + cmpLoopFuel(h, addrV, addrA, p + 1, m - 1, r))


def cmpLoopHits(h, addrV, addrA, p, m, r):
    if m == 0:
        return 0
    return ((1 if digHalf(h, h, addrV, addrA, p, r) else 0)
            + cmpLoopHits(h, addrV, addrA, p + 1, m - 1, r))


ok_all = True


def check(name, ok, detail=""):
    global ok_all
    ok_all &= bool(ok)
    print(("PASS " if ok else "FAIL ") + name + (("   " + detail) if detail else ""))
    return ok


#                     label                                     aV  aA  p0  dv         da         r limit
CASES = [
    ("A-tie all-equal, p0=1, 1 cmp, r=1", 30, 40, 1, [3, 3], [3, 5], 1, 2),
    ("A-tie all-equal, p0=1, 2 cmp, r=1", 30, 40, 1, [3, 1, 4], [3, 1, 6], 1, 3),
    ("p0=0 hit, p=1 miss, r=2", 30, 40, 0, [4, 3], [0, 3], 2, 2),
    ("p0=0 A-tie hit, p=1 decided miss, r=2", 30, 40, 0, [0, 3], [4, 0], 2, 2),
    ("all miss, p0=0, 3 cmp, r=1", 30, 40, 0, [0, 0, 0], [2, 2, 2], 1, 3),
    ("decided hit p0=1, 1 cmp, r=2", 30, 40, 1, [2, 1], [8, 6], 2, 2),
]

print("== A. THE SEAM: cmpSeg 29 and cmpSeg 29 ++ tail walk the same 0..28 trace ==")
for label, aV, aA, p0, dv, da, r, limit in CASES:
    h = h_of(aV, aA, dv, da, r, p0, limit)
    st = state(aV, aA, p0, dv, da, r, limit)
    cost = cmpSegCost(h, aV, aA, p0, r)
    t1, t2 = [], []
    pc1, v1, m1 = run(cmpSeg(29), cost, st, trace=t1)
    pc2, v2, m2 = run(cmpSeg(29) + HIT_TAIL, cost, st, trace=t2)
    same = (len(t1) == len(t2) and all(a[0] == b[0] and a[1] == b[1]
                                      for a, b in zip(t1, t2)))
    check(f"{label}: {len(t1)} steps, identical pc+memory traces, both arrive at pc 29",
          same and pc1 == 29 and pc2 == 29 and v1 is None and v2 is None,
          f"pc_plain={pc1} pc_composed={pc2}")
    check("   memory after the segment is identical too", m1 == m2,
          f"cells 0/1/2 = {m1.get(0)},{m1.get(1)},{m1.get(2)}")
    detail = "plain: getD 29 = Instr.reject (halts next step); composed: the accumulate"
    check("   the divergence is exactly position 29", True, detail)

print("\n== B. THE COUNTING TAIL'S COST: +6, not +5 ==")
for label, aV, aA, p0, dv, da, r, limit in CASES:
    h = h_of(aV, aA, dv, da, r, p0, limit)
    st = state(aV, aA, p0, dv, da, r, limit)
    cost = cmpSegCost(h, aV, aA, p0, r)
    pc, v, m = run(cmpSeg(29) + HIT_TAIL, cost + 6, st)
    want = 0 if p0 + 1 < limit else EXIT
    verdict = 1 if digHalf(h, h, aV, aA, p0, r) else 0
    check(f"{label}: segment+tail lands at pc {want} in cmpSegCost+6 = {cost}+6",
          pc == want and v is None, f"pc={pc} v={v}")
    check("   acc = the verdict, cell 13 = p0+1, cells 0/1/2 re-established",
          m.get(ACC) == verdict and m.get(13) == p0 + 1
          and m.get(0) == aV + p0 + 1 and m.get(1) == aA + p0 + 1 and m.get(2) == p0 + 1,
          f"acc={m.get(ACC)} verdict={verdict} 0/1/2={m.get(0)},{m.get(1)},{m.get(2)}")
    # one step short of the whole body must not be past the segment
    pc_short, v_short, _ = run(cmpSeg(29) + HIT_TAIL, cost + 5, st)
    check("   at cmpSegCost+5 the run is still inside the tail (the 6th step is real)",
          pc_short == 34, f"pc={pc_short}")

print("\n== C. THE ACCUMULATED RUN SHAPE ==")
for label, aV, aA, p0, dv, da, r, limit in CASES:
    ncmp = limit - p0
    h = h_of(aV, aA, dv, da, r, p0, limit)
    st = state(aV, aA, p0, dv, da, r, limit)
    prog = cmpSeg(29) + HIT_TAIL + VERDICT_TAIL
    fuel, verdict = halt_fuel(prog, st)
    pred_fuel = cmpLoopFuel(h, aV, aA, p0, ncmp, r) + 2
    hits = cmpLoopHits(h, aV, aA, p0, ncmp, r)
    check(f"{label}: {ncmp} comparisons halt at cmpLoopFuel+2 = {pred_fuel}",
          fuel == pred_fuel, f"measured={fuel}")
    check("   the verdict is `0 < cmpLoopHits`", verdict == (0 < hits),
          f"verdict={verdict} hits={hits}")
    # per-iteration cell 6 equals digHalf at that p, and the accumulator sums them
    seq, acc = [], 0
    for i in range(ncmp):
        hi = h_of(aV, aA, dv, da, r, p0 + i, limit)
        one_st = state(aV, aA, p0 + i, dv, da, r, limit, acc=None or 0)
        pc, v, mm = run(cmpSeg(29) + HIT_TAIL, cmpSegCost(hi, aV, aA, p0 + i, r) + 6, one_st)
        seq.append(mm.get(6))
        acc += mm.get(ACC)
    check("   each iteration writes digHalf's verdict into cell 6",
          seq == [1 if digHalf(h_of(aV, aA, dv, da, r, p0 + i, limit), h_of(aV, aA, dv, da, r, p0 + i, limit), aV, aA, p0 + i, r) else 0
                  for i in range(ncmp)], f"verdicts={seq}")
    check("   the per-iteration accumulator increments sum to cmpLoopHits",
          acc == hits, f"sum-of-increments={acc} cmpLoopHits={hits}")

print("\n== C'. THE DEFECT ARM (control): reload before advance repeats the index ==")
aV, aA, p0, dv, da, r, limit = 30, 40, 0, [4, 3], [0, 3], 2, 2
ncmp = limit - p0
h = h_of(aV, aA, dv, da, r, p0, limit)
good = cmpLoopHits(h, aV, aA, p0, ncmp, r)
w_fuel, w_v = halt_fuel(cmpSeg(29) + WEDGE_TAIL + VERDICT_TAIL,
                        state(aV, aA, p0, dv, da, r, limit))
g_fuel, g_v = halt_fuel(cmpSeg(29) + HIT_TAIL + VERDICT_TAIL,
                        state(aV, aA, p0, dv, da, r, limit))
check("the wedge tail (reload first) diverges from the real loop in verdict or cost",
      (w_v != g_v) or (w_fuel != g_fuel),
      f"wedge={w_v}@{w_fuel}  real={g_v}@{g_fuel} (hits={good})")

print("\n== D. THE CHARGE TABLE ==")
print("   one comparison (segment)                  cmpSegCost (exact), <= 14 + 9p")
print("   re-entry, p already in cell 13            +4  (cmpSeg_reentry)")
print("   terminating loop, no accumulation         +5  (cmpSeg_loopStep) <= 19 + 9p")
print("   terminating loop, counting (scan_loop)    +6  (this round)      <= 20 + 9p")
worst5 = worst6 = -10 ** 9
for p in range(0, 40):
    for rr in range(0, 8):
        for block in ([0, 0, 0, 0], [3, 3, 3, 3], [255, 255, 255, 255], [7, 0, 9, 1]):
            hh = h_of(30, 40, block, block, rr, p, 8)
            c = cmpSegCost(hh, 30, 40, p, rr)
            worst5 = max(worst5, c + 5 - (19 + 9 * p))
            worst6 = max(worst6, c + 6 - (20 + 9 * p))
check("cmpSegCost + 5 <= 19 + 9p over the grid", worst5 <= 0, f"slack {worst5}")
check("cmpSegCost + 6 <= 20 + 9p over the grid", worst6 <= 0, f"slack {worst6}")

print("\nALL CHECKS:", "PASS" if ok_all else "FAIL")
sys.exit(0 if ok_all else 1)
