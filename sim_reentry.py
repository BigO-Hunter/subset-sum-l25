#!/usr/bin/env python3
"""Simulate cmpSeg + the candidate entry-reach tails, exactly as Statement.lean's
exec does (one step per instruction, fuel counts down).

Purpose per the lane's discipline: run the *exact* Instr list before proving
anything about it, and compute the Lean cost functions independently so a
stated-shape defect shows up here in minutes rather than in Lean archaeology.
"""

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


def exec_(P, t, pc, mem):
    steps = 0
    while t > 0:
        instr = P[pc] if pc < len(P) else REJECT
        kind = instr[0]
        t -= 1
        steps += 1
        if kind == "accept":
            return True, steps
        if kind == "reject":
            return False, steps
        if kind == "one":
            mem[instr[1]] = 1
            pc += 1
        elif kind in ("add", "sub", "rem"):
            i, j, k = instr[1], instr[2], instr[3]
            a, b = mem.get(j, 0), mem.get(k, 0)
            v = {"add": a + b, "sub": a - b, "rem": (a % b) if b else a}[kind]
            mem[i] = v % (1 << W)
            pc += 1
        elif kind == "load":
            mem[instr[1]] = mem.get(mem.get(instr[2], 0), 0)
            pc += 1
        elif kind == "blt":
            pc = instr[3] if mem.get(instr[1], 0) < mem.get(instr[2], 0) else pc + 1
        else:
            raise AssertionError(kind)
    return None, steps


def halt_at(P, mem):
    """minimal halting fuel, and the verdict."""
    for fuel in range(1, 400):
        v, _ = exec_(P, fuel, 0, dict(mem))
        if v is not None:
            return fuel, v
    return None, None


# ---------------------------------------------------------------- Lean's cost functions
def walkCost(h, addrV, addrA, n):
    if n == 0:
        return 7
    m = n - 1
    if h(addrV + m) == h(addrA + m):
        return 12 if m == 0 else 9 + walkCost(h, addrV, addrA, m)
    return 7 if h(addrV + m) < h(addrA + m) else 9


def cmpSegCost(h, addrV, addrA, p, r):
    if h(addrV + p) < h(addrA + p) + 2 ** r:
        if h(addrA + p) < h(addrV + p) + 2 ** r:
            return 8
        if h(addrV + p) + 2 ** r < h(addrA + p):
            return 9
        return 10 if p == 0 else 11 + walkCost(h, addrA, addrV, p)
    if h(addrA + p) + 2 ** r < h(addrV + p):
        return 7
    return 10 if p == 0 else 7 + walkCost(h, addrV, addrA, p)


# tails: sources cell 11 = addrV, 12 = addrA, 13 = p, 7 = 0, 8 = 1, 14 = limit
RELOAD = [add(0, 11, 13), add(1, 12, 13), add(2, 13, 7)]
ENTRY_TAIL = RELOAD + [blt(7, 8, 0)]                       # 4: reload + back-edge to 0
# the loop's own tail: the index advances FIRST, then the reload reads it, then the
# guard doubles as the back-edge.  (Advance-after-reload repeats p forever — measured.)
ADVANCE_TAIL = [add(13, 13, 8)] + RELOAD + [blt(13, 14, 0)]   # 5: advance + reload + guarded back-edge


def state(addrV, addrA, p, dv, da, r, limit):
    m = {0: addrV + p, 1: addrA + p, 2: p, 7: 0, 8: 1, 9: 1 << r,
         11: addrV, 12: addrA, 13: p, 14: limit}
    for i, d in enumerate(dv):
        m[addrV + i] = d
    for i, d in enumerate(da):
        m[addrA + i] = d
    return m


def h_of(addrV, addrA, dv, da, r, p):
    """the caller's frame h, as the state's non-scratch content."""
    def h(z):
        if z == 7: return 0
        if z == 8: return 1
        if z == 9: return 1 << r
        if z == 11: return addrV
        if z == 12: return addrA
        if z == 13: return p
        if addrV <= z < addrV + len(dv): return dv[z - addrV]
        if addrA <= z < addrA + len(da): return da[z - addrA]
        return 0
    return h


def frame_ok(m, h):
    """cells 0..6, 10 are the segment's; every other cell must hold h."""
    return all(m.get(z, 0) == h(z) for z in range(7, 60) if not (z <= 6 or z == 10))


ok_all = True


def check(name, ok, detail=""):
    global ok_all
    ok_all &= bool(ok)
    print(("PASS " if ok else "FAIL ") + name + (("   " + detail) if detail else ""))
    return ok


CASES = [
    ("A-tie all-equal (worst), p=1 r=1", 30, 40, 1, [3, 3], [3, 5], 1, 2),
    ("A-tie all-equal, p=2 r=1", 30, 40, 2, [3, 1, 4], [3, 1, 6], 1, 3),
    ("V-tie all-equal, p=1 r=1", 30, 40, 1, [5, 5], [3, 3], 1, 2),
    ("p=0 tie V-side, r=2", 30, 40, 0, [4], [0], 2, 1),
    ("p=0 tie A-side, r=2", 30, 40, 0, [0], [4], 2, 1),
    ("decided miss, p=1 r=2", 30, 40, 1, [3, 3], [3, 3], 2, 2),
    ("V-side hit (v above), p=1 r=1", 30, 40, 1, [8, 6], [2, 1], 1, 2),
    ("A-side hit (a above), p=1 r=1", 30, 40, 1, [2, 1], [8, 6], 1, 2),
    ("walk down-miss at p=2", 30, 40, 2, [9, 2, 1], [1, 3, 1], 1, 3),
]

print("== segment cost vs the Lean cost function (segment + 2-instr verdict tail) ==")
for label, aV, aA, p, dv, da, r, limit in CASES:
    m = state(aV, aA, p, dv, da, r, limit)
    h = h_of(aV, aA, dv, da, r, p)
    prog = cmpSeg(29) + [blt(7, 6, 31), REJECT, ACCEPT]   # 29 = blast, 30 = reject, 31 = accept
    fuel, verdict = halt_at(prog, m)
    pred_cost = cmpSegCost(h, aV, aA, p, r)
    pred_verdict = 2 ** (r) <= 0 or None  # placeholder; compare with digHalf below
    # the verdict's step count: hit -> 2 (blt+accept), miss -> 2 (blt+reject)
    check(f"{label}: program halts at cmpSegCost+2", fuel == pred_cost + 2,
          f"measured={fuel} cmpSegCost={pred_cost}")
    print(f"     verdict={verdict} cells 0/1/2 after seg = ", end="")
    mm = dict(m)
    exec_(cmpSeg(29), pred_cost, 0, mm)
    print(f"{mm.get(0)},{mm.get(1)},{mm.get(2)}   cell6={mm.get(6)}")

print("\n== entry reach: segment then 3 adds then a *redirected* back-edge to a verdict tail ==")
print("   (the real back-edge targets 0 and the program loops; redirecting it one slot past")
print("    the adds makes the post-reload state observable through the verdict)")
for label, aV, aA, p, dv, da, r, limit in CASES:
    m = state(aV, aA, p, dv, da, r, limit)
    h = h_of(aV, aA, dv, da, r, p)
    cost = cmpSegCost(h, aV, aA, p, r)
    # positions: 0..28 segment(cont=29), 29..31 adds, 32 back-edge -> 33,
    # 33 = blt 7 6 35, 34 = reject, 35 = accept
    prog = cmpSeg(29) + RELOAD + [blt(7, 8, 33), blt(7, 6, 35), REJECT, ACCEPT]
    fuel, verdict = halt_at(prog, m)
    check(f"{label}: entry tail costs 4 (total cmpSegCost+4+2)", fuel == cost + 6,
          f"measured={fuel} predicted={cost + 6}")
    # one step short must not halt
    v_short, _ = exec_(prog, cost + 5, 0, dict(m))
    check("   one step short does not halt", v_short is None, f"fuel={cost + 5}")
    # the reload restores the frame: run seg + 4-instruction tail with the real back-edge,
    # then inspect the memory at the moment pc returns to 0
    mm = dict(m)
    exec_(cmpSeg(29) + ENTRY_TAIL, cost + 4, 0, mm)
    check("   frame re-established (0/1/2 at p, 7/8/9 and 11/12/13 untouched)",
          mm.get(0) == aV + p and mm.get(1) == aA + p and mm.get(2) == p
          and mm.get(7) == 0 and mm.get(8) == 1 and mm.get(9) == 1 << r
          and mm.get(11) == aV and mm.get(12) == aA and mm.get(13) == p,
          f"0={mm.get(0)} 1={mm.get(1)} 2={mm.get(2)} 9={mm.get(9)}")

print("\n== terminating loop: 5-instruction tail (reload + index advance + guarded back-edge) ==")
# two iterations p=0 then p=1; p=0 -> hit (tie V-side), p=1 -> decided miss.
dv, da, r = [4, 3], [0, 3], 2
limit = 2
aV, aA = 30, 40
m = state(aV, aA, 0, dv, da, r, limit)
h0 = h_of(aV, aA, dv, da, r, 0)
h1 = h_of(aV, aA, dv, da, r, 1)
c0 = cmpSegCost(h0, aV, aA, 0, r)
c1 = cmpSegCost(h1, aV, aA, 1, r)
prog = cmpSeg(29) + ADVANCE_TAIL + [blt(7, 6, 36), REJECT, ACCEPT]
fuel, verdict = halt_at(prog, m)
pred = c0 + 5 + c1 + 5 + 2
check("advance loop halts at cmpSegCost(0)+5+cmpSegCost(1)+5+2", fuel == pred,
      f"measured={fuel} predicted={pred} (c0={c0} c1={c1})")
check("final verdict is the p=1 verdict (miss = false) -> the index really advanced",
      verdict is False, f"verdict={verdict}")
# what the p=0 verdict was, for contrast
v0f, v0 = halt_at(cmpSeg(29) + [blt(7, 6, 31), REJECT, ACCEPT], m)
check("p=0 alone is a hit (so a missing advance would end true)", v0 is True, f"verdict={v0}")

print("\nALL CHECKS:", "PASS" if ok_all else "FAIL")
print("cost shape: entry reach = 4 (3 adds + back-edge); terminating loop = 5")
print("            (3 adds + index advance + guarded back-edge, guard folded into the back-edge)")
