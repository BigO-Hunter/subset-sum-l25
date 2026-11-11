#!/usr/bin/env python3
"""jv1000 C6 round 19 — `hdecay`: the annulus/Cauchy coefficient decay, MEASURED first.

The quadrature lemma `trapezoid_error_le_of_decay` (JV1000Strip §6) consumes

    hdecay :  forall k != 0,  ||c k|| <= M * q^{|k|}

This round has to *produce* that hypothesis from strip analyticity.  Before any Lean,
three numeric claims are checked here:

  1. THE CONTOUR SHIFT IS AN IDENTITY, not an approximation.
         c_k = (1/2pi) int_0^{2pi} F(x) e^{-ikx} dx
             = (1/2pi) int_0^{2pi} F(x+is) e^{-ik(x+is)} dx     for |s| < a
     (periodicity kills the two vertical sides of the rectangle; the factor that
     survives is e^{ks}, real).  Checked on a function with EXACT known coefficients.

  2. THE BOUND AT A FIXED SHIFT  ||c_k|| <= M e^{ks}  and its consequence at the
     endpoint of the open strip  ||c_k|| <= M e^{-a|k|}.
     The passage s -> a is NOT a limit theorem in Lean: for k > 0 and any s in (0,a),
     `||c_k|| <= M e^{ks} < M e^{ka}` is STRICT (M > 0), so `le_of_forall_lt`
     (`forall c < a, c < b -> a <= b`) closes it with `Real.exp_lt_exp` alone.
     Measured here that the strictness is real, i.e. no equality case is lost.

  3. THE SHARP TEST CASE, so the constant is not faked.  b > cosh(a):
         F(z) = 1/(b - cos z)  =  sum_k r^{|k|}/sqrt(b^2-1) e^{ikz},  r = e^{-a'}
     where cosh(a') = b is the singularity distance, so the TRUE decay rate is e^{-a'}
     and the hypothesis' rate is e^{-a} with a < a'.  The inequality is then tight in
     the rate and the constant M = 1/(b - cosh a) has to do the work -- exactly the
     situation the moment integrands are in (entire, but the bound only knows a = 0.2).

  4. THE ACTUAL MOMENT INTEGRANDS at n = 256: the strip sup M (already measured in
     sim_strip.py) against the TRUE coefficients, i.e. is the hypothesis SATISFIABLE
     for the functions §6 will be instantiated at (rather than only for toy cases).

Run: python3 sim/sim_decay.py
"""
import json
import math

import numpy as np
from flint import arb, ctx

ctx.prec = 200

# ---------------------------------------------------------------- 1. the shift identity
# exact test case: b > cosh(a), F(z) = 1/(b - cos z), true coefficients r^{|k|}/sinh(a')
A_TEST = 0.2
APRIME = 0.3                      # singularity at |Im z| = a' = 0.3
B = math.cosh(APRIME)
R = math.exp(-APRIME)


def F_test(z):
    return 1.0 / (B - complex(np.cos(z)))


def coeff_shift(s, k, N=4096):
    """(1/2pi) int_0^{2pi} F(x+is) e^{-ik(x+is)} dx, equispaced (spectrally exact)."""
    x = 2 * math.pi * np.arange(N) / N
    v = np.array([F_test(xj + 1j * s) for xj in x]) * np.exp(-1j * k * (x + 1j * s))
    return v.mean()


def coeff_true(k):
    # r^{|k|} / sinh(a')  (standard Poisson-kernel expansion of 1/(b - cos z))
    return R ** abs(k) / math.sinh(APRIME)


print("=" * 78)
print(f"1. CONTOUR SHIFT IDENTITY   (b = cosh {APRIME} = {B:.12f}, a = {A_TEST})")
print("=" * 78)
print(f"{'k':>3} {'c_k (s=0)':>24} {'c_k (s=0.19)':>24} {'exact':>24} {'|shift-exact|':>12}")
worst_id = 0.0
for k in range(0, 7):
    c0, cs, ce = coeff_shift(0.0, k), coeff_shift(0.19, k), coeff_true(k)
    worst_id = max(worst_id, abs(c0 - ce), abs(cs - ce))
    print(f"{k:>3} {c0:>24.18f} {cs:>24.18f} {ce:>24.18f} {abs(cs - ce):>12.2e}")
print(f"  worst |measured - exact| = {worst_id:.3e}   (float quadrature floor, ~1e-16)")

print()
print("=" * 78)
print("2. THE FIXED-SHIFT BOUND, THEN THE ENDPOINT (strict, so no limit is needed)")
print("=" * 78)
M_TEST = 1.0 / (B - math.cosh(A_TEST))
print(f"  M = 1/(b - cosh a) = {M_TEST:.12f}   (sup of |F| on the closed strip |Im| <= a)")
print(f"  {'k':>3} {'|c_k|':>14} {'M e^{ks}, s=.1':>16} {'M e^{ks}, s=.19':>17}"
      f" {'M e^{-a|k|}':>15} {'ratio':>9}")
ok_all = True
for k in range(0, 8):
    c = coeff_true(k)
    b1, b2 = M_TEST * math.exp(k * 0.1), M_TEST * math.exp(k * 0.19)
    bnd = M_TEST * math.exp(-A_TEST * k)
    ok_all &= (c <= b1 + 1e-18) and (c <= b2 + 1e-18) and (c <= bnd + 1e-18)
    print(f"  {k:>3} {c:>14.9f} {b1:>16.9f} {b2:>17.9f} {bnd:>15.9f} {c / bnd:>9.4f}")
print(f"  all three bounds hold for k <= 7: {ok_all}")
print(f"  strictness at the endpoint: M e^{{ks}} / (M e^{{ka}}) = e^{{k(s-a)}} = "
      f"{math.exp(7 * (0.19 - A_TEST)):.6f} < 1  -> the passage s->a is STRICT")
print(f"  (for k<0 the same with s in (-a,0): the surviving factor is e^{{k s}} = e^{{|k| |s|}})")
print(f"  true rate exponent a' = {APRIME} vs hypothesis exponent a = {A_TEST}:")
print("    hypothesis is weaker by exp(-(a'-a)|k|); constant absorbs: M/M_ideal = "
      + f"{(M_TEST * math.sinh(APRIME)):.4f}")

print()
print("=" * 78)
print("3. A SHARPNESS PROBE: how much slack does the hypothesis have at the true rate?")
print("=" * 78)
# ratio |c_k| / (M e^{-a|k|}) must DECAY like e^{-(a'-a)k}; check it does
for k in (0, 2, 4, 8, 16):
    print(f"  k = {k:>2}: |c_k|/(M e^{{-a|k|}}) = {coeff_true(k) / (M_TEST * math.exp(-A_TEST * k)):.6e}"
          f"   predicted e^{{-(a'-a)k}}*const = "
          f"{math.exp(-(APRIME - A_TEST) * k) / math.sinh(APRIME) / M_TEST:.6e}")

print()
print("=" * 78)
print("4. IS THE HYPOTHESIS SATISFIABLE FOR THE ACTUAL MOMENT INTEGRANDS?")
print("=" * 78)
AUDIT = "/Volumes/Substrate-1/bigo/audit-jv1000"
try:
    cand = json.load(open(f"{AUDIT}/exponent-2026/lab_notebook/candidate_base.json"))
    rep = json.load(open(f"{AUDIT}/repro_run1.json"))
except FileNotFoundError as e:
    cand = rep = None
    print(f"  (audit data unavailable: {e} -- sections 1-3 stand alone)")

if cand is not None:
    rc = np.array([float(x) for x in cand["rc"]])
    sc = np.array([float(x) for x in cand["sc"]])
    tau0, eta = float(cand["tau0"]), float(cand["eta"])
    kap, p, q = float(cand["kappa"]), float(cand["p"]), float(cand["q_m"])
    Delta = eta - tau0
    aG = Delta / (2 * tau0 - eta)
    A_OUT = 0.2
    strip = rep["strip"]
    U, W = strip["Ustar"], strip["Wstar"]
    sup1, sup2 = p * (Delta + U), q * (aG * W + U)
    W_OUT = 2 + 2 * math.cosh(A_OUT)

    N_in, c = 256, 32
    N = N_in * c
    xs = np.array([2 * math.pi * k / N for k in range(N)])

    def trigv(co, th):
        out = np.zeros_like(th, dtype=float)
        for j in range(16):
            out += co[j] * np.cos((j + 1) * th) + co[16 + j] * np.sin((j + 1) * th)
        return out

    # the n=256 nodes' u, v (certifier route, as in sim_strip.py)
    F = 2.0 ** trigv(rc, xs)
    G = 2.0 ** trigv(sc, xs)
    LZ = math.log2(F.mean()) + math.log2(G.mean())
    Zfk = math.log2((2.0 ** (kap * trigv(rc, xs))).mean())
    Zgk = math.log2((2.0 ** (kap * trigv(sc, xs))).mean())
    H_ = Zfk + Zgk - kap * LZ
    Gs, GSs = G[::c], (G * trigv(sc, xs))[::c]
    FR = F * trigv(rc, xs)
    u = np.empty(N)
    v = np.empty(N)
    for k in range(N):
        idx = (k + c * np.arange(N_in)) % N
        Pk = (F[idx] * Gs).mean()
        Yk = (FR[idx] * Gs).mean() + (F[idx] * GSs).mean()
        L = math.log2(Pk) - LZ
        Bq = Yk / Pk - LZ
        u[k] = L + (kap - 1) * Bq - H_
        v[k] = (2 - kap) * Bq - 2 * L + H_

    w = 2 + 2 * np.cos(xs)
    f1 = w * 2.0 ** (p * (Delta - u))
    f2 = w * 2.0 ** (q * (aG * v - u))

    print(f"  integrands: F1 = (2+2cos x) 2^p(Delta-u),  F2 = (2+2cos x) 2^q(aG v - u)")
    print(f"  strip half-width a = {A_OUT}, W_OUT = 2+2cosh(0.2) = {W_OUT:.9f}")
    for name, f, sup in (("M1", f1, sup1), ("M2", f2, sup2)):
        M = W_OUT * 2.0 ** sup
        print(f"  {name}: M = W_OUT*2^{sup:.4f} = {M:.6e}   (the previous round's number)")
        # true coefficients of the integrand (entire -> super-geometric decay)
        Nc = 4096
        xc = 2 * math.pi * np.arange(Nc) / Nc
        wc = 2 + 2 * np.cos(xc)
        Fi = np.interp(xc, xs, f, period=2 * math.pi)
        bic = np.abs(np.array([(Fi * np.exp(-1j * k * xc)).mean() for k in range(0, 9)]))
        print(f"    {'k':>2} {'|c_k| (true)':>14} {'M e^{-a|k|}':>14} {'slack':>10}")
        ok = True
        for k in range(0, 9):
            bnd = M * math.exp(-A_OUT * k)
            ok &= bic[k] <= bnd
            print(f"    {k:>2} {bic[k]:>14.6e} {bnd:>14.6e} {bnd / max(bic[k], 1e-300):>10.2e}")
        print(f"    hypothesis holds at every k <= 8: {ok}")
        print(f"    (k=0 is NOT needed by hdecay -- it requires k != 0 -- and is measured"
              f" only for context)")

print()
print("=" * 78)
print("5. WHAT §6 WILL STATE AT n = 256 (both moments)")
print("=" * 78)
if cand is not None:
    margins = {"M1": 1.315448714849562e-6, "M2": 1.494035330313608e-6}
    q = math.exp(-0.2)
    for name, sup in (("M1", sup1), ("M2", sup2)):
        ceil = math.ceil(sup)
        M = W_OUT * 2.0 ** ceil
        x = math.log(q)                      # -a
        # the Lean statement's shape: M*q^256*(2K+1) + 2 eps
        qn = q ** 256
        print(f"  {name}: M = {W_OUT:.6f} * 2^{ceil} = {M:.6e}, q = e^-0.2 = {q:.17f}")
        print(f"      q^256 = {qn:.6e}   M q^256 = {M * qn:.6e}")
        for K in (16, 32):
            print(f"      K = {K:>3}: M q^256 (2K+1) = {M * qn * (2 * K + 1):.6e}"
                  f"   vs margin {margins[name]:.6e}"
                  f"   -> {'CLEARS' if M * qn * (2 * K + 1) < margins[name] else 'FAILS'}")
        print(f"      note: 2*eps must also be < margin; eps is the partial-sum tail,"
              f" ~1e-16 at K = 32 numerically")
