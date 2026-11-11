#!/usr/bin/env python3
"""jv1000 C6 round 18 — the strip-analyticity quadrature bound, MEASURED before proving.

The previous round (C6, commit 3c29c99) named the route as "periodic trapezoid + strip
analyticity, q0 = 0.3708350894162912, so q0^n < 1e-17 at n = 40".  This script measures
what the certifier's own code actually does, and the answer is that q0 is NOT the
quadrature decay base.  Two distinct quantities were conflated:

  q0 = sqrt((nf-1)(ng-1))            -- the CONTOUR-SPLIT CONTRACTION of the strip
                                       correction (certify_c5.py l.54): it bounds how far
                                       the corrected u,v can be from the raw r,s
                                       (|Re L| <= -log2(1-q0), Bmax, U*, W*), and it
                                       appears in the SUP CONSTANT, not in the rate.
  q  = e^{-a}                        -- the QUADRATURE decay base, a = strip half-width
                                       (certify_c5.py l.6, l.63: Trefethen-Weideman
                                       Thm 3.2, |mean_N g - mean g| <= 2M/(e^{aN}-1)).

Measured here, in the order the round needs them:

  1. the certifier's own strip constants (2 beta = 0.2 outer, sigma = 0.3 inner);
  2. the honest error bound eps(n) = 2(2+2cosh(2beta)) 2^sup / (e^{2 beta n} - 1) and the
     MINIMAL feasible n for each moment's margin (1.3154e-6 / 1.4940e-6);
  3. the same with the sup ceiling rounded UP to an integer, so 2^ceil(sup) is
     norm_num-able in Lean (no rational-power numeric bound anywhere);
  4. the TRUE trapezoid error at those n, by direct summation (the bound is pessimistic
     by ~14 orders: the integrand is entire, the bound only knows the strip);
  5. the INNER P/Y enclosure at N_in = 256 and the relative error that must survive log.

Run: python3 sim/sim_strip.py
"""
import json
import math

import numpy as np
from flint import arb, ctx

ctx.prec = 200

AUDIT = "/Volumes/Substrate-1/bigo/audit-jv1000"
cand = json.load(open(f"{AUDIT}/exponent-2026/lab_notebook/candidate_base.json"))
rep = json.load(open(f"{AUDIT}/repro_run1.json"))

rc = np.array([float(x) for x in cand["rc"]])
sc = np.array([float(x) for x in cand["sc"]])
tau0, eta = float(cand["tau0"]), float(cand["eta"])
kap, p, q = float(cand["kappa"]), float(cand["p"]), float(cand["q_m"])
Delta = eta - tau0
aG = Delta / (2 * tau0 - eta)
rhoF = eta - 1.5e-6
rhoC = rhoF - 1e-6
TWO_PI = 2 * math.pi
LN2 = math.log(2)

# the certifier's strips (certify_c5.py l.70 defaults: beta = 0.1, sigma = 0.3)
BETA, SIG = 0.1, 0.3
A_OUT = 2 * BETA          # outer strip half-width the moment is integrated in
A_IN = SIG                # inner strip half-width for P, Y and the Z normalizers


def trigv(co, th):
    out = np.zeros_like(th, dtype=float)
    for j in range(16):
        out += co[j] * np.cos((j + 1) * th) + co[16 + j] * np.sin((j + 1) * th)
    return out


def S(co, y):
    """certify_c5.py l.28-29: the strip majorant of a cos/sin trig polynomial."""
    return sum(abs(co[j]) * math.cosh((j + 1) * y) for j in range(16)) + \
        sum(abs(co[16 + j]) * math.cosh((j + 1) * y) for j in range(16))


def qerr(M, a, n):
    """certify_c5.py l.30: Trefethen-Weideman Thm 3.2."""
    e = a * n
    if e > 700:            # e^{700} overflows a float; the bound is far below 1e-300
        return 0.0
    return 2 * M / (math.exp(e) - 1)


print("=" * 78)
print("1. THE STRIP CONSTANTS (certifier's own, re-derived)")
print("=" * 78)
Rs, Ss = S(rc, A_IN), S(sc, A_IN)
print(f"  sigma (inner)          = {A_IN}   2*beta (outer) = {A_OUT}")
print(f"  S(r, sigma)            = {Rs:.6f}      |r(z)| <= S on |Im z| <= sigma")
print(f"  S(s, sigma)            = {Ss:.6f}")
print(f"  S(r, beta)             = {S(rc, BETA):.6f}")
print(f"  S(s, beta)             = {S(sc, BETA):.6f}")

strip = rep["strip"]
q0, U, W = strip["q0"], strip["Ustar"], strip["Wstar"]
print(f"  q0 (contour split)     = {q0:.15f}   <-- NOT a decay base")
print(f"  U* = |Re u| bound      = {U:.12f}")
print(f"  W* = |Re v| bound      = {W:.12f}")

# the sup of the integrand on the outer strip, exactly as certify_c5.py l.61-63
sup1 = p * (Delta + U)
sup2 = q * (aG * W + U)
W_OUT = 2 + 2 * math.cosh(A_OUT)
print(f"  |2+2cos z| <= 2+2cosh(2beta) = {W_OUT:.9f}")
print(f"  sup_bits M1            = p(Delta+U*)  = {sup1:.9f}")
print(f"  sup_bits M2            = q(aG W*+U*)  = {sup2:.9f}")

print()
print("=" * 78)
print("2. HONEST eps(n) AND THE MINIMAL FEASIBLE n  (real sup)")
print("=" * 78)
margins = {"M1": 1.315448714849562e-6, "M2": 1.494035330313608e-6}
feas = {}
for name, sup, mg in (("M1", sup1, margins["M1"]), ("M2", sup2, margins["M2"])):
    M = W_OUT * 2.0 ** sup
    print(f"  {name}: M = {W_OUT:.6f} * 2^{sup:.4f} = {M:.6e}   margin = {mg:.6e}")
    n = 1
    while qerr(M, A_OUT, n) > mg:
        n += 1
    feas[name] = n
    print(f"      eps(n) = 2M/(e^{A_OUT}n - 1) <= margin  first at  n = {n}")
    for probe in (40, n, 128, 512, 1024, 8192):
        print(f"        n = {probe:5d} : eps = {qerr(M, A_OUT, probe):.3e}")

print()
print("=" * 78)
print("3. SUP CEILING TO AN INTEGER  (so 2^k is norm_num-able in Lean)")
print("=" * 78)
ceil1, ceil2 = math.ceil(sup1), math.ceil(sup2)
print(f"  ceil(sup1) = {ceil1}   ceil(sup2) = {ceil2}")
feas_i = {}
for name, sup, ceil, mg in (("M1", sup1, ceil1, margins["M1"]), ("M2", sup2, ceil2, margins["M2"])):
    M = W_OUT * 2.0 ** ceil
    n = 1
    while qerr(M, A_OUT, n) > mg:
        n += 1
    feas_i[name] = n
    print(f"  {name}: M_int = {W_OUT:.6f} * 2^{ceil} = {M:.6e}  ->  n = {n}"
          f"   (eps = {qerr(M, A_OUT, n):.3e})")
    print(f"      slack at that n: margin/eps = {mg / qerr(M, A_OUT, n):.3f}x")

print()
print("=" * 78)
print("4. THE TRUE TRAPEZOID ERROR AT THOSE n  (direct summation, complex strip)")
print("=" * 78)
# u, v are needed for the true integrand; take them from a fine grid (certifier's route)
N_in, c = 256, 32
N = N_in * c
xs = np.array([TWO_PI * k / N for k in range(N)])
F = 2.0 ** trigv(rc, xs)
G = 2.0 ** trigv(sc, xs)
Zf, Zg = F.mean(), G.mean()
Zfk = (2.0 ** (kap * trigv(rc, xs))).mean()
Zgk = (2.0 ** (kap * trigv(sc, xs))).mean()
LZ = math.log2(Zf * Zg)
H_ = math.log2(Zfk) + math.log2(Zgk) - kap * LZ
Gs = G[::c]
GSs = (G * trigv(sc, xs))[::c]
FR = F * trigv(rc, xs)
u = np.empty(N)
v = np.empty(N)
for k in range(N):
    idx = (k + c * np.arange(N_in)) % N
    Pk = (F[idx] * Gs).mean()                       # mean_y 2^{r(x+y)+s(y)}
    Yk = (FR[idx] * Gs).mean() + (F[idx] * GSs).mean()   # mean_y (r+s) 2^{r+s}
    L = math.log2(Pk) - LZ
    B = Yk / Pk - LZ
    u[k] = L + (kap - 1) * B - H_
    v[k] = (2 - kap) * B - 2 * L + H_
w = 2 + 2 * np.cos(xs)
f1 = w * 2.0 ** (p * (Delta - u))
f2 = w * 2.0 ** (q * (aG * v - u))
I1, I2 = f1.mean(), f2.mean()
print(f"  log2 M1 (grid) = {math.log2(I1):.15f}   margin {margins['M1']:.3e}")
print(f"  log2 M2 (grid) = {math.log2(I2):.15f}   margin {margins['M2']:.3e}")

for name, f, I, ceil in (("M1", f1, I1, ceil1), ("M2", f2, I2, ceil2)):
    for nn in (128, 256, 512, 1024):
        assert N % nn == 0, nn
        trap = f[::N // nn].mean()          # exactly equispaced n-point trapezoid
        tr = abs(trap - I)
        bd = qerr(W_OUT * 2.0 ** ceil, A_OUT, nn)
        print(f"  {name}: n = {nn:4d}  TRUE |trap_n - int| = {tr:.3e}   bound = {bd:.3e}"
              f"   bound/true = {bd / tr if tr > 0 else float('inf'):.2e}x")

print()
print("=" * 78)
print("5. THE INNER P/Y ENCLOSURE AT N_in = 256, AND WHAT log COSTS")
print("=" * 78)
eP = qerr(2.0 ** (Rs + Ss), A_IN, N_in)
eY = qerr((Rs + Ss) * 2.0 ** (Rs + Ss), A_IN, N_in)
print(f"  eP = 2*2^(Rs+Ss)/(e^(sigma*N_in)-1) = {eP:.6e}")
print(f"  eY = 2*(Rs+Ss)*2^(Rs+Ss)/(e^(sigma*N_in)-1) = {eY:.6e}")
print(f"  e^(sigma*N_in) = e^{A_IN * N_in:.1f} = {math.exp(A_IN * N_in):.4e}")
print(f"  P ranges over [{2.0 ** (-(Rs + Ss)):.3e}, {2.0 ** (Rs + Ss):.3e}] on the strip;")
print(f"  the certifier asserts Pk > 0 at every node (certify_c5.py l.47).")
print(f"  relative error of P: eP/P <= eP / min P.  min P over the circle (measured):")

# measure min P on the circle
Pk_all = np.empty(N)
for k in range(N):
    idx = (k + c * np.arange(N_in)) % N
    Pk_all[k] = F[idx].mean()
print(f"    min P = {Pk_all.min():.9f}   max P = {Pk_all.max():.9f}")
print(f"    eP/min P = {eP / Pk_all.min():.3e}   ->  |dlog2 P| <= {eP / Pk_all.min() / LN2:.3e}")
print(f"  the moment's margin on u is {margins['M1']:.3e}; p*|du| must be << that.")
print(f"  p * |dlog2 P| = {p * eP / Pk_all.min() / LN2:.3e}  ->  survives log by "
      f"{margins['M1'] / (p * eP / Pk_all.min() / LN2):.1e}x")

print()
print("=" * 78)
print("6. WHAT THE PREVIOUS ROUND'S CLAIM ACTUALLY COMPUTED")
print("=" * 78)
print(f"  q0 = {q0:.15f};  q0^40 = {q0 ** 40:.3e}   (the number the C6 commit cites)")
print(f"  but the bound the certifier uses at n=40 is")
M1r = W_OUT * 2.0 ** sup1
print(f"    2*(2+2cosh(2beta))*2^sup/(e^(2beta*40)-1) = {qerr(M1r, A_OUT, 40):.4f}  -- >1, useless")
print(f"  ratio to the cited 5.9e-18: {qerr(M1r, A_OUT, 40) / 5.9e-18:.2e}x")
print(f"  VERDICT: q0 is the contour-split contraction, not a decay base.  The honest")
print(f"  decay base is e^(-2beta) = {math.exp(-A_OUT):.6f} per node, and the feasible n")
print(f"  is {feas_i['M1']} (M1) / {feas_i['M2']} (M2) with the integer sup ceiling.")
print("=" * 78)
