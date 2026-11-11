#!/usr/bin/env python3
"""jv1000 C6 measurement artifact (round 17) — the numbers the Lean round cites.

Four measurements, each reproduced here so the next mind does not have to trust prose:

  1. the RAW-density moment shapes the residue used to assert (and their log2 vs rho_c);
  2. the CERTIFIED strip-corrected moments (continuum limit of certify_c5's grid sums),
     and their agreement with the audit pack's discrete value;
  3. the trapezoid+Lipschitz subdivision requirement at this point;
  4. the strip-analyticity decay q0^n (the route the proof must take).

Data: exponent-2026/lab_notebook/candidate_base.json (the frozen point) and
audit-jv1000/repro_run1.json (the certifier's own log2M1/log2M2 and strip constants).

Run: python3 sim/sim_m1.py
"""
import json
import math

import numpy as np

AUDIT = "/Volumes/Substrate-1/bigo/audit-jv1000"
cand = json.load(open(f"{AUDIT}/exponent-2026/lab_notebook/candidate_base.json"))
rep = json.load(open(f"{AUDIT}/repro_run1.json"))

rc = np.array([float(x) for x in cand["rc"]])   # 16 cosine, then 16 sine, density r
sc = np.array([float(x) for x in cand["sc"]])   # same, density s
tau0, eta = float(cand["tau0"]), float(cand["eta"])
kap, p, q = float(cand["kappa"]), float(cand["p"]), float(cand["q_m"])
Delta = eta - tau0
aG = Delta / (2 * tau0 - eta)
rhoF = eta - 1.5e-6
rhoC = rhoF - 1e-6
TWO_PI = 2 * math.pi
LN2 = math.log(2)


def trigv(co, th):
    out = np.zeros_like(th, dtype=float)
    for j in range(16):
        out += co[j] * np.cos((j + 1) * th) + co[16 + j] * np.sin((j + 1) * th)
    return out


def lip16(co):
    return sum((j + 1) * (abs(co[j]) + abs(co[16 + j])) for j in range(16))


print(f"rho_c            = {rhoC:.10f}")
print(f"lip16 r          = {lip16(rc):.8f}   lip16 s = {lip16(sc):.8f}")
print(f"r(0)             = {float(trigv(rc, np.array([0.0]))[0]):+.8f}"
      f"   s(0) = {float(trigv(sc, np.array([0.0]))[0]):+.8f}")

# --- 1. the raw-density shapes the residue asserted -------------------------------
M = 1 << 20
th = np.arange(M) * TWO_PI / M
w = 2 + 2 * np.cos(th)
r_th, s_th = trigv(rc, th), trigv(sc, th)
raw1 = float((w * 2.0 ** (p * (Delta - r_th))).mean())
raw2 = float((w * 2.0 ** (q * (aG * s_th - r_th))).mean())
print("\n[1] RAW-density shapes (what JV1000Instance's m1/m2 asserted):")
print(f"    M1 = {raw1:12.6f}   log2 = {math.log2(raw1):.10f}   margin = {rhoC - math.log2(raw1):+.6f}")
print(f"    M2 = {raw2:12.6f}   log2 = {math.log2(raw2):.10f}   margin = {rhoC - math.log2(raw2):+.6f}")

# --- 2. the certified strip-corrected moments (continuum limit) -------------------
N_O, N_I = 1024, 512
thk = np.arange(N_O) * TWO_PI / N_O
yi = np.arange(N_I) * TWO_PI / N_I
Gi = 2.0 ** trigv(sc, yi)
GiS = Gi * trigv(sc, yi)
ri, si = trigv(rc, thk), trigv(sc, thk)
Zf, Zg = (2.0 ** ri).mean(), Gi.mean()
LZ = math.log2(Zf * Zg)
H_ = math.log2((2.0 ** (kap * ri)).mean()) + math.log2((2.0 ** (kap * si)).mean()) - kap * LZ
TH = thk[:, None] + yi[None, :]
rr = trigv(rc, TH)
Fi = 2.0 ** rr
Pk = (Fi * Gi[None, :]).mean(axis=1)
Yk = (Fi * rr * Gi[None, :] + Fi * GiS[None, :]).mean(axis=1)
L_ = np.log2(Pk) - LZ
B_ = Yk / Pk - LZ
u = L_ + (kap - 1) * B_ - H_
v = (2 - kap) * B_ - 2 * L_ + H_
wk = 2 + 2 * np.cos(thk)
cert1 = float((wk * 2.0 ** (p * (Delta - u))).mean())
cert2 = float((wk * 2.0 ** (q * (aG * v - u))).mean())
print("\n[2] CERTIFIED (strip-corrected u, v — continuum limit of certify_c5):")
print(f"    M1 = {cert1:12.10f}   log2 = {math.log2(cert1):.15f}   margin = {rhoC - math.log2(cert1):+.6e}")
print(f"    M2 = {cert2:12.10f}   log2 = {math.log2(cert2):.15f}   margin = {rhoC - math.log2(cert2):+.6e}")
print(f"    u range [{u.min():+.6f}, {u.max():+.6f}]   v range [{v.min():+.6f}, {v.max():+.6f}]")
print(f"    audit pack discrete (prec 60): log2M1 = {rep['log2M1']}   log2M2 = {rep['log2M2']}")
print(f"    |continuum(this grid) - discrete| (M1) = "
      f"{abs(math.log2(cert1) - 0.51626832585128515044):.2e}  <- shrinks with the grid;"
      f" it is this script's quadrature error, not a definition mismatch")

# --- 3. trapezoid + Lipschitz subdivision requirement -----------------------------
K = 2.0 ** (p * (Delta + 3.21)) * (2 + 4 * LN2 * p * lip16(rc))
tol = rhoC - math.log2(cert1)          # absolute accuracy the moment target needs
print("\n[3] trapezoid + Lipschitz (the bound proved in Row/JV1000Quadrature):")
print(f"    K = 2^(p(Delta+3.21))*(2+4 ln2 p lip16) = {K:.4e}")
print(f"    n >= K*(2pi)^2/(2*tol) = {K * TWO_PI ** 2 / (2 * tol):.3e} panels")
for n in (16, 64, 256, 1024, 4096):
    xs = np.arange(n) * TWO_PI / n
    T = float(((2 + 2 * np.cos(xs)) * 2.0 ** (p * (Delta - trigv(rc, xs)))).mean())
    print(f"      true trapezoid error at n={n:5d}: {abs(T - raw1):11.3e}"
          f"   (Lipschitz bound {K * TWO_PI ** 2 / (2 * n):11.3e})")

# --- 4. strip analyticity: the route that can close it ---------------------------
q0 = float(rep["strip"]["q0"])
print(f"\n[4] strip analyticity: q0 = {q0:.16f}")
for n in (20, 30, 40, 64, 100):
    print(f"      q0^{n:3d} = {q0 ** n:.2e}")
