#!/usr/bin/env python3
"""jv1000 C6 round 21 — the U*/W* bounds and the enclosure, MEASURED before proved.

Round 20 (`JV1000Compose.lean`) left three residues: the strip bounds `Re u >= -U*` /
`Re v <= W*` (named `hU`/`hV`), and the 256-term comparison `hcmp`.  This script measures
what each one needs, in the order the Lean work must consume it.

THE REDUCTION (which this script quantifies):

    Re u = log2|P| + (kappa-1) Re(Y/P) - kappa*LZ - H_
    Re v = (2-kappa) Re(Y/P) - 2 log2|P| + kappa*LZ + H_

so with a lower bound `lam <= |P_c z|` on the strip and the already-proved majorants
`|Y_c z| <= Ymaj`, `|P_c z| <= Pmaj`:

    Re u >= log2(lam) - (kappa-1)*Ymaj/lam - kappa*LZ - H_          (*)
    Re v <= (2-kappa)*Ymaj/lam - 2*log2(lam) + kappa*LZ + H_        (*)

i.e. BOTH strip bounds are implied by THREE numeric facts: `lam`, `LZ <= l`, `H_ <= h`.

What this script measures:

  §1  the true strip extrema of Re w, Im w (w = r_c + s) and what a *crude* majorant
      route would give -- the point is to know whether the crude route can ever close;
  §2  `lam` itself: the true min |P_c| / min Re P_c on the strip (the target of the one
      remaining analytic obligation), and the value (*) needs;
  §3  the numbers in (*): Ymaj, Pmaj, LZ, H_, and the size of the cushion;
  §4  the enclosure arithmetic for `hcmp`: the derivative of F1 w.r.t. `u`, hence the
      relative precision on `P` that 3e-7 absolute on trapMean 256 demands, the inner
      trapezoid order that reaches it, and the outer quadrature's own share.

Run: python3 sim/sim_bounds_enclosure.py
"""
import json
import math

import numpy as np

AUDIT = "/Volumes/Substrate-1/bigo/audit-jv1000"
cand = json.load(open(f"{AUDIT}/exponent-2026/lab_notebook/candidate_base.json"))
rep = json.load(open(f"{AUDIT}/repro_run1.json"))

rc = np.array([float(x) for x in cand["rc"]])
sc = np.array([float(x) for x in cand["sc"]])
tau0, eta = float(cand["tau0"]), float(cand["eta"])
kap, p, q = float(cand["kappa"]), float(cand["p"]), float(cand["q_m"])
Delta = eta - tau0
aG = Delta / (2 * tau0 - eta)
rhoC = eta - 1.5e-6 - 1e-6
LN2 = math.log(2)
TWO_PI = 2 * math.pi
A_OUT = 0.2
U, W = rep["strip"]["Ustar"], rep["strip"]["Wstar"]

print("=" * 78)
print("0. CONSTANTS")
print("=" * 78)
print(f"  kappa = {kap:.8f}  (kappa-1 = {kap-1:+.8f})   2-kappa = {2-kap:.8f}")
print(f"  p = {p:.8f}   q = {q:.8f}   Delta = {Delta:.10f}   a_G = {aG:.10f}")
print(f"  rho_c = {rhoC:.10f}   U* = {U:.10f}   W* = {W:.10f}")


def trigc(co, th):
    out = np.zeros_like(th, dtype=complex)
    for j in range(16):
        out += co[j] * np.cos((j + 1) * th) + co[16 + j] * np.sin((j + 1) * th)
    return out


N = 1 << 14
xs = np.arange(N) * TWO_PI / N
ys = xs.copy()
F2r = np.exp(trigc(rc, xs) * LN2)
G2 = np.exp(trigc(sc, ys) * LN2)
Zf, Zg = F2r.mean(), G2.mean()
Zfk = np.exp(kap * trigc(rc, xs) * LN2).mean()
Zgk = np.exp(kap * trigc(sc, ys) * LN2).mean()
LZ = math.log2(Zf * Zg)
H_ = math.log2(Zfk) + math.log2(Zgk) - kap * LZ

# ---- §1: strip extrema of w = r_c(z+y) + s(y) -------------------------------------
print()
print("=" * 78)
print("1. THE STRIP EXTREMA OF w  (what a lower bound on Re P must survive)")
print("=" * 78)
NPTS = 600
ts = np.linspace(-A_OUT, A_OUT, 41)
NT = 2048
xt = np.arange(NT) * TWO_PI / NT
yt = xt.copy()
srow = np.exp(trigc(sc, yt) * LN2)                # 2^{s(y)}, real
sval = trigc(sc, yt).real                          # s(y), real
rw_min, rw_max, iw_max = 1e9, -1e9, 0.0
w_min, w_max, wi_max = 1e9, -1e9, 0.0
for t in ts:
    rr = trigc(rc, xt[:, None] + 1j * t + yt[None, :])
    re_r, im_r = rr.real, rr.imag
    rw_min = min(rw_min, re_r.min()); rw_max = max(rw_max, re_r.max())
    iw_max = max(iw_max, np.abs(im_r).max())
    wv = re_r + sval[None, :]
    w_min = min(w_min, wv.min()); w_max = max(w_max, wv.max())
    wi_max = max(wi_max, np.abs(im_r).max())       # s is real: Im w = Im r_c
print(f"  Re r_c on the strip : [{rw_min:+.6f}, {rw_max:+.6f}]")
print(f"  |Im r_c| on the strip <= {iw_max:.6f}   (== max |Im w|)")
print(f"  Re w   on the strip : [{w_min:+.6f}, {w_max:+.6f}]")
theta_max = LN2 * wi_max
print(f"  theta_max = log2 * max|Im w| = {theta_max:.6f} rad   (cos = {math.cos(theta_max):+.6f})")

# crude majorants (the only ones available without trig minimisation in Lean)
S_cosh = sum((abs(rc[j]) + abs(rc[16 + j])) * math.cosh(A_OUT * (j + 1)) for j in range(16))
S_sinh = sum((abs(rc[j]) + abs(rc[16 + j])) * math.sinh(A_OUT * (j + 1)) for j in range(16))
S2_cosh = sum((abs(sc[j]) + abs(sc[16 + j])) * math.cosh(A_OUT * (j + 1)) for j in range(16))
print(f"  crude Re r_c >= -{S_cosh:.6f}, |Im r_c| <= {S_sinh:.6f}, Re s >= -{S2_cosh:.6f}")
rho_min_true, rho_max_true = w_min, w_max
rho_min_crude, rho_max_crude = -S_cosh - S2_cosh, S_cosh + S2_cosh
print(f"  => crude  rho in [{rho_min_crude:+.4f}, {rho_max_crude:+.4f}], theta_max <= {LN2*S_sinh:.4f}")
for tag, rmin, rmax, th in (("TRUE ", rho_min_true, rho_max_true, theta_max),
                            ("CRUDE", rho_min_crude, rho_max_crude, LN2 * S_sinh)):
    R = 2.0 ** (rmax - rmin)
    lam_pt = 2.0 ** rmin * math.cos(th)                  # pointwise cos route
    lam_qd = 2.0 ** rmin * (1 - R * th * th / 2)          # quadratic-cos route
    print(f"  {tag}: lam(pointwise cos) = {lam_pt:+.6f}   lam(quadratic) = {lam_qd:+.6f}"
          f"   [R=2^({rmax-rmin:.3f})={R:.3g}]")

# ---- §2: the true lam ------------------------------------------------------------
print()
print("=" * 78)
print("2. THE TARGET: min over the strip of Re P_c and of |P_c|")
print("=" * 78)
PX = 512
xt2 = np.arange(PX) * TWO_PI / PX
Pmin_re, Pmin_abs, arg = 1e9, 1e9, None
for t in np.linspace(-A_OUT, A_OUT, 21):
    z = xt2[:, None] + 1j * t
    Pz = (np.exp(trigc(rc, z + yt[None, :]) * LN2) * srow[None, :]).mean(axis=1)
    if Pz.real.min() < Pmin_re:
        Pmin_re = Pz.real.min(); arg = (t, float(xt2[int(Pz.real.argmin())]))
    Pmin_abs = min(Pmin_abs, np.abs(Pz).min())
print(f"  min Re P_c = {Pmin_re:.9f}  (at t = {arg[0]:+.3f}, x = {arg[1]:.3f})")
print(f"  min |P_c|  = {Pmin_abs:.9f}")
print(f"  max |P_c|  = (see §3 Pmaj)")

# ---- §3: the numbers in (*) ------------------------------------------------------
print()
print("=" * 78)
print("3. THE NUMBERS IN THE REDUCTION (*)")
print("=" * 78)
Pmaj = math.exp(LN2 * (S_cosh + S2_cosh))
Ymaj = (S_cosh + S2_cosh) * Pmaj
print(f"  Zf = {Zf:.10f}  Zg = {Zg:.10f}  LZ = {LZ:+.10f}")
print(f"  Zfk = {Zfk:.10f}  Zgk = {Zgk:.10f}  H_ = {H_:+.10f}")
print(f"  kappa*LZ + H_ = {kap*LZ + H_:+.10f}   (the additive constant in (*))")
print(f"  S = S_cosh(r)+S_cosh(s) = {S_cosh + S2_cosh:.6f}  -> Pmaj = e^(ln2*S) = {Pmaj:.4f}")
print(f"  Ymaj = S*Pmaj = {Ymaj:.4f}    (the proved majorant of |Y_c|)")
print()
print(f"  {'lam':>8} {'Re u lower':>12} {'Re v upper':>12}")
for lam in (Pmin_re, Pmin_abs, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3):
    lo_u = math.log2(lam) - (kap - 1) * (Ymaj / lam) - (kap * LZ + H_)
    hi_v = (2 - kap) * (Ymaj / lam) - 2 * math.log2(lam) + (kap * LZ + H_)
    print(f"  {lam:8.4f} {lo_u:12.4f} {hi_v:12.4f}"
          f"   {'U ok' if lo_u >= -1.326 else 'U FAIL':>7} {'W ok' if hi_v <= 19.178 else 'W FAIL':>7}")
print("  true measured Re u >= %.6f, Re v <= %.6f" % (rep["strip"].get("umin", float('nan')),
                                                      rep["strip"].get("vmax", float('nan'))))
print(f"  NOTE the reduction is very loose in Re v (Ymaj/lam = {Ymaj/Pmin_re:.2f});")
print(f"       the Y-term penalty on Re u is (kappa-1)*Ymaj/lam = {(kap-1)*Ymaj/Pmin_re:.4f}")

# ---- §4: the enclosure arithmetic for hcmp ---------------------------------------
print()
print("=" * 78)
print("4. THE ENCLOSURE FOR hcmp AT 3e-7 ABSOLUTE")
print("=" * 78)
Pr, _ = None, None
th = trigc(rc, xt2[:, None] + yt[None, :])
Fi = np.exp(th * LN2)
P = (Fi * srow[None, :]).mean(axis=1)
Y = (Fi * th * srow[None, :]).mean(axis=1) + (Fi * (trigc(sc, yt) * srow)[None, :]).mean(axis=1)
Lc = np.log(P) / LN2 - LZ
Bc = Y / P - LZ
u = (Lc + (kap - 1) * Bc - H_).real
v = ((2 - kap) * Bc - 2 * Lc + H_).real
w = 2 + 2 * np.cos(xt2)
F1 = w * np.exp(p * (Delta - u) * LN2)
F2 = w * np.exp(q * (aG * v - u) * LN2)
M1, M2 = F1.mean(), F2.mean()
print(f"  M1 = {M1:.12f}   log2 = {math.log2(M1):.15f}   margin {rhoC-math.log2(M1):+.3e}")
print(f"  M2 = {M2:.12f}   log2 = {math.log2(M2):.15f}   margin {rhoC-math.log2(M2):+.3e}")
w1new = 2.0 ** rhoC
print(f"  2^rho_c = {w1new:.12f}   room after 1e-6 = {w1new - M1 - 1e-6:+.3e}"
      f"   after 3e-7 = {w1new - M1 - 3e-7:+.3e}")
print()
# sensitivity: dM/du
dM_du = (F1 * (-p * LN2)).mean()
print(f"  dM1/d(u) (mean over theta) = {dM_du:+.6f}  -> absolute du per 1e-7 of M:"
      f" {1e-7/abs(dM_du):.3e}")
n = 256
thk = np.arange(n) * TWO_PI / n
F1k = (2 + 2 * np.cos(thk)) * np.exp(p * (Delta - u[np.searchsorted(xt2, thk) % PX]) * LN2)
print(f"  trapMean-256 vs true mean (same u field): {F1k.mean() - M1:+.3e}")
print(f"  quadrature error bound at n=256 (JV1000Decay): 1e-6  [consumed by §7]")
print(f"  room left for the enclosure: {(w1new - M1) - 1e-6:+.3e}")
# The falsity of `eps <= 1e-20` at K=32 is NOT a tail-sum estimate that could be loose: the
# residual r_K(x) = sum_{|k|>K} c_k e^{ikx} has sup-norm at least its mean square, so a single
# measured coefficient already refutes the premise.
rms32 = math.sqrt(2 * sum(abs(c) ** 2 for c in
                          [c1k for c1k in np.fft.fft(F1) / len(F1)][33:len(F1) // 2]))
print(f"  residual RMS lower bound at K=32: {rms32:.3e}  (so sup|r_32| >= {rms32:.3e} >> 1e-20)")
# what precision on P does 3e-7 on M demand?
dM_dP = (F1 * (-p * LN2) * (1.0 / P)).mean()
rel = 3e-7 / abs((F1 * (-p * LN2)).mean() * 1.0)
print(f"  |dM/dlogP| ≈ {abs((F1*(p*LN2)).mean()):.4f} -> relative precision on |P| needed:"
      f" {3e-7/abs((F1*(p*LN2)).mean()):.3e}")
# inner trapezoid: the inner integrand 2^{r+s} is entire, strip sigma
for sigma in (0.3,):
    for nin in (128, 256, 512, 1024, 2048, 4096):
        err = math.exp(-sigma * nin)
        print(f"    inner n={nin:5d}, sigma={sigma}: eps ~ e^(-sigma n) = {err:.2e}")
print()
print("  VERDICT LINE: the 3e-7 enclosure needs |P| (hence LZ, H_, Zf, Zg, Zfk, Zgk and the")
print("  256 pointwise u values) enclosed to the relative precision printed above.  Every one")
print("  of those is an integral of 2^{trig16}; no rigorous enclosure of one exists in the lane.")
