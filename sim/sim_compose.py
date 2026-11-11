#!/usr/bin/env python3
"""jv1000 C6 round 20 — the COMPOSITION passage, measured before proved.

Round 19 landed `hdecay` (`JV1000Decay.lean`): a strip-analytic 2pi-periodic `g` with
sup `M` on `|Im z| < a` has Fourier coefficients `|c_k| <= M q^{|k|}` at `q = e^{-a}`,
and §6/§7 discharge the quadrature bound at `n = 256`.  What that file NAMED but did not
write is the instantiation: `u`, `v` are `log2` of strip-analytic integrals, so the
composite moment integrand

    F_c(z) = (2 + 2 cos z) * 2^{p (Delta - u_c(z))}          (M1)
    F_c(z) = (2 + 2 cos z) * 2^{q (aG v_c(z) - u_c(z))}     (M2)

is holomorphic on `|Im z| < 1/5` with a sup on the certifier's own integer ceiling.

Four things this script measures, in the order the round needs them:

  1. **Does `P_c` avoid the log branch cut?**  `u` contains `log2 P`; on the complex
     strip the honest object is `Complex.log`, differentiable off `(-inf, 0]`.  The
     composition is only holomorphic if `P_c(z) != 0` AND `P_c(z)` avoids the negative
     real axis.  Measured: min Re P_c over the strip, and whether Im P_c ever changes
     sign while Re P_c < 0.
  2. **Is `Re u_c` bounded on the strip, and by what?**  The sup bound is
     `|2+2cos z| <= 2+2cosh(0.2)` times `2^{p(Delta - inf Re u)}`; the certifier carries
     `U* = |Re u|` bound from its contour-split contraction (`q0`).  Measured here:
     inf/sup of Re u_c, Re v_c over the strip, vs `U*`, `W*`.
  3. **The composite sup, against the integer ceiling.**  `M <= W_out * 2^{ceil(sup)}`
     with `ceil(sup1) = 12`, `ceil(sup2) = 21` -> `M2 = 8472775`, the number
     `quadrature_at_256_of_strip` takes as `hMle`.
  4. **Where `Re u` actually peaks** — the sup of the product is NOT at the point
     maximising `Re u`, because `|2+2cos z|` moves independently.  Measured separately so
     the Lean statement is not silently about the wrong point.

Run: python3 sim/sim_compose.py
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

A_OUT = 0.2          # 2*beta: the outer strip the moment integrand must be holomorphic on
A_IN = 0.3           # sigma: the inner strip P, Y live on
U, W = rep["strip"]["Ustar"], rep["strip"]["Wstar"]
W_OUT = 2 + 2 * math.cosh(A_OUT)


def trigc(co, th):
    """The complex analytic continuation of trig16: cos/sin of a complex argument."""
    out = np.zeros_like(th, dtype=complex)
    for j in range(16):
        out += co[j] * np.cos((j + 1) * th) + co[16 + j] * np.sin((j + 1) * th)
    return out


def pow2c(w):
    """2^w for complex w — exp(w log 2), the ONLY reading that is entire."""
    return np.exp(w * LN2)


# --- reference (real-axis) constants, from the same grid the earlier rounds used ------
N = 4096
xs = np.arange(N) * TWO_PI / N
ys = np.arange(N) * TWO_PI / N
F = pow2c(trigc(rc, xs))
G = pow2c(trigc(sc, ys))
Zf, Zg = F.mean(), G.mean()
Zfk = pow2c(kap * trigc(rc, xs)).mean()
Zgk = pow2c(kap * trigc(sc, ys)).mean()
LZ = math.log2(Zf.real * Zg.real)
H_ = math.log2(Zfk.real) + math.log2(Zgk.real) - kap * LZ


def PY(x):
    """P(x), Y(x) on the real axis (continuum, N-node trapezoid)."""
    th = trigc(rc, x[:, None] + ys[None, :])
    Fi = pow2c(th)
    Gi = G[None, :]
    P = (Fi * Gi).mean(axis=1)
    Y = (Fi * th * Gi + Fi * (G * trigc(sc, ys))[None, :]).mean(axis=1)
    return P, Y


def uv(P, Y):
    L = np.log(P) / LN2 - LZ
    B = Y / P - LZ
    return L + (kap - 1) * B - H_, (2 - kap) * B - 2 * L + H_


# --- real axis sanity: reproduce the round-17 certified values -----------------------
Pr, Yr = PY(xs)
ur, vr = uv(Pr, Yr)
w = 2 + 2 * np.cos(xs)
m1 = (w * pow2c(p * (Delta - ur))).real.mean()
m2 = (w * pow2c(q * (aG * vr - ur))).real.mean()
print("=" * 78)
print("0. REAL-AXIS SANITY (must reproduce round 17: 0.516268325851285)")
print("=" * 78)
print(f"  log2 M1 = {math.log2(m1):.15f}   margin {rhoC - math.log2(m1):+.3e}")
print(f"  log2 M2 = {math.log2(m2):.15f}   margin {rhoC - math.log2(m2):+.3e}")

# --- 1..4: the strip, z = x + i t, |t| <= A_OUT -------------------------------------
print()
print("=" * 78)
print("1. P_c ON THE STRIP: does it avoid the log branch cut?")
print("=" * 78)
NX, NT = 512, 21
ts = np.linspace(-A_OUT, A_OUT, NT)
Pmin_re, Pmax_abs, worst = 1e9, 0.0, None
neg_cross = []
for t in ts:
    z = xs + 1j * t
    Pz, Yz = PY(z)
    re, im = Pz.real, Pz.imag
    if re.min() < Pmin_re:
        Pmin_re, worst = re.min(), (t, xs[re.argmin()])
    Pmax_abs = max(Pmax_abs, np.abs(Pz).max())
    # does P_c cross the negative real axis?  sign change of Im between adjacent nodes
    s = np.sign(im)
    flip = np.nonzero(s[:-1] * s[1:] < 0)[0]
    for k in flip:
        if re[k] < 0 or re[k + 1] < 0:
            neg_cross.append((t, float(xs[k])))
print(f"  min over strip of Re P_c      = {Pmin_re:.9f}   (at Im t = {worst[0]:+.3f})")
print(f"  max over strip of |P_c|       = {Pmax_abs:.6f}")
print(f"  Im P_c sign changes with Re < 0  : {len(neg_cross)} occurrences")
print(f"  radius of the disc around 0 the image avoids: >= {Pmin_re:.6f} > 0")
print("  VERDICT: P_c maps the strip into the OPEN RIGHT HALF-PLANE" if Pmin_re > 0
      else "  VERDICT: FAILS — the strip image touches Re <= 0")

print()
print("=" * 78)
print("2. Re u_c, Re v_c ON THE STRIP (the sup constant)")
print("=" * 78)
umin, umax, vmin, vmax = 1e9, -1e9, 1e9, -1e9
sup1, sup2, arg1, arg2 = 0.0, 0.0, None, None
for t in ts:
    z = xs + 1j * t
    Pz, Yz = PY(z)
    Lc = np.log(Pz) / LN2 - LZ
    Bc = Yz / Pz - LZ
    uc = Lc + (kap - 1) * Bc - H_
    vc = (2 - kap) * Bc - 2 * Lc + H_
    umin, umax = min(umin, uc.real.min()), max(umax, uc.real.max())
    vmin, vmax = min(vmin, vc.real.min()), max(vmax, vc.real.max())
    wc = np.abs(2 + 2 * np.cos(z))
    f1 = wc * pow2c(p * (Delta - uc)).real if False else wc * np.exp(p * (Delta - uc.real) * LN2)
    f2 = wc * np.exp(q * (aG * vc.real - uc.real) * LN2)
    if f1.max() > sup1:
        sup1, arg1 = f1.max(), (t, xs[f1.argmax()])
    if f2.max() > sup2:
        sup2, arg2 = f2.max(), (t, xs[f2.argmax()])
print(f"  Re u_c in [{umin:+.6f}, {umax:+.6f}]   |Re u| <= {max(-umin, umax):.6f}   (certifier U* = {U:.6f})")
print(f"  Re v_c in [{vmin:+.6f}, {vmax:+.6f}]   |Re v| <= {max(-vmin, vmax):.6f}   (certifier W* = {W:.6f})")
print(f"  the certifier's U*, W* are {'CONSERVATIVE' if (U >= max(-umin,umax) and W >= max(-vmin,vmax)) else 'TOO SMALL'}")

print()
print("=" * 78)
print("3. THE COMPOSITE SUP vs THE INTEGER CEILING")
print("=" * 78)
ceil1, ceil2 = math.ceil(p * (Delta + U)), math.ceil(q * (aG * W + U))
print(f"  |2+2cos z| <= 2+2cosh({A_OUT}) = {W_OUT:.9f}")
print(f"  sup1 = p(Delta+U*) = {p*(Delta+U):.6f} -> ceil {ceil1} -> M = {W_OUT*2**ceil1:.1f}")
print(f"  sup2 = q(aG W*+U*) = {q*(aG*W+U):.6f} -> ceil {ceil2} -> M = {W_OUT*2**ceil2:.1f}")
print(f"  MEASURED sup on the strip: M1 {sup1:.4e} (at t={arg1[0]:+.3f})  M2 {sup2:.4e} (at t={arg2[0]:+.3f})")
print(f"  ceiling 8472775 covers M1 by {8472775/sup1:.3e}x, M2 by {8472775/sup2:.3e}x")
assert sup1 <= W_OUT * 2 ** ceil1 and sup2 <= W_OUT * 2 ** ceil2

print()
print("=" * 78)
print("4. THE QUADRATURE BOUND AT n = 256, FED BY THIS SUP")
print("=" * 78)
for name, sup, ceil, mg in (("M1", sup1, ceil1, rhoC - math.log2(m1)),
                            ("M2", sup2, ceil2, rhoC - math.log2(m2))):
    M = W_OUT * 2 ** ceil
    qn = math.exp(-A_OUT) ** 256
    eps = 2 * M / (math.exp(A_OUT * 256) - 1)
    print(f"  {name}: M = {M:.6e}  q^256 = {qn:.3e}  eps(256) = 2M/(e^{A_OUT*256}-1) = {eps:.3e}")
    print(f"      target 1e-6: {'PASS' if eps <= 1e-6 else 'FAIL'}   (bound in JV1000Decay is"
          f" M*q^256*(2K+1)+2eps <= 1e-6)")
print()
print("  NOTE the Lean §7 bound is M*q^n*(2K+1)+2eps, NOT the 2M/(e^{an}-1) form;")
print("  at M = 8472775, K = 32: 8472775*e^{-51.2}*65 = "
      f"{8472775*math.exp(-51.2)*65:.3e} + 2*eps = {2*8472775/(math.exp(51.2)-1):.3e}")
