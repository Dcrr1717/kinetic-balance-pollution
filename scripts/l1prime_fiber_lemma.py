"""Lemma L1'-fiber: EXACT per-mode leakage of kinetically-balanced trial
families w.r.t. the free-Dirac spectral splitting. Verification battery
per the math-rigor protocol (symbols/hypotheses: ../../math-context.md).

Claims verified here:
(A) Discrete SVD reduction: H0 = [[c^2 I, cK],[cK^T, -c^2 I]] decomposes
    into exact 2x2 fibers h(sigma_j) on span{(u_j,0),(0,v_j)}; spectral
    projectors decompose blockwise.
(B) Exact 2x2 leakages, r(t) = 2t/(1+sqrt(1+4t^2)), t = p/(2c):
      l_spl  = r/sqrt(1+r^2)                       = t - (3/2)t^3 + O(t^5)
      l_bal  = (t-r)/(sqrt(1+r^2)sqrt(1+t^2))      =       t^3    + O(t^5)
      l_pos  = same as l_bal                        (exponent 3)
      l_anti = (t+r)/(sqrt(1+r^2)sqrt(1+t^2))      = 2t - 3t^3    + O(t^5)
(C) The REAL Laguerre reference (kappa=-1, beta=0.9) obeys (A)+(B) at
    machine precision -> per-mode exponents are EXACTLY 3/1/3/1, replacing
    the mode-mixed fitted exponents 2.15/0.95/3.60/1.59 of FINDINGS #6.
"""

import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

t0 = time.perf_counter()
rng = np.random.default_rng(20260711)

# ---------------- V1: symbolic (sympy) --------------------------------
import sympy as sp

t, c = sp.symbols('t c', positive=True)
p = 2 * c * t
E = sp.sqrt(c**4 + c**2 * p**2)
r = 2 * t / (1 + sp.sqrt(1 + 4 * t**2))
h = sp.Matrix([[c**2, c * p], [c * p, -c**2]])
vp = sp.Matrix([1, r]) / sp.sqrt(1 + r**2)
vm = sp.Matrix([-r, 1]) / sp.sqrt(1 + r**2)

chk1 = sp.simplify(h * vp - E * vp)
chk2 = sp.simplify(h * vm + E * vm)
print("V1a eigen-identities: h*v+ - E*v+ =", chk1.T, " h*v- + E*v- =", chk2.T)

nb = sp.sqrt(1 + t**2)
l_spl = sp.simplify(sp.Abs(vm.dot(sp.Matrix([1, 0]))))
l_bal = sp.simplify(sp.Abs(vm.dot(sp.Matrix([1, t]))) / nb)
l_pos = sp.simplify(sp.Abs(vp.dot(sp.Matrix([-t, 1]))) / nb)
l_anti = sp.simplify(sp.Abs(vp.dot(sp.Matrix([t, 1]))) / nb)

forms = dict(spl=r / sp.sqrt(1 + r**2),
             bal=(t - r) / (sp.sqrt(1 + r**2) * nb),
             pos=(t - r) / (sp.sqrt(1 + r**2) * nb),
             anti=(t + r) / (sp.sqrt(1 + r**2) * nb))
for name, direct in dict(spl=l_spl, bal=l_bal, pos=l_pos, anti=l_anti).items():
    d = sp.simplify(sp.radsimp(direct - forms[name]))
    print(f"V1b closed form {name}: direct - formula = {d}")
# r(t) < t for t > 0  <=>  1 + sqrt(1+4t^2) > 2
print("V1c r<t check: simplify(t - r > 0) for t>0:",
      sp.simplify(sp.Gt(t - r, 0)))

for name in ("spl", "bal", "anti"):
    s = sp.series(forms[name], t, 0, 5)
    print(f"V1d series {name}: {s}")

# ---------------- V2: random numeric 2x2, three c-scales --------------
def leak2x2(cv, tv):
    pv = 2 * cv * tv
    hM = np.array([[cv**2, cv * pv], [cv * pv, -cv**2]])
    ev, U = np.linalg.eigh(hM)
    Lm = U[:, :1] @ U[:, :1].T          # negative-energy projector
    Lp = U[:, 1:] @ U[:, 1:].T
    def lk(P, u):
        u = np.asarray(u, float)
        return np.linalg.norm(P @ u) / np.linalg.norm(u)
    return (lk(Lm, [1, 0]), lk(Lm, [1, tv]), lk(Lp, [-tv, 1]), lk(Lp, [tv, 1]))


def formulas(tv):
    rv = 2 * tv / (1 + np.sqrt(1 + 4 * tv**2))
    a, b = np.sqrt(1 + rv**2), np.sqrt(1 + tv**2)
    return (rv / a, (tv - rv) / (a * b), (tv - rv) / (a * b), (tv + rv) / (a * b))


worst = 0.0
for cv in (1.0, 137.035999084, 1e3):
    for _ in range(20):
        tv = 10 ** rng.uniform(-4, np.log10(0.45))
        worst = max(worst, max(abs(np.array(leak2x2(cv, tv)) - np.array(formulas(tv)))))
for tv in (1e-8, 0.5, 5.0):                      # boundary/pathological
    worst = max(worst, max(abs(np.array(leak2x2(1.0, tv)) - np.array(formulas(tv)))))
print(f"V2 random 2x2 (3 c-scales x 20 + boundary t=1e-8,0.5,5): max abs dev = {worst:.1e}")

# ---------------- V3: random discrete K, SVD reduction ----------------
def permode_leaks(K, cv):
    n = K.shape[0]
    U, S, Vt = np.linalg.svd(K)
    H0 = np.block([[cv**2 * np.eye(n), cv * K], [cv * K.T, -cv**2 * np.eye(n)]])
    ev, W = np.linalg.eigh(H0)
    Lm = W[:, ev < 0] @ W[:, ev < 0].T
    Lp = np.eye(2 * n) - Lm
    out = []
    for j in range(n):
        tj = S[j] / (2 * cv)
        e1 = np.concatenate([U[:, j], np.zeros(n)])
        e2 = np.concatenate([np.zeros(n), Vt[j]])
        def lk(P, u):
            return np.linalg.norm(P @ u) / np.linalg.norm(u)
        got = (lk(Lm, e1), lk(Lm, e1 + tj * e2),
               lk(Lp, -tj * e1 + e2), lk(Lp, tj * e1 + e2))
        out.append((tj, got, formulas(tj)))
    return out


worst3 = 0.0
for n in (2, 3, 5):
    for _ in range(20):
        cv = 10 ** rng.uniform(0, 2.5)
        K = rng.normal(size=(n, n)) * cv * rng.uniform(0.01, 0.5)
        for tj, got, want in permode_leaks(K, cv):
            worst3 = max(worst3, max(abs(np.array(got) - np.array(want))))
print(f"V3 random K, n in (2,3,5) x 20: max |full-eigh - 2x2 formula| = {worst3:.1e}")

# ---------------- V4: the REAL Laguerre reference ----------------------
from dirac import RadialDiracBasis  # noqa: E402

B = RadialDiracBasis(240, -1, 0.0, 0.9, cert_tol=1e-6)
K = B._me(B.f, 2.0 * B.c * B.h)                 # <f_i|O+ f_j>
res = permode_leaks(K, B.c)
res.sort(key=lambda z: z[0])
worst4 = max(max(abs(np.array(g) - np.array(w))) for _, g, w in res)
print(f"V4 Laguerre kappa=-1 beta=0.9 nb=240: max |measured - formula| = {worst4:.1e}")
tj = np.array([z[0] for z in res])
low = (tj > 1e-4) & (tj < 2e-2)                  # asymptotic window
for i, name in enumerate(("spl", "bal", "pos", "anti")):
    y = np.array([z[1][i] for z in res])
    slope = np.polyfit(np.log(tj[low]), np.log(y[low]), 1)[0]
    coef = np.exp(np.mean(np.log(y[low]) - slope * np.log(tj[low])))
    print(f"   {name:>5}: fitted exponent = {slope:.4f}   leading const = {coef:.4f}")
print(f"   t-range of reference modes: [{tj.min():.2e}, {tj.max():.2e}]")
print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
