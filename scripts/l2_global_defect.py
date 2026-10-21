"""Lemma L2: EXACT global conformity defect of untruncated single-family
trial prescriptions, by fiber block-diagonalization (math-rigor protocol;
symbols: ../../math-context.md; L1'-fiber: l1prime_fiber_lemma.py).

Claims verified here:
(L2a) Per-fiber defect identity: for unit vectors b, v in R^2 and
      P = v v^T:  ||(I - b b^T) P b|| = |<v,b>| sqrt(1 - <v,b>^2).
(L2b) Block law: for single-family spans V_N = span{b_j} (one trial
      vector per SVD fiber), (I-Pi)Lambda+ Pi is block-diagonal and
      delta_N = max_j l_j sqrt(1 - l_j^2), with l_j the L1' leakage.
      The same value is obtained with Lambda- (per-fiber symmetry
      <v+,b>^2 + <v-,b>^2 = 1).
(L2c) The FULL DKB pair space (both families, untruncated) spans every
      fiber entirely -> delta = 0 exactly.
(L2d) Scale law: sigma_max(N) of the Laguerre K grows ~ N^q (measured),
      hence delta_N^bal ~ (sigma_max/2c)^3 grows with N at fixed beta --
      the growth observed in FINDINGS #6 now has an exact mechanism.
"""

import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

t0 = time.perf_counter()
rng = np.random.default_rng(20260711)

# ---------------- V1: symbolic per-fiber identity ----------------------
import sympy as sp

# Coordinate-free chain (the actual proof): w := (I-bb^T)Pb = g(v - gb)
# with g = <v,b>, ||b|| = ||v|| = 1, hence ||w||^2 = g^2(1 - 2g^2 + g^2).
gsym = sp.Symbol('g', real=True)
print("V1 scalar chain residual:",
      sp.expand(gsym**2 * (1 - 2 * gsym**2 + gsym**2)
                - gsym**2 * (1 - gsym**2)))
# parametrized 2D confirmation, rotationally reduced (a = q + s)
q, s = sp.symbols('q s', real=True)
b = sp.Matrix([sp.cos(q + s), sp.sin(q + s)])
v = sp.Matrix([sp.cos(q), sp.sin(q)])
w = (sp.eye(2) - b * b.T) * (v * v.T) * b
g = v.dot(b)
resid = sp.simplify(sp.expand_trig(sp.expand(w.dot(w) - g**2 * (1 - g**2))))
print("V1 parametrized residual (a = q + s):", resid)
# complement identity <v+,b>^2 + <v-,b>^2 = 1 (v- = rotate(v+, pi/2))
vperp = sp.Matrix([-sp.sin(q), sp.cos(q)])
print("V1b complement identity:",
      sp.simplify(v.dot(b)**2 + vperp.dot(b)**2 - 1))


# ---------------- shared builders --------------------------------------
def leak_formulas(tv):
    rv = 2 * tv / (1 + np.sqrt(1 + 4 * tv**2))
    A, Bn = np.sqrt(1 + rv**2), np.sqrt(1 + tv**2)
    return dict(spl=rv / A, bal=(tv - rv) / (A * Bn),
                pos=(tv - rv) / (A * Bn), anti=(tv + rv) / (A * Bn))


def family_vectors(U, Vt, T, kind):
    """Untruncated single-family trial vectors (columns), ref coords."""
    n = U.shape[0]
    Z = np.zeros((n, n))
    if kind == "spl":
        up, lo = U, Z
    elif kind == "bal":
        up, lo = U, Vt.T * T
    elif kind == "pos":
        up, lo = -U * T, Vt.T
    elif kind == "anti":
        up, lo = U * T, Vt.T
    C = np.vstack([up, lo])
    return C / np.linalg.norm(C, axis=0)


def defect(Lam, C):
    Q, _ = np.linalg.qr(C)
    LQ = Lam @ Q
    return np.linalg.norm(LQ - Q @ (Q.T @ LQ), 2)


def check_case(K, cv):
    U, S, Vt = np.linalg.svd(K)
    T = S / (2 * cv)
    n = K.shape[0]
    H0 = np.block([[cv**2 * np.eye(n), cv * K], [cv * K.T, -cv**2 * np.eye(n)]])
    ev, W = np.linalg.eigh(H0)
    Lp = W[:, ev > 0] @ W[:, ev > 0].T
    Lm = np.eye(2 * n) - Lp
    out = {}
    for kind in ("spl", "bal", "pos", "anti"):
        C = family_vectors(U, Vt, T, kind)
        ells = np.array([leak_formulas(tv)[kind] for tv in T])
        want = np.max(ells * np.sqrt(1.0 - ells**2))
        out[kind] = (defect(Lp, C), defect(Lm, C), want)
    # full DKB pair space (bal + pos): spans every fiber
    Cfull = np.hstack([family_vectors(U, Vt, T, "bal"),
                       family_vectors(U, Vt, T, "pos")])
    out["dkb-full"] = (defect(Lp, Cfull), defect(Lm, Cfull), 0.0)
    return out


# ---------------- V2: random K ------------------------------------------
worst = 0.0
for n in (2, 3, 5):
    for _ in range(20):
        cv = 10 ** rng.uniform(0, 2.5)
        K = rng.normal(size=(n, n)) * cv * rng.uniform(0.01, 0.5)
        for kind, (dp, dm, want) in check_case(K, cv).items():
            worst = max(worst, abs(dp - want), abs(dm - want))
print(f"V2 random K n in (2,3,5) x 20, both Lambda+/-: max |delta - formula| = {worst:.1e}")

# ---------------- V3: real Laguerre reference ---------------------------
from dirac import RadialDiracBasis  # noqa: E402

B = RadialDiracBasis(240, -1, 0.0, 0.9, cert_tol=1e-6)
K = B._me(B.f, 2.0 * B.c * B.h)
print("V3 Laguerre kappa=-1 beta=0.9 nb=240 (untruncated prescriptions):")
for kind, (dp, dm, want) in check_case(K, B.c).items():
    print(f"   {kind:>8}: delta(L+) = {dp:.6e}  delta(L-) = {dm:.6e}"
          f"  formula = {want:.6e}  |diff| = {abs(dp - want):.1e}")

# ---------------- V4: sigma_max(N) scale law ----------------------------
# NOTE: N=480 FAILS certification C1 (0.31): the Legendre-quadrature
# envelope (nq = 16 nb, default xmax) is exceeded there -- the assembly
# certification catches it, so the scale law is fitted on certified
# builds only.
print("V4 sigma_max(N), Laguerre kappa=-1 beta=0.9 (certified builds):")
Ns, sig = [], []
for N in (60, 120, 240, 360):
    Bn = RadialDiracBasis(N, -1, 0.0, 0.9, cert_tol=1e-5)
    Kn = Bn._me(Bn.f, 2.0 * Bn.c * Bn.h)
    s = np.linalg.svd(Kn, compute_uv=False)
    Ns.append(N)
    sig.append(s[0])
    print(f"   N={N:>4}: sigma_max = {s[0]:.4f}   t_max = {s[0]/(2*Bn.c):.4f}")
qfit = np.polyfit(np.log(Ns), np.log(sig), 1)[0]
print(f"   fitted growth exponent q (sigma_max ~ N^q) = {qfit:.3f}")
print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
