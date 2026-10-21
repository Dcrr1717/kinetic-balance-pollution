"""Theorem T1-bounded: pollution dichotomy for BOUNDED potentials.
Verification battery (math_daniel protocol; symbols: ../../math-context.md;
uses L1'-A fiber decomposition and L2 step 1, both proven).

Statements verified here:
(T1a) Fiber Rayleigh classification, R(u) = <u,h(p)u>/<u,u>, t = p/2c:
      R_bal  = c^2(1+3t^2)/(1+t^2)  >= c^2   (equality iff t=0)
      R_spl  = c^2                            (edge, never inside)
      R_pos  = -c^2(1+3t^2)/(1+t^2) <= -c^2
      R_anti = c^2(5t^2-1)/(1+t^2), STRICTLY inside (-c^2, c^2)
               for all 0 < t < 1/sqrt(2); equals mid-gap 0 at t=1/sqrt(5).
(T1b) Bounded-window dichotomy. W = diag(Vd, Vd), ||Vd|| <= v.
      G_v := (-c^2+v, c^2-v).  Then:
      (i)   spec(H0 + W) avoids G_v                        [Weyl]
      (ii)  balanced Galerkin:  all eigenvalues >= c^2 - v [no pollution
            in G_v]; positronic: all <= -c^2 + v; split: within v of c^2.
      (iii) anti-balanced Galerkin: sorted eigenvalues lie within v of the
            sorted R_anti(t_j); every fiber with |R_anti(t_j)| < c^2 - 2v
            forces a Galerkin eigenvalue INSIDE G_v, where (i) says the
            parent matrix has no spectrum: guaranteed genuine pollution.
Scope: V bounded. Coulomb (unbounded) is outside T1-bounded and remains
the open T1-Coulomb (Lewin-Sere compressions / form-relative Weyl).
"""

import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

t0 = time.perf_counter()
rng = np.random.default_rng(20260712)

# ---------------- V1: symbolic Rayleigh classification -----------------
import sympy as sp

t, c = sp.symbols('t c', positive=True)
p = 2 * c * t
h = sp.Matrix([[c**2, c * p], [c * p, -c**2]])


def rayleigh(u):
    u = sp.Matrix(u)
    return sp.simplify((u.T * h * u)[0] / (u.T * u)[0])


R_bal = rayleigh([1, t])
R_spl = rayleigh([1, 0])
R_pos = rayleigh([-t, 1])
R_anti = rayleigh([t, 1])
print("V1 Rayleigh values:")
print("  R_bal  =", R_bal, " | R_bal - c^2 =",
      sp.simplify(R_bal - c**2), " (>=0 since 2c^2t^2/(1+t^2))")
print("  R_spl  =", R_spl)
print("  R_pos  =", sp.simplify(R_pos), " | R_pos + c^2 =",
      sp.simplify(R_pos + c**2))
print("  R_anti =", R_anti)
print("  in-gap upper: c^2 - R_anti =", sp.simplify(c**2 - R_anti),
      " (>0 iff t^2<1/2)")
print("  in-gap lower: R_anti + c^2 =", sp.simplify(R_anti + c**2),
      " (>0 iff t>0)")
print("  R_anti at t=1/sqrt(5):", sp.simplify(R_anti.subs(t, 1 / sp.sqrt(5))))

# ---------------- shared builders --------------------------------------
def family_vectors(U, Vt, T, kind):
    n = U.shape[0]
    Z = np.zeros((n, n))
    up, lo = {"spl": (U, Z), "bal": (U, Vt.T * T),
              "pos": (-U * T, Vt.T), "anti": (U * T, Vt.T)}[kind]
    C = np.vstack([up, lo])
    return C / np.linalg.norm(C, axis=0)


def rayleigh_np(tv, kind):
    if kind == "bal":
        return (1 + 3 * tv**2) / (1 + tv**2)
    if kind == "spl":
        return np.ones_like(tv)
    if kind == "pos":
        return -(1 + 3 * tv**2) / (1 + tv**2)
    return (5 * tv**2 - 1) / (1 + tv**2)          # anti


def check_case(K, cv, Vd, tol=1e-9):
    """Run all T1b checks for one (K, Vd). Returns dict of margins
    (all should be >= -tol)."""
    n = K.shape[0]
    U, S, Vt = np.linalg.svd(K)
    T = S / (2 * cv)
    v = np.linalg.norm(Vd, 2)
    W = np.block([[Vd, np.zeros((n, n))], [np.zeros((n, n)), Vd]])
    H0 = np.block([[cv**2 * np.eye(n), cv * K], [cv * K.T, -cv**2 * np.eye(n)]])
    out = {}
    # (i) parent spectrum avoids G_v
    ev = np.linalg.eigvalsh(H0 + W)
    ingap = ev[(ev > -cv**2 + v) & (ev < cv**2 - v)]
    out["parent_avoids_Gv"] = -ingap.size          # 0 if none
    # (ii)+(iii) Galerkin per family
    for kind in ("bal", "pos", "spl", "anti"):
        C = family_vectors(U, Vt, T, kind)
        A = C.T @ (H0 + W) @ C                    # C orthonormal columns
        eA = np.sort(np.linalg.eigvalsh(0.5 * (A + A.T)))
        R = np.sort(cv**2 * rayleigh_np(T, kind))
        # Weyl pairing: |eig_k - R_k| <= ||C^T W C|| <= v
        out[f"weyl_{kind}"] = float(v - np.max(np.abs(eA - R)))
        if kind == "bal":
            out["bal_window"] = float(eA.min() - (cv**2 - v))
        if kind == "pos":
            out["pos_window"] = float((-cv**2 + v) - eA.max())
        if kind == "anti":
            # guaranteed pollution: every fiber with |R|<c^2-2v must
            # produce an eigenvalue inside G_v
            deep = np.abs(R) < cv**2 - 2 * v
            if deep.any():
                got = ((eA > -cv**2 + v) & (eA < cv**2 - v)).sum()
                out["anti_pollution"] = float(got - deep.sum())  # >= 0
    return out


# ---------------- V2: random matrices ----------------------------------
worst = {}
for n in (2, 3, 5):
    for _ in range(20):
        cv = 10 ** rng.uniform(0.5, 2.5)
        K = rng.normal(size=(n, n)) * cv * rng.uniform(0.02, 0.6)
        M = rng.normal(size=(n, n))
        Vd = 0.5 * (M + M.T)
        Vd *= rng.uniform(0.05, 0.45) * cv**2 / np.linalg.norm(Vd, 2)
        for k, m in check_case(K, cv, Vd).items():
            worst[k] = min(worst.get(k, np.inf), m)
print("\nV2 random (n in 2,3,5 x 20) worst margins (>=0 required):")
for k, m in worst.items():
    print(f"   {k:>18}: {m:+.2e}")

# ---------------- V3: real Laguerre system -----------------------------
from dirac import RadialDiracBasis  # noqa: E402

B = RadialDiracBasis(240, -1, 0.0, 0.9, cert_tol=1e-6)
K = B._me(B.f, 2.0 * B.c * B.h)
V0, lam = 500.0, 1.0                              # bounded well, depth 500 Ha
Vfun = -V0 * np.exp(-lam * B.r)
Vd = B._mev(B.f, Vfun, B.f)
Vd = 0.5 * (Vd + Vd.T)
vnorm = np.linalg.norm(Vd, 2)
print(f"\nV3 Laguerre nb=240, bounded well V0={V0}: ||Vd|| = {vnorm:.2f}"
      f"  (<= V0? {vnorm <= V0 + 1e-9})")
res = check_case(K, B.c, Vd)
for k, m in res.items():
    print(f"   {k:>18}: {m:+.2e}")

# locate the guaranteed impostors of the anti family explicitly
U, S, Vt = np.linalg.svd(K)
T = S / (2 * B.c)
R = B.c**2 * rayleigh_np(T, "anti")
deep = np.abs(R) < B.c**2 - 2 * vnorm
print(f"   anti fibers with |R| < c^2-2v: {deep.sum()} of {len(T)}"
      f"  (t range {T.min():.3f}..{T.max():.3f});"
      f" deepest predicted impostor at R = {R[np.argmin(np.abs(R))]:.1f} Ha"
      f" (mid-gap = 0, fiber t = {T[np.argmin(np.abs(R))]:.4f},"
      f" 1/sqrt(5) = {1/np.sqrt(5):.4f})")
print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
