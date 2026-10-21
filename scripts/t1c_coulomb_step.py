"""T1-Coulomb, step 1: spectral inclusion and conditional protection from
MEASURABLE relative bounds (math_daniel protocol; math-context v1.1;
uses the fiber structure of L1'/L2 and |H0| = E(sigma_j) I per fiber).

Propositions verified here (finite-dimensional, W symmetric, possibly
UNBOUNDED-potential compressions like Coulomb):

(P1) Resolvent inclusion window. a_N := ||W (H0)^-1||_2.  For real E with
     |E| < c^2 (1 - a_N):  E is not an eigenvalue of H0 + W.
     Proof: H0+W-E = (I + W(H0-E)^-1)(H0-E); ||W(H0-E)^-1|| <=
     ||W H0^-1|| * ||H0 (H0-E)^-1|| = a_N * c^2/(c^2-|E|) < 1.

(P2) Conditional mid-gap protection of the balanced family.
     alpha_N := || |H0|^-1/2 W |H0|^-1/2 ||_2  (form bound), and
     g(t) := R_bal(t)/E(t) = (1+3t^2)/((1+t^2) sqrt(1+4t^2)) in (0,1].
     Then min eig(Galerkin_bal(H0+W)) >= min_j E_j (g(t_j) - alpha_N).
     In particular alpha_N < min_j g(t_j) = g(t_max)  ==>  the balanced
     Galerkin has NO eigenvalue at or below mid-gap (0), for ANY
     symmetric W with that form bound -- Coulomb included.
     (Positronic family: mirror statement above 0 by symmetry.)

Necessity check (P-c): the physical 1s at E = gamma c^2 belongs to
spec(H0+W), so P1 forces a_N >= 1 - gamma.  We measure sharpness.

Real-system measurements: gamma-basis + exact cusp quadrature, kappa=-1,
Coulomb V = -Z/r (exact integrals), Z in {40, 92, 118, 130}, N in
{40, 80, 160}: convergence of a_N and alpha_N, the ratio a_N/(1-gamma),
and the P2 condition alpha_N vs g(t_max) in the distinguished regime.
"""

import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

t0 = time.perf_counter()
rng = np.random.default_rng(20260713)


def g_ratio(tv):
    return (1 + 3 * tv**2) / ((1 + tv**2) * np.sqrt(1 + 4 * tv**2))


def build(K, cv, Vd):
    n = K.shape[0]
    H0 = np.block([[cv**2 * np.eye(n), cv * K], [cv * K.T, -cv**2 * np.eye(n)]])
    W = np.block([[Vd, np.zeros((n, n))], [np.zeros((n, n)), Vd]])
    return H0, W


def bounds(H0, W, cv):
    ev, U = np.linalg.eigh(H0)
    a_N = np.linalg.norm(W @ U @ np.diag(1.0 / ev) @ U.T, 2)
    S = U @ np.diag(1.0 / np.sqrt(np.abs(ev))) @ U.T      # |H0|^{-1/2}
    alpha_N = np.linalg.norm(S @ W @ S, 2)
    return a_N, alpha_N


def balanced_galerkin(K, cv, H0W):
    n = K.shape[0]
    U, S, Vt = np.linalg.svd(K)
    T = S / (2 * cv)
    C = np.vstack([U, Vt.T * T])
    C = C / np.linalg.norm(C, axis=0)
    A = C.T @ H0W @ C
    return np.linalg.eigvalsh(0.5 * (A + A.T)), T


# ---------------- V1: random-matrix verification of P1 and P2 ----------
worst_p1, worst_p2 = np.inf, np.inf
for n in (2, 3, 5):
    for _ in range(20):
        cv = 10 ** rng.uniform(0.5, 2.0)
        K = rng.normal(size=(n, n)) * cv * rng.uniform(0.05, 0.6)
        M = rng.normal(size=(n, n))
        Vd = 0.5 * (M + M.T) * cv**2 * rng.uniform(0.1, 1.5) / n
        H0, W = build(K, cv, Vd)
        a_N, alpha_N = bounds(H0, W, cv)
        # P1: no eigenvalue of H0+W inside the window
        ev = np.linalg.eigvalsh(H0 + W)
        win = cv**2 * (1 - a_N)
        if win > 0:
            inside = ev[np.abs(ev) < win - 1e-9 * cv**2]
            worst_p1 = min(worst_p1, -inside.size)
        # P2: balanced Galerkin min-eig >= min_j E_j (g_j - alpha)
        eA, T = balanced_galerkin(K, cv, H0 + W)
        Ej = cv**2 * np.sqrt(1 + 4 * T**2)
        bound = np.min(Ej * (g_ratio(T) - alpha_N))
        worst_p2 = min(worst_p2, float(eA.min() - bound))
print("V1 random n in (2,3,5) x 20:")
print(f"   P1 inside-window eigenvalue count (must be 0): {-worst_p1:.0f}")
print(f"   P2 margin min-eig - bound (must be >= 0): {worst_p2:+.2e}")

# ---------------- V2: real Coulomb system ------------------------------
from dirac import C_AU, RadialDiracBasis  # noqa: E402

C = C_AU
print("\nV2 gamma-basis + cusp, kappa=-1, Coulomb V=-Z/r (exact integrals):")
print(f"{'Z':>5} {'nu':>6} {'gam':>6} {'N':>4} {'a_N':>7} {'a/(1-gam)':>9}"
      f" {'alpha_N':>8} {'g(tmax)':>8} {'P2 ok':>6} {'minEig':>10} {'bound':>10}")
for Z in (40.0, 92.0, 118.0, 130.0):
    nu = Z / C
    gam = float(np.sqrt(1 - nu**2))
    for N in (40, 80, 160):
        B = RadialDiracBasis(N, -1, Z, 0.8 * Z, mu=gam, quad="cusp",
                             nquad=N + 150, cert_tol=1e-5)
        K = B._me(B.f, 2.0 * B.c * B.h)
        Vd = B._mev(B.f, B.V, B.f)
        Vd = 0.5 * (Vd + Vd.T)
        H0, W = build(K, C, Vd)
        a_N, alpha_N = bounds(H0, W, C)
        eA, T = balanced_galerkin(K, C, H0 + W)
        Ej = C**2 * np.sqrt(1 + 4 * T**2)
        bound = float(np.min(Ej * (g_ratio(T) - alpha_N)))
        gtm = float(g_ratio(T.max()))
        ok = alpha_N < gtm
        print(f"{Z:>5.0f} {nu:>6.3f} {gam:>6.3f} {N:>4} {a_N:>7.4f}"
              f" {a_N/(1-gam):>9.4f} {alpha_N:>8.4f} {gtm:>8.4f}"
              f" {str(ok):>6} {eA.min():>10.1f} {bound:>10.1f}")

print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
