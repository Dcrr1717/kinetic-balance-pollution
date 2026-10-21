"""E-T1: universality of the L3c eigenvalue-rate law and its mechanism.

Pre-registered predictions:
P1  The eigenvalue-error decay exponent for a mismatched-prefactor basis
    is 2*gamma_kappa, INDEPENDENT of mu and kappa (only gamma matters),
    following L3b (universal coefficient exponent) + the dual first-order
    estimate  |dE| ~ C * ||(I-Pi)psi|| * ||(I-Pi) h psi||.
P2  Mechanism check (corrected in-run: the naive dual product
    ||(I-Pi)psi||*||(I-Pi)h psi|| is degenerate for an exact
    eigenfunction since h psi = E psi): the eigenvalue error is
    QUADRATIC in the |H0|-form norm of the projection residual,
        dE_N ~ <res_N, |H0| res_N>,   res_N = (I-Pi_N) psi,
    whose tail is sum_{j>N} c_j^2 E_j ~ N^{-2 gamma} by L3b -- the
    measured law.  Prediction: dE_N / <res,|H0|res> is O(1) and roughly
    N-independent (measured in a large nested reference).

Instrument note: Legendre quadrature (generic mu); quadrature error kept
far below the truncation error being measured (nq = 16N floor raised).
"""

import sys
import time
from decimal import Decimal, getcontext
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from dirac import C_AU, RadialDiracBasis, laguerre_funcs  # noqa: E402

getcontext().prec = 40
C = C_AU
t0 = time.perf_counter()


def exact_dec(nr, kappa, Z):
    cD, ZD = Decimal(repr(C)), Decimal(repr(float(Z)))
    nu = ZD / cD
    g = (Decimal(kappa * kappa) - nu * nu).sqrt()
    d = nu / (Decimal(nr) + g)
    return cD * cD / (Decimal(1) + d * d).sqrt() - cD * cD


def rate(kappa, Z, mu, Ns, beta_fac=0.8):
    ex = exact_dec(0, kappa, Z)
    errs = []
    for N in Ns:
        B = RadialDiracBasis(N, kappa, Z, beta_fac * Z, mu=mu,
                             nquad=max(6000, 24 * N), cert_tol=1e-4)
        ev = B.solve_naive(shifted=True)
        errs.append(abs(float((Decimal(repr(float(ev[0]))) - ex) / ex)))
    slope = np.polyfit(np.log(Ns), np.log(errs), 1)[0]
    return slope, errs


print("P1: eigenvalue-error exponent vs 2*gamma (prediction: -2*gamma):")
CASES = [(-1, 40.0, None), (-1, 80.0, None), (-1, 120.0, None),
         (-1, 80.0, "gam+0.3"), (-2, 80.0, None)]
for kappa, Z, mutag in CASES:
    nu = Z / C
    gam = float(np.sqrt(kappa * kappa - nu**2))
    mu = (gam + 0.3) if mutag else float((-kappa - 1 if kappa < 0 else kappa) + 1)
    Ns = (20, 40, 80, 160) if kappa == -1 else (10, 14, 20, 28)
    slope, errs = rate(kappa, Z, mu, Ns)
    print(f"   kappa={kappa} Z={Z:>4.0f} mu={mu:.3f} gamma={gam:.4f}:"
          f" exponent = {slope:+.3f}  (pred {-2*gam:+.3f})"
          f"   errs {errs[0]:.1e}->{errs[-1]:.1e}")

# ---------------- P2: form-norm mechanism (corrected) -------------------
print("\nP2 mechanism (kappa=-1, Z=80, mu=1): dE vs <res,|H0|res> in a"
      " nested reference (nb_ref=320, mu=1):")
kappa, Z = -1, 80.0
nu = Z / C
gam = float(np.sqrt(1 - nu**2))
lam = Z
# exact ground state (L3a): psi = (a, b) r^gamma e^{-Z r}; b/a from the
# r^{gamma-1} row condition: -Z a + c(kappa - gamma) b = 0
ab = np.array([1.0, Z / (C * (kappa - gam))])
Egs = float(exact_dec(0, kappa, Z))

Bref = RadialDiracBasis(320, kappa, Z, 0.8 * Z, mu=1.0, nquad=8000,
                        cert_tol=1e-4)
r, W = Bref.r, Bref.W
prof = r**gam * np.exp(-lam * r)
psi = np.vstack([ab[0] * prof, ab[1] * prof])
psi /= np.sqrt(np.sum(W * (psi**2).sum(0)))
cu = Bref._me(Bref.f, psi[0][None, :] * np.ones((1, 1)))[:, 0]
cl = Bref._me(Bref.f, psi[1][None, :] * np.ones((1, 1)))[:, 0]
Kref = Bref._me(Bref.f, 2.0 * C * Bref.h)
H0 = np.block([[C**2 * np.eye(320), C * Kref],
               [C * Kref.T, -C**2 * np.eye(320)]])
evH, UH = np.linalg.eigh(H0)
absH = UH @ np.diag(np.abs(evH)) @ UH.T
coef = np.concatenate([cu, cl])
for N in (20, 40, 80, 160):
    res = coef.copy()
    res[:320][:N] = 0.0                     # remove the first N upper coefs
    res[320:][:N] = 0.0                     # and the first N lower coefs
    q = float(res @ (absH @ res))           # <res, |H0| res>
    B = RadialDiracBasis(N, kappa, Z, 0.8 * Z, mu=1.0,
                         nquad=max(6000, 24 * N), cert_tol=1e-4)
    dE = abs(float(B.solve_naive(shifted=True)[0]) - Egs)
    print(f"   N={N:>4}: |dE| = {dE:.3e}   <res,|H0|res> = {q:.3e}"
          f"   ratio = {dE / q:.3f}")
print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
