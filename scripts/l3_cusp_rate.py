"""Lemma L3 (cusp): exact representation and the rate dichotomy.
math_daniel protocol; symbols: ../../math-context.md (v1.2).

Claims verified here (pre-registered):

(L3a) EXACT REPRESENTATION. For kappa < 0, n_r = 0, the Dirac-Coulomb
      ground state has BOTH components proportional to r^gamma e^{-Z r}
      (same radial profile), E = gamma c^2 / |kappa|, lam = Z/|kappa|.
      Hence with mu = gamma and beta = Z/|kappa| the state lies in the
      nb = 1 trial space: the solver must return the exact binding with
      TWO degrees of freedom, at the shifted-pencil floor.

(L3b) RATE DICHOTOMY (universal exponent). For the cusp profile
      u(x) = x^gamma e^{-x/2} expanded in the orthonormal family
      q_j^(mu), the coefficients are EXACTLY
        c_j = N_j Gamma(mu+gamma+1) Gamma(j+mu-gamma) /
              (j! Gamma(mu-gamma)),   N_j = sqrt(j!/Gamma(j+2mu+1)),
      so |c_j| ~ [Gamma(mu+gamma+1)/|Gamma(mu-gamma)|] j^{-(1+gamma)}:
      the DECAY EXPONENT -(1+gamma) is INDEPENDENT of mu; the prefactor
      mismatch only changes the constant, which vanishes identically
      iff mu - gamma in {0,-1,-2,...} (exactness at mu = gamma).
      L2 tail after N terms ~ N^{-(1/2+gamma)}.

(V3)  Consequence for eigenvalues (measured; rate law CONJECTURED, not
      proven): integer-prefactor basis (mu = 1) at high Z converges
      algebraically, with fitted exponent to compare against 2*gamma-1.
"""

import sys
import time
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

t0 = time.perf_counter()

# ---------------- V1: L3a symbolic + numeric ----------------------------
import sympy as sp

r, cS, ZS = sp.symbols('r c Z', positive=True)
kap = sp.Symbol('kappa', integer=True)
a, b = sp.symbols('a b')
for kv in (-1, -2):
    gam = sp.sqrt(kap**2 - (ZS / cS)**2).subs(kap, kv)
    lamv = ZS / abs(kv)
    prof = r**gam * sp.exp(-lamv * r)
    f = a * prof
    g = b * prof
    Op = lambda u, s: s * (-sp.diff(u, r)) + kv / r * u     # O± = ∓d/dr+κ/r
    E = gam * cS**2 / abs(kv)
    eq1 = sp.simplify(((-ZS / r + cS**2) * f + cS * Op(g, -1) - E * f) / prof)
    eq2 = sp.simplify((cS * Op(f, +1) + (-ZS / r - cS**2) * g - E * g) / prof)
    sol = sp.solve([sp.Eq(eq1, 0), sp.Eq(eq2, 0)], [b], dict=True)
    # eq1, eq2 are linear in (a,b): check consistency -> one ratio b/a
    A1 = sp.Poly(eq1.expand(), a, b).coeffs()
    print(f"V1 kappa={kv}: eq1 = {sp.simplify(eq1)}")
    print(f"           eq2 = {sp.simplify(eq2)}")
    rat1 = sp.simplify(-sp.diff(eq1, a) / sp.diff(eq1, b))   # b/a from eq1
    rat2 = sp.simplify(-sp.diff(eq2, a) / sp.diff(eq2, b))   # b/a from eq2
    print(f"           b/a from eq1 = {sp.simplify(1/rat1)}, "
          f"from eq2 = {sp.simplify(1/rat2)}, "
          f"consistent: {sp.simplify(1/rat1 - 1/rat2) == 0}")

from decimal import Decimal, getcontext

from dirac import C_AU, RadialDiracBasis  # noqa: E402

getcontext().prec = 40
C = C_AU


def exact_dec(nr, kappa, Z):
    cD, ZD = Decimal(repr(C)), Decimal(repr(float(Z)))
    nu = ZD / cD
    g = (Decimal(kappa * kappa) - nu * nu).sqrt()
    d = nu / (Decimal(nr) + g)
    return cD * cD / (Decimal(1) + d * d).sqrt() - cD * cD


print("\nV1 numeric: nb=1 (TWO degrees of freedom), mu=gamma, beta=Z/|kappa|:")
for Z in (40.0, 92.0, 130.0):
    for kappa in (-1, -2):
        nu = Z / C
        gam = float(np.sqrt(kappa * kappa - nu**2))
        B = RadialDiracBasis(1, kappa, Z, Z / abs(kappa), mu=gam,
                             quad="cusp", nquad=40, cert_tol=1e-6)
        ev = B.solve_naive(shifted=True)
        ex = exact_dec(0, kappa, Z)
        rel = float((Decimal(repr(float(ev[0]))) - ex) / ex)
        print(f"   Z={Z:>5.0f} kappa={kappa:>2}: E = {float(ev[0]):.10f}"
              f"   rel dev from exact = {rel:+.1e}")

# ---------------- V2: L3b coefficient law -------------------------------
from scipy.special import gammaln

from dirac import laguerre_funcs  # noqa: E402


def coeffs(mu, gam, nb=160, nq=6000, X=500.0):
    tq, wq = leggauss(nq)
    x = 0.5 * X * (tq + 1.0)
    w = 0.5 * X * wq
    q, _, _ = laguerre_funcs(nb, mu, x)
    u = x**gam * np.exp(-0.5 * x)
    return q @ (w * u)


def formula(j, mu, gam):
    # N_j * Gamma(mu+gam+1) * Gamma(j+mu-gam) / (j! * Gamma(mu-gam))
    lognj = 0.5 * (gammaln(j + 1) - gammaln(j + 2 * mu + 1))
    lg = (gammaln(mu + gam + 1) + gammaln(j + mu - gam)
          - gammaln(j + 1) - gammaln(mu - gam))
    return np.exp(lognj + lg)


print("\nV2 coefficient law c_j for u = x^gamma e^{-x/2}:")
gam0 = 0.7411                                    # gamma of Z=92, kappa=1
for mu in (1.0, 0.9, 2.0):
    c = coeffs(mu, gam0)
    j = np.arange(len(c))
    pred = formula(j.astype(float), mu, gam0)
    ok = np.max(np.abs(c[:120] - pred[:120]) / np.abs(pred[:120]))
    lo, hi = 30, 120
    slope = np.polyfit(np.log(j[lo:hi]), np.log(np.abs(c[lo:hi])), 1)[0]
    print(f"   mu={mu:4.2f}: max rel dev formula (j<120) = {ok:.1e};"
          f" fitted exponent = {slope:+.4f}  (predicted {-(1+gam0):+.4f})")
c_match = coeffs(gam0, gam0)
print(f"   mu=gamma: max |c_j|, j>=1 = {np.max(np.abs(c_match[1:])):.1e}"
      f"  (exactness: identically 0 up to quadrature)")
# constant ratio between two mismatched mu at fixed j-window
c1, c2 = coeffs(1.0, gam0), coeffs(2.0, gam0)
jw = np.arange(60, 100)
meas = np.mean(np.abs(c2[jw] / c1[jw]))
pred_ratio = np.exp((gammaln(2.0 + gam0 + 1) - gammaln(1.0 + gam0 + 1))
                    - (gammaln(2.0 - gam0) - gammaln(1.0 - gam0)))
# note: N_j and Gamma(j+mu-gam)/j! carry mu dependence too -> use full formula
full_ratio = np.mean(formula(jw.astype(float), 2.0, gam0)
                     / formula(jw.astype(float), 1.0, gam0))
print(f"   constant ratio mu=2 / mu=1 (j=60..100): measured {meas:.4f},"
      f" full-formula {full_ratio:.4f}")

# ---------------- V3: eigenvalue-rate consequence (measured) -----------
print("\nV3 integer-prefactor basis (mu=1), Z=80, kappa=-1, Legendre quad:")
Z = 80.0
nu = Z / C
gam = float(np.sqrt(1 - nu**2))
errs, Ns = [], []
ex = exact_dec(0, -1, Z)
for N in (20, 40, 80, 160):
    B = RadialDiracBasis(N, -1, Z, 0.8 * Z, cert_tol=1e-5)
    ev = B.solve_naive(shifted=True)
    rel = abs(float((Decimal(repr(float(ev[0]))) - ex) / ex))
    Ns.append(N)
    errs.append(rel)
    print(f"   N={N:>4}: rel err = {rel:.3e}")
slope = np.polyfit(np.log(Ns), np.log(errs), 1)[0]
print(f"   fitted eigenvalue-error exponent = {slope:+.3f}"
      f"   (2*gamma-1 = {2*gam-1:.3f}; gamma = {gam:.4f})"
      f"   [rate law CONJECTURED, exponent measured]")
print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
