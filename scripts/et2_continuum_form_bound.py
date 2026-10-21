"""E-T2: does the CONTINUUM-relative form bound converge (unlike the
discrete-relative one, which diverges -- FINDINGS #13)?

alpha_tilde(nb; nb_ref) := || M^{-1/2} W M^{-1/2} ||,
   M = P |H0_ref| P   (compression of the LARGE-reference |H0|,
                       proxy for the continuum |D0|, onto the first nb
                       nested basis pairs),
   W = diag(Vd, Vd) on the same nb pairs, Coulomb V = -Z/r (exact
       integrals, gamma-basis + cusp rule).

Pre-registered predictions:
Q1  alpha_tilde CONVERGES as nb_ref grows at fixed nb (the continuum
    Kato/Hardy bound is finite), in contrast with the divergent
    discrete-relative alpha_N of FINDINGS #13.
Q2  alpha_tilde is linear in nu = Z/c: alpha_tilde ~ nu * C_kappa.
    Competing theory values for the channel constant C_1 (|kappa|=1):
      (A) sharp/Talman:  C = 1/0.9058 = 1.104  -> alpha=1 at nu=0.906
      (B) generic Kato:  C = pi/2     = 1.571  -> alpha=1 at nu=0.637
    The measured slope adjudicates.
Q3  alpha_tilde is only weakly increasing in nb at fixed nb_ref (edge
    effects), consistent with a finite continuum limit.
"""

import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from dirac import C_AU, RadialDiracBasis  # noqa: E402

C = C_AU
t0 = time.perf_counter()


def alpha_tilde(Z, nb, nb_ref, beta_fac=0.8):
    nu = Z / C
    gam = float(np.sqrt(1 - nu**2))                  # kappa = -1
    # Instrument envelope (measured): scipy weights NaN out at nq >~ 350
    # AND underflow genuine tail weight beyond x ~ 709, which caps the
    # cusp rule at nb <~ 170 (the C1 certification catches violations).
    B = RadialDiracBasis(nb_ref, -1, Z, beta_fac * Z, mu=gam, quad="cusp",
                         nquad=min(nb_ref + 80, 300), cert_tol=1e-5)
    K = B._me(B.f, 2.0 * C * B.h)
    H0 = np.block([[C**2 * np.eye(nb_ref), C * K],
                   [C * K.T, -C**2 * np.eye(nb_ref)]])
    evH, UH = np.linalg.eigh(H0)
    absH = UH @ np.diag(np.abs(evH)) @ UH.T
    sel = np.concatenate([np.arange(nb), nb_ref + np.arange(nb)])
    M = absH[np.ix_(sel, sel)]
    Vd = B._mev(B.f, B.V, B.f)[:nb, :nb]
    Vd = 0.5 * (Vd + Vd.T)
    W = np.block([[Vd, np.zeros((nb, nb))], [np.zeros((nb, nb)), Vd]])
    em, Um = np.linalg.eigh(M)
    Mi = Um @ np.diag(1.0 / np.sqrt(em)) @ Um.T
    return float(np.linalg.norm(Mi @ W @ Mi, 2))


print("Q1 convergence in nb_ref (Z=92, nb=40):")
for nb_ref in (80, 100, 120, 140, 160):
    a = alpha_tilde(92.0, 40, nb_ref)
    print(f"   nb_ref={nb_ref:>4}: alpha_tilde = {a:.4f}")

print("\nQ3 dependence on nb (Z=92, nb_ref=160):")
for nb in (20, 40, 60, 80):
    a = alpha_tilde(92.0, nb, 160)
    print(f"   nb={nb:>4}: alpha_tilde = {a:.4f}")

print("\nQ2 slope in nu (nb=40, nb_ref=160):")
rows = []
for Z in (20.0, 40.0, 60.0, 80.0, 92.0, 110.0, 124.0, 130.0):
    nu = Z / C
    a = alpha_tilde(Z, 40, 160)
    rows.append((nu, a))
    print(f"   Z={Z:>5.0f} nu={nu:.4f}: alpha_tilde = {a:.4f}"
          f"   alpha/nu = {a / nu:.4f}")
nus = np.array([r[0] for r in rows])
als = np.array([r[1] for r in rows])
slope = np.polyfit(nus, als, 1)[0]
nu_crit = np.interp(1.0, als, nus)
print(f"\n   fitted slope d(alpha)/d(nu) = {slope:.4f}")
print(f"   candidates: 1/0.9058 = {1/0.9058:.4f} (Talman sharp)"
      f" | pi/2 = {np.pi/2:.4f} (generic Kato)")
print(f"   alpha_tilde = 1 reached at nu ~ {nu_crit:.4f}"
      f"   (Talman: 0.9058, Kato: 0.6366)")
print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
