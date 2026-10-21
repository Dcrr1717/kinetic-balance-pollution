"""E-T3: empirical onset map of the DKB s=+1 (anti-balanced) mid-gap
impostor at point Coulomb -- the datum T1-Coulomb must predict.

Detector (refined): a gap eigenvalue at relative distance > 1e-3 from
EVERY exact ladder level among the first 12 AND deeper than the 6th
exact level (so truncation-limited high Rydberg states are not
miscounted).  This catches both the edge-hugging and mid-ladder
impostors; the coarser 1.5x-ground rule of the first pass missed the
latter.  Integer-prefactor basis (mu = ell+1), beta = 0.9 max(Z,1),
kappa = -1, Legendre quadrature -- the setting of the original
observation (FINDINGS #2: Z=1 pollutes from nb ~ 60; that record was
based on coarser inspection and is superseded by this scan).

Also serves as a REGRESSION TEST of the solve_dkb(s) refactor:
s = -1 must remain clean (machine precision) at every scanned point.

Recorded per Z: nb_crit (first nb with an impostor), the impostor
binding, and the dimensionless fiber ceiling t_max = sigma_max/(2c) at
onset, to expose the empirical scaling invariant.
"""

import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from dirac import C_AU, RadialDiracBasis, exact_ladder  # noqa: E402

C = C_AU
t0 = time.perf_counter()

def spurious(ev, ladder):
    """Gap states far from every exact level and deeper than level 6."""
    out = []
    for e in ev:
        if e > ladder[5]:
            continue
        rel = np.min(np.abs((e - ladder) / ladder))
        if rel > 1e-3:
            out.append(float(e))
    return out


print(f"{'Z':>5} {'nb_crit':>8} {'impostor E_b':>14} {'ground':>12}"
      f" {'t_max@crit':>10} {'nu*t_max':>9} {'s=-1@60':>9}")
for Z in (1.0, 10.0, 20.0, 40.0, 60.0, 80.0):
    nu = Z / C
    beta = 0.9 * max(Z, 1.0)
    ladder = exact_ladder(-1, Z)
    nb_crit, imp, tmax_c, reg60 = None, np.nan, np.nan, np.nan
    for nb in range(20, 131, 10):
        B = RadialDiracBasis(nb, -1, Z, beta, cert_tol=1e-5)
        evp = B.solve_dkb(s=+1)
        if nb == 60:                       # regression point, s = -1
            evm = B.solve_dkb(s=-1)
            k = min(3, evm.size)
            reg60 = float(np.max(np.abs(
                (evm[:k] - ladder[:k]) / ladder[:k])))
        sp = spurious(evp, ladder)
        if sp and nb_crit is None:
            nb_crit = nb
            imp = sp[0]
            K = B._me(B.f, 2.0 * C * B.h)
            tmax_c = float(np.linalg.svd(K, compute_uv=False)[0] / (2 * C))
    if nb_crit is None:
        print(f"{Z:>5.0f} {'>130':>8} {'-':>14} {ladder[0]:>12.3f}"
              f" {'-':>10} {'-':>9} {reg60:>9.1e}")
    else:
        print(f"{Z:>5.0f} {nb_crit:>8} {imp:>14.1f} {ladder[0]:>12.3f}"
              f" {tmax_c:>10.4f} {nu * tmax_c:>9.5f} {reg60:>9.1e}")

print("\nZ=1 impostor trajectory vs nb (s=+1, spurious list head):")
ladder = exact_ladder(-1, 1.0)
for nb in (20, 40, 60, 80):
    B = RadialDiracBasis(nb, -1, 1.0, 0.9, cert_tol=1e-5)
    sp = spurious(B.solve_dkb(s=+1), ladder)
    print(f"   nb={nb:>4}: {['%.1f' % s for s in sp[:4]]}")
print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
