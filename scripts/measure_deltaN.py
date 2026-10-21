"""L1 empirical test: conformity defect delta_N of four trial spaces with
respect to the FREE-Dirac spectral splitting Lambda+/Lambda-.

delta_N := || (I - Pi_N) Lambda+ Pi_N ||_2,

where Pi_N is the orthogonal projector onto the 2N-dimensional trial space
V_N and Lambda+ is the positive-energy spectral projector of the free
radial Dirac operator (channel kappa), built in a large reference space
(same orthonormal Laguerre family, nb_ref >> N, so the trial functions are
EXACTLY nested and coefficients are exact up to the reference truncation,
which we monitor via completeness residuals and nb_ref drift).

delta_N = 0  <=>  Lambda+ maps V_N into itself, i.e. V_N splits as
(V_N ∩ Lambda+H) ⊕ (V_N ∩ Lambda-H): the Lewin-Sere no-pollution condition.

PRE-REGISTERED PREDICTIONS (before running):
D1  DKB s=-1 (Shabaev): delta_N smallest, ~O((p/c)^2) -- dual kinetic
    balance aligns the span with Lambda+/- to leading order.
D2  naive and RKB: intermediate, ~O(p/c) (kinetic balance helps the
    electronic sector only / not the splitting itself).
D3  DKB s=+1 (anti-balanced): largest, O(1)-ish and NOT decaying -- this
    span was observed to pollute already at Z=1 from nb~60.
D4  Ordering of delta_N reproduces the observed pollution ordering:
    s=-1 clean << naive/RKB << s=+1 polluting.
"""

import sys
import time
from pathlib import Path

import numpy as np
from scipy.linalg import eigh, qr

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from dirac import RadialDiracBasis  # noqa: E402

t0 = time.perf_counter()
KAPPA, BETA = -1, 0.9


def free_projector(nb_ref):
    """Reference basis + Lambda+ in reference coordinates (2*nb_ref dim)."""
    B = RadialDiracBasis(nb_ref, KAPPA, 0.0, BETA, cert_tol=1e-6)
    c = B.c
    f, df = B.f, B.df
    r, W = B.r, B.W
    Opf = -df + KAPPA / r * f
    ME = B._me
    # free Dirac in the (upper=f_i, lower=f_i) product basis, Z=0
    Sff = ME(f, f)
    H0 = np.block([[c * c * Sff, c * ME(f, Opf)],
                   [c * ME(f, Opf).T, -c * c * Sff]])
    H0 = 0.5 * (H0 + H0.T)
    E, U = eigh(H0)                      # ref basis is orthonormal: S=I
    Lam = U @ np.diag((E > 0).astype(float)) @ U.T
    return B, Lam


def trial_coeffs(B, nb, kind):
    """Coefficients (2*nb_ref x 2*nb) of the trial family in ref coords."""
    nref = B.nb
    c = B.c
    f, g, h = B.f, B.g, B.h
    ME = B._me
    # component-wise expansion in the orthonormal f-family (exact nesting
    # for the f parts; quadrature Gram for the g/h parts)
    def coef(u):                          # u: (>=nb x ngrid) -> (nref x nb)
        return ME(f, u[:nb])              # [i,j] = <f_i, u_j>

    Zc = np.zeros((nref, nb))
    Inb = np.eye(nref, nb)                # f_j = j-th ref function
    if kind == "naive":
        up = np.hstack([Inb, Zc]); lo = np.hstack([Zc, Inb])
    elif kind == "rkb":
        chi = coef(2 * c * g)             # O- f_j
        up = np.hstack([Inb, Zc]); lo = np.hstack([Zc, chi])
    elif kind == "dkb-":
        gg, hh = coef(g), coef(h)
        up = np.hstack([Inb, -hh]); lo = np.hstack([gg, Inb])
    elif kind == "dkb+":
        gg, hh = coef(g), coef(h)
        up = np.hstack([Inb, +hh]); lo = np.hstack([gg, Inb])
    C = np.vstack([up, lo])
    # completeness residual of the projected (non-nested) columns
    def gridnorm2(u):
        return np.einsum('jk,jk,k->j', u[:nb], u[:nb], B.W)
    targets = {"naive": [], "rkb": [2 * c * g], "dkb-": [g, h],
               "dkb+": [g, h]}[kind]
    res = 0.0
    for tgt in targets:
        full = gridnorm2(tgt)
        proj = np.sum(coef(tgt) ** 2, axis=0)
        res = max(res, float(np.sqrt(np.maximum(full - proj, 0).max()
                                     / full.max())))
    return C, res


def delta_N(Lam, C):
    Q, _ = qr(C, mode='economic')
    LQ = Lam @ Q
    return np.linalg.norm(LQ - Q @ (Q.T @ LQ), 2)


print(f"kappa={KAPPA}, beta={BETA}, free-Dirac splitting  (Z plays no role)")
for nb_ref in (160, 240):
    B, Lam = free_projector(nb_ref)
    print(f"\n-- reference nb_ref={nb_ref} (certs {tuple(f'{x:.0e}' for x in B.certs)}) --")
    print(f"{'nb':>5} {'naive':>10} {'rkb':>10} {'dkb s=-1':>10} {'dkb s=+1':>10} {'max res':>9}")
    for nb in (10, 20, 40, 80):
        row, worst = [], 0.0
        for kind in ("naive", "rkb", "dkb-", "dkb+"):
            C, res = trial_coeffs(B, nb, kind)
            row.append(delta_N(Lam, C))
            worst = max(worst, res)
        print(f"{nb:>5} " + " ".join(f"{d:10.2e}" for d in row) + f" {worst:9.1e}")

print(f"\ntotal: {time.perf_counter()-t0:.1f} s")
