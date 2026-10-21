#!/usr/bin/env python3
"""Self-contained numerical check of the algebraic core of

    "Exact fiber analysis of kinetic-balance spectral pollution for the
     radial Dirac operator"  (Paper T).

WHAT THIS SCRIPT VERIFIES
-------------------------
  Prop. 2.1  fiber decomposition of H0 and E(sigma) = sqrt(c^4 + c^2 sigma^2)
  Thm. 3.1   the four exact per-mode leakage laws, Eqs. (lspl)/(lbal)/(lanti),
             including the key identity t - rho = 4t^3/(1+w)^2, Eq. (key)
  Thm. 4.1   the exact global conformity defect  delta = max_j l_j sqrt(1-l_j^2)
  Cor. 4.2   exact conformity (zero defect) of the dual-kinetic-balance pair space
  Thm. 5.1(a) the fiber Rayleigh values, Eq. (rayleigh):
             R_bal - c^2 = 2c^2 t^2/(1+t^2) >= 0,
             c^2 - R_anti = c^2 (2-4t^2)/(1+t^2),  R_anti + c^2 = 6c^2 t^2/(1+t^2),
             R_anti strictly inside (-c^2, c^2) for 0 < t < 1/sqrt(2),
             R_anti = 0 exactly at t = 1/sqrt(5).

DEPENDENCIES
------------
NumPy only.  The script is deliberately independent of the certified Laguerre
discretization of the companion paper: it builds its own random free operators.
Independence is machine-enforced by the import guard below -- any attempt to
pull in the companion solver (`dirac`, `src.dirac`) raises ImportError.

Consequently this file reproduces the *algebraic* statements of the paper
(Sections 2-5) and nothing else.  The Coulomb-frontier numbers of Sections 7-8
are NOT reproducible here; they require the companion discretization.

Run:      python selfcheck_fiber.py
Exit code: 0 = all checks passed, 1 = at least one tolerance exceeded.
Seed:     np.random.default_rng(20260711)  (same seed as the development script)
"""

from __future__ import annotations

# --- hard independence guard: no companion-solver import may succeed --------
import builtins as _builtins
import sys as _sys

_FORBIDDEN = {"dirac", "src"}
_real_import = _builtins.__import__


def _guarded_import(name, *args, **kwargs):
    if name.split(".")[0] in _FORBIDDEN:
        raise ImportError(
            f"selfcheck_fiber.py is self-contained and must not import {name!r}"
        )
    return _real_import(name, *args, **kwargs)


_builtins.__import__ = _guarded_import
# ---------------------------------------------------------------------------

import numpy as np

RNG = np.random.default_rng(20260711)
TOL = 1e-12          # generous vs. the ~1e-16 actually observed
report: list[tuple[str, float]] = []
failures: list[str] = []


def record(label: str, dev: float, tol: float = TOL) -> None:
    report.append((label, dev))
    status = "ok  " if dev <= tol else "FAIL"
    if dev > tol:
        failures.append(f"{label}: {dev:.3e} > {tol:.1e}")
    print(f"  [{status}] {label:<58s} max dev = {dev:.3e}")


# ===========================================================================
# closed forms of the paper
# ===========================================================================
def rho_of(t):
    """rho = 2t/(1+w), w = sqrt(1+4t^2)  (Thm. 3.1)."""
    return 2.0 * t / (1.0 + np.sqrt(1.0 + 4.0 * t**2))


def leak_closed(t):
    """Eqs. (lspl), (lbal), (lanti) exactly as printed in Theorem 3.1.

    Returns (l_spl, l_bal, l_pos, l_anti).  l_bal is evaluated in the
    4t^3/(1+w)^2 form of Eq. (lbal), i.e. the form that already uses the
    key identity (key); l_pos = l_bal by the theorem.
    """
    w = np.sqrt(1.0 + 4.0 * t**2)
    rho = 2.0 * t / (1.0 + w)
    a = np.sqrt(1.0 + rho**2)
    b = np.sqrt(1.0 + t**2)
    l_spl = rho / a
    l_bal = 4.0 * t**3 / ((1.0 + w) ** 2 * a * b)
    l_anti = (t + rho) / (a * b)
    return l_spl, l_bal, l_bal, l_anti


def leak_closed_trho(t):
    """Same leakages written with the un-simplified numerator (t - rho).

    Comparing against leak_closed() is a numerical test of Eq. (key),
    t - rho = 4t^3/(1+w)^2.
    """
    w = np.sqrt(1.0 + 4.0 * t**2)
    rho = 2.0 * t / (1.0 + w)
    a = np.sqrt(1.0 + rho**2)
    b = np.sqrt(1.0 + t**2)
    return rho / a, (t - rho) / (a * b), (t - rho) / (a * b), (t + rho) / (a * b)


def rayleigh_closed(c, t):
    """Eq. (rayleigh): (R_bal, R_spl, R_pos, R_anti)."""
    return (
        c**2 * (1.0 + 3.0 * t**2) / (1.0 + t**2),
        c**2 * np.ones_like(t) if np.ndim(t) else c**2,
        -c**2 * (1.0 + 3.0 * t**2) / (1.0 + t**2),
        c**2 * (5.0 * t**2 - 1.0) / (1.0 + t**2),
    )


# fiber trial directions, Eq. (families): bal, spl, pos, anti
def trial_dirs(t):
    return [
        np.array([1.0, t]),      # u_bal  (electronic)
        np.array([1.0, 0.0]),    # u_spl  (electronic)
        np.array([-t, 1.0]),     # u_pos  (positronic)
        np.array([t, 1.0]),      # u_anti (positronic)
    ]


FAMILIES = ("bal", "spl", "pos", "anti")
# wrong sector per family: electronic families leak into the negative sector,
# positronic families into the positive sector.
WRONG_SECTOR = {"bal": "-", "spl": "-", "pos": "+", "anti": "+"}


# ===========================================================================
# numerical machinery: projectors from an actual eigendecomposition
# ===========================================================================
def spectral_projectors(H):
    """(Lambda_minus, Lambda_plus) of a real symmetric H, by eigh."""
    ev, W = np.linalg.eigh(H)
    Wm = W[:, ev < 0]
    Wp = W[:, ev > 0]
    return Wm @ Wm.T, Wp @ Wp.T


def leak_num(P, u):
    """||P u|| / ||u||: the norm of the wrong-sector component."""
    u = np.asarray(u, float)
    return float(np.linalg.norm(P @ u) / np.linalg.norm(u))


def fiber_matrix(c, t):
    """h(sigma) of Eq. (fiberm) with sigma = 2ct."""
    p = 2.0 * c * t
    return np.array([[c**2, c * p], [c * p, -(c**2)]])


# ===========================================================================
# (a)+(b)+(c)  random free 2x2 fibers: measured leakages vs Theorem 3.1
# ===========================================================================
print("\n== (1) Theorem 3.1: exact per-mode leakage, random free 2x2 fibers ==")

dev_direct = 0.0
dev_key = 0.0
dev_balpos = 0.0
dev_pyth = 0.0
n2x2 = 0
for c_val in (1.0, 137.035999084, 1000.0):
    for _ in range(40):
        t_val = 10.0 ** RNG.uniform(-4.0, np.log10(0.45))
        h = fiber_matrix(c_val, t_val)
        Lm, Lp = spectral_projectors(h)
        got = []
        for name, u in zip(FAMILIES, trial_dirs(t_val)):
            P = Lm if WRONG_SECTOR[name] == "-" else Lp
            got.append(leak_num(P, u))
        got = np.array(got)
        # paper order in leak_closed() is (spl, bal, pos, anti); reorder
        w_spl, w_bal, w_pos, w_anti = leak_closed(t_val)
        want = np.array([w_bal, w_spl, w_pos, w_anti])
        dev_direct = max(dev_direct, float(np.max(np.abs(got - want))))
        # Eq. (key): the (t-rho) form must agree with the 4t^3/(1+w)^2 form
        k_spl, k_bal, k_pos, k_anti = leak_closed_trho(t_val)
        dev_key = max(
            dev_key,
            float(np.max(np.abs(np.array([k_spl, k_bal, k_pos, k_anti])
                                - np.array([w_spl, w_bal, w_pos, w_anti])))),
        )
        # l_bal == l_pos, as the theorem asserts
        dev_balpos = max(dev_balpos, abs(got[0] - got[2]))
        # <v+,b>^2 + <v-,b>^2 = 1 in every fiber (used in the Thm 4.1 proof)
        for u in trial_dirs(t_val):
            dev_pyth = max(
                dev_pyth,
                abs(leak_num(Lm, u) ** 2 + leak_num(Lp, u) ** 2 - 1.0),
            )
        n2x2 += 1

record(f"eigh leakages vs Eqs.(lspl,lbal,lanti)  [{n2x2} fibers, 3 c-scales]",
       dev_direct)
record("Eq.(key)  t-rho = 4t^3/(1+w)^2  via the two leakage forms", dev_key)
record("Thm 3.1  l_bal = l_pos (measured)", dev_balpos)
record("fiber Pythagoras  l_+^2 + l_-^2 = 1", dev_pyth)

# boundary / pathological t, including t > 1/sqrt(2)
dev_bd = 0.0
for t_val in (1e-8, 1e-6, 0.25, 1 / np.sqrt(5), 0.5, 1 / np.sqrt(2), 1.0, 5.0):
    h = fiber_matrix(1.0, t_val)
    Lm, Lp = spectral_projectors(h)
    got = np.array([leak_num(Lm if WRONG_SECTOR[n] == "-" else Lp, u)
                    for n, u in zip(FAMILIES, trial_dirs(t_val))])
    w_spl, w_bal, w_pos, w_anti = leak_closed(t_val)
    dev_bd = max(dev_bd,
                 float(np.max(np.abs(got - np.array([w_bal, w_spl, w_pos, w_anti])))))
record("boundary t in {1e-8,1e-6,.25,1/sqrt5,.5,1/sqrt2,1,5}", dev_bd)


# ===========================================================================
# (a)+(b)+(c)  random n=5 Gaussian K: the full 2N x 2N problem
# ===========================================================================
print("\n== (2) Prop. 2.1 + Thm 3.1: random n=5 Gaussian K, full 10x10 H0 ==")

N = 5


def build_H0(K, c):
    n = K.shape[0]
    return np.block([[c**2 * np.eye(n), c * K],
                     [c * K.T, -(c**2) * np.eye(n)]])


def fiber_data(K, c):
    """Per-fiber orthonormal frames (e1,e2) and parameters t_j (Prop. 2.1)."""
    U, S, Vt = np.linalg.svd(K)
    n = K.shape[0]
    out = []
    for j in range(n):
        e1 = np.concatenate([U[:, j], np.zeros(n)])
        e2 = np.concatenate([np.zeros(n), Vt[j]])
        out.append((S[j] / (2.0 * c), e1, e2))
    return out


dev_full = 0.0
dev_inv = 0.0
dev_E = 0.0
n_fib = 0
K_examples = []
for _ in range(30):
    c_val = 10.0 ** RNG.uniform(0.0, 2.5)
    K = RNG.normal(size=(N, N)) * c_val * RNG.uniform(0.01, 0.5)
    K_examples.append((c_val, K))
    H0 = build_H0(K, c_val)
    Lm, Lp = spectral_projectors(H0)
    for t_j, e1, e2 in fiber_data(K, c_val):
        # Prop 2.1: W_j is H0-invariant and H0|W_j = h(sigma_j).
        # Both residuals are measured relative to ||H0||, since the matrix
        # entries scale like c^2 and c ranges over 1..316 here.
        Wj = np.column_stack([e1, e2])
        blk = Wj.T @ H0 @ Wj
        nH = float(np.linalg.norm(H0))
        dev_inv = max(dev_inv,
                      float(np.max(np.abs(blk - fiber_matrix(c_val, t_j)))) / nH)
        dev_inv = max(dev_inv,
                      float(np.linalg.norm(H0 @ Wj - Wj @ blk)) / nH)
        # Prop 2.1: E(sigma) = sqrt(c^4 + c^2 sigma^2) = c^2 sqrt(1+4t^2)
        sig = 2.0 * c_val * t_j
        dev_E = max(dev_E, abs(np.sqrt(c_val**4 + c_val**2 * sig**2)
                               - c_val**2 * np.sqrt(1.0 + 4.0 * t_j**2))
                    / c_val**2)
        # Thm 3.1 in the full 2N-dimensional problem
        dirs = [e1 + t_j * e2, e1, -t_j * e1 + e2, t_j * e1 + e2]
        got = np.array([leak_num(Lm if WRONG_SECTOR[n] == "-" else Lp, u)
                        for n, u in zip(FAMILIES, dirs)])
        w_spl, w_bal, w_pos, w_anti = leak_closed(t_j)
        dev_full = max(dev_full,
                       float(np.max(np.abs(got - np.array([w_bal, w_spl, w_pos, w_anti])))))
        n_fib += 1

record(f"Prop 2.1  H0-invariance of W_j, block = h(sigma_j) [{n_fib} fib, rel]",
       dev_inv)
record("Prop 2.1  E(sigma) = c^2 sqrt(1+4t^2)   (relative)", dev_E)
record("Thm 3.1  full 10x10 eigh leakages vs closed forms", dev_full)


# ===========================================================================
# (d)  Theorem 4.1 exact global defect, and Corollary 4.2 exact zero
# ===========================================================================
print("\n== (3) Thm 4.1 global defect and Cor. 4.2 exact conformity ==")


def single_family_projector(K, c, family):
    """Pi = Q Q^T for the untruncated single-family trial space."""
    cols = []
    for t_j, e1, e2 in fiber_data(K, c):
        d = {"bal": e1 + t_j * e2,
             "spl": e1,
             "pos": -t_j * e1 + e2,
             "anti": t_j * e1 + e2}[family]
        cols.append(d / np.linalg.norm(d))
    Q = np.column_stack(cols)
    return Q @ Q.T, Q


dev_defect = {f: 0.0 for f in FAMILIES}
dev_defect_minus = {f: 0.0 for f in FAMILIES}
dev_dkb = 0.0
for c_val, K in K_examples:
    H0 = build_H0(K, c_val)
    Lm, Lp = spectral_projectors(H0)
    I = np.eye(2 * N)
    ts = [t_j for t_j, _, _ in fiber_data(K, c_val)]
    for family in FAMILIES:
        Pi, _ = single_family_projector(K, c_val, family)
        delta_p = np.linalg.norm((I - Pi) @ Lp @ Pi, 2)
        delta_m = np.linalg.norm((I - Pi) @ Lm @ Pi, 2)
        idx = FAMILIES.index(family)
        ell = np.array([leak_closed(t_j)[[1, 0, 2, 3][idx]] for t_j in ts])
        predicted = float(np.max(ell * np.sqrt(np.maximum(0.0, 1.0 - ell**2))))
        dev_defect[family] = max(dev_defect[family], abs(delta_p - predicted))
        dev_defect_minus[family] = max(dev_defect_minus[family],
                                       abs(delta_m - predicted))
    # Cor 4.2: the DKB pair space spans every fiber -> exact zero defect
    cols = []
    for t_j, e1, e2 in fiber_data(K, c_val):
        for d in (e1 + t_j * e2, -t_j * e1 + e2):
            cols.append(d / np.linalg.norm(d))
    Qd = np.linalg.qr(np.column_stack(cols))[0]
    Pid = Qd @ Qd.T
    dev_dkb = max(dev_dkb,
                  float(np.linalg.norm((I - Pid) @ Lp @ Pid, 2)),
                  float(np.linalg.norm((I - Pid) @ Lm @ Pid, 2)))

for family in FAMILIES:
    record(f"Thm 4.1  ||(I-Pi)L+ Pi||_2 = max_j l_j sqrt(1-l_j^2)   [{family:>4s}]",
           dev_defect[family])
record("Thm 4.1  same value with Lambda_- (all four families)",
       max(dev_defect_minus.values()))
record("Cor 4.2  DKB pair space: ||(I-Pi)L_pm Pi||_2 = 0 exactly", dev_dkb, tol=1e-13)


# ===========================================================================
# (e)  Theorem 5.1(a): the fiber Rayleigh values and the anti-balanced sweep
# ===========================================================================
print("\n== (4) Thm 5.1(a): fiber Rayleigh values and the anti-balanced sweep ==")

c_sweep = 137.035999084
ts = np.linspace(1e-6, 1.0 / np.sqrt(2.0), 20001)

dev_R = 0.0
for c_val in (1.0, c_sweep):
    for t_val in (1e-6, 1e-3, 0.1, 1 / np.sqrt(5), 0.4, 1 / np.sqrt(2), 1.0, 3.0):
        h = fiber_matrix(c_val, t_val)
        meas = []
        for u in trial_dirs(t_val):          # bal, spl, pos, anti
            meas.append(float(u @ h @ u / (u @ u)))
        Rb, Rs, Rp, Ra = rayleigh_closed(c_val, t_val)
        dev_R = max(dev_R,
                    float(np.max(np.abs(np.array(meas) - np.array([Rb, Rs, Rp, Ra]))
                                 / c_val**2)))
record("Eq.(rayleigh)  measured u^T h u/u^T u vs closed forms (relative)", dev_R)

Rb, Rs, Rp, Ra = rayleigh_closed(c_sweep, ts)

# Thm 5.1(a) first half:  R_bal - c^2 = 2 c^2 t^2/(1+t^2) >= 0
lhs = Rb - c_sweep**2
rhs = 2.0 * c_sweep**2 * ts**2 / (1.0 + ts**2)
record("Thm 5.1(a)  R_bal - c^2 = 2c^2 t^2/(1+t^2)   (relative)",
       float(np.max(np.abs(lhs - rhs)) / c_sweep**2))
print(f"        min over the sweep of (R_bal - c^2)/c^2 = {np.min(lhs)/c_sweep**2:.6e}"
      f"   (>= 0 required)")
if np.min(lhs) < 0.0:
    failures.append("R_bal - c^2 < 0 somewhere on the sweep")

# the two identities used in the Thm 5.1(a) proof
record("Thm 5.1(a)  c^2 - R_anti = c^2(2-4t^2)/(1+t^2)   (relative)",
       float(np.max(np.abs((c_sweep**2 - Ra)
                           - c_sweep**2 * (2.0 - 4.0 * ts**2) / (1.0 + ts**2)))
             / c_sweep**2))
record("Thm 5.1(a)  R_anti + c^2 = 6c^2 t^2/(1+t^2)      (relative)",
       float(np.max(np.abs((Ra + c_sweep**2)
                           - 6.0 * c_sweep**2 * ts**2 / (1.0 + ts**2)))
             / c_sweep**2))

# R_anti strictly inside the gap on 0 < t < 1/sqrt(2)
interior = ts < 1.0 / np.sqrt(2.0)
strictly_in = bool(np.all(np.abs(Ra[interior]) < c_sweep**2))
print(f"        R_anti strictly inside (-c^2, c^2) on 0 < t < 1/sqrt(2): {strictly_in}")
print(f"        sweep range  R_anti/c^2 in [{Ra.min()/c_sweep**2:.6f},"
      f" {Ra.max()/c_sweep**2:.6f}]   (traverses the whole gap)")
if not strictly_in:
    failures.append("R_anti left the gap on 0 < t < 1/sqrt(2)")

# mid-gap crossing at t = 1/sqrt(5)
t_mid = 1.0 / np.sqrt(5.0)
R_mid = c_sweep**2 * (5.0 * t_mid**2 - 1.0) / (1.0 + t_mid**2)
record("Thm 5.1(a)  R_anti(1/sqrt5) = 0 (mid-gap)   (relative)",
       abs(R_mid) / c_sweep**2)

# monotone sweep: R_anti strictly increasing on the window
record("Thm 5.1(a) remark  R_anti strictly increasing on (0,1/sqrt2)",
       0.0 if bool(np.all(np.diff(Ra) > 0.0)) else 1.0, tol=0.5)

# endpoints of the sweep
R0 = c_sweep**2 * (5.0 * 0.0 - 1.0) / (1.0 + 0.0)
R_half = c_sweep**2 * (5.0 * 0.5 - 1.0) / (1.0 + 0.5)
record("Thm 5.1(a)  R_anti(0) = -c^2 and R_anti(1/sqrt2) = +c^2   (relative)",
       max(abs(R0 + c_sweep**2), abs(R_half - c_sweep**2)) / c_sweep**2)


# ===========================================================================
# summary
# ===========================================================================
print("\n" + "=" * 78)
overall = max(d for _, d in report)
print(f"SUMMARY: {len(report)} checks, worst deviation over all of them = {overall:.3e}")
print(f"tolerance = {TOL:.1e}")
print("dependencies actually loaded:  numpy " + np.__version__
      + f"  (python {_sys.version_info.major}.{_sys.version_info.minor}"
      + f".{_sys.version_info.micro})")
_leaked = sorted(m for m in _sys.modules if m.split(".")[0] in _FORBIDDEN)
print(f"companion-solver modules imported: {_leaked}   (must be [])")
if _leaked:
    failures.append("companion-solver module was imported")

if failures:
    print("\nFAILURES:")
    for f in failures:
        print("  - " + f)
    print("=" * 78)
    _sys.exit(1)

print("ALL CHECKS PASSED")
print("=" * 78)
_sys.exit(0)
