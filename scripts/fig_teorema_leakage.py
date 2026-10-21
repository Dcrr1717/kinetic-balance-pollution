"""Figure for the theorem paper: measured per-mode sector leakages of the
four trial families in the real Laguerre discretization, overlaid with
the EXACT algebraic laws of Lemma L1' (no fitted parameters)."""

import sys
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from dirac import RadialDiracBasis  # noqa: E402

plt.rcParams.update({
    "font.family": "serif", "font.size": 10,
    "axes.labelsize": 10.5, "xtick.labelsize": 9.5, "ytick.labelsize": 9.5,
    "legend.fontsize": 8.6, "axes.grid": True, "grid.alpha": 0.3,
    "figure.dpi": 200, "savefig.bbox": "tight", "savefig.pad_inches": 0.02,
})

B = RadialDiracBasis(240, -1, 0.0, 0.9, cert_tol=1e-6)
cv = B.c
K = B._me(B.f, 2.0 * cv * B.h)
U, S, Vt = np.linalg.svd(K)
T = S / (2 * cv)
n = K.shape[0]
H0 = np.block([[cv**2 * np.eye(n), cv * K], [cv * K.T, -cv**2 * np.eye(n)]])
ev, W = np.linalg.eigh(H0)
Lm = W[:, ev < 0] @ W[:, ev < 0].T
Lp = np.eye(2 * n) - Lm


def leak(P, up, lo):
    u = np.concatenate([up, lo])
    return np.linalg.norm(P @ u) / np.linalg.norm(u)


fams = {"split $(1,0)$": [], "balanced $(1,t)$": [],
        "positronic $(-t,1)$": [], "anti-balanced $(t,1)$": []}
Z = np.zeros(n)
for j in range(n):
    u, v = U[:, j], Vt[j]
    t = T[j]
    fams["split $(1,0)$"].append(leak(Lm, u, Z))
    fams["balanced $(1,t)$"].append(leak(Lm, u, t * v))
    fams["positronic $(-t,1)$"].append(leak(Lp, -t * u, v))
    fams["anti-balanced $(t,1)$"].append(leak(Lp, t * u, v))

o = np.argsort(T)
Ts = T[o]
fig, ax = plt.subplots(figsize=(390.0 / 72.27, 3.1))
mk = {"split $(1,0)$": ("o", "tab:blue"),
      "balanced $(1,t)$": ("s", "tab:orange"),
      "positronic $(-t,1)$": ("D", "tab:green"),
      "anti-balanced $(t,1)$": ("^", "tab:red")}
for name, vals in fams.items():
    m, col = mk[name]
    ax.loglog(Ts, np.array(vals)[o], m, ms=3.2, mfc="none", mec=col,
              mew=0.8, label=name)
tt = np.logspace(np.log10(Ts.min()), np.log10(0.5), 100)
w = np.sqrt(1 + 4 * tt**2)
r = 2 * tt / (1 + w)
A, Bn = np.sqrt(1 + r**2), np.sqrt(1 + tt**2)
ax.loglog(tt, r / A, "-", color="tab:blue", lw=1.0)
ax.loglog(tt, (tt - r) / (A * Bn), "-", color="tab:orange", lw=1.0)
ax.loglog(tt, (tt + r) / (A * Bn), "-", color="tab:red", lw=1.0)
ax.text(2e-3, 4e-9, r"$\ell = t^3 + O(t^5)$", color="tab:orange",
        fontsize=8.5, rotation=32)
ax.text(2e-3, 6e-3, r"$\ell = t - \frac{3}{2}t^3 + O(t^5)$",
        color="tab:blue", fontsize=8.5, rotation=12)
ax.set_xlabel(r"fiber parameter  $t_j = \sigma_j/2c$")
ax.set_ylabel(r"sector leakage  $\ell$")
ax.legend(loc="upper left", handlelength=1.2)
fig.tight_layout()
out = ROOT / "paper_teorema" / "figures" / "figT_leakage"
for ext in ("pdf", "png"):
    fig.savefig(f"{out}.{ext}")
print("figT_leakage done")
