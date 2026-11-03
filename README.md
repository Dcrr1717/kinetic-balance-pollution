# Paper T — Exact fiber analysis of kinetic-balance spectral pollution for the radial Dirac operator

Reproducibility repository for the Paper T manuscript (C. D. Reinoso, 2026),
prepared for the IMA Journal of Numerical Analysis.

## Contents
- `main.tex` — manuscript source (LaTeX, `amsart` class; bibliography is inline).
- `figT_leakage.pdf` — figure.
- `reproducibility/selfcheck_fiber.py` — numerical self-check of the fiber
  lemmas.
- `scripts/` — the numerical scripts behind the theorem's constants and the
  figure: fiber lemma (`l1prime_fiber_lemma.py`), global defect
  (`l2_global_defect.py`), cusp rate (`l3_cusp_rate.py`), bounded-window and
  Coulomb-step checks (`t1_bounded_window.py`, `t1c_coulomb_step.py`),
  universality / continuum-form / s+ onset studies
  (`et1_l3c_universality.py`, `et2_continuum_form_bound.py`,
  `et3_splus_onset.py`), ΔN measurement (`measure_deltaN.py`), the leakage
  figure (`fig_teorema_leakage.py`), and a quadrature test
  (`test_cusp_quadrature.py`).
- `formalization/` — the Lean formalization sources: the scalar identities
  (`FiberLemmas.lean`), the operator-level library (`KineticBalance/`, with
  Prop. 2.1 (including completeness of the fiber decomposition and SVD
  existence), Thms 3.1, 4.1, Cor. 4.2 and Thm 5.1(a) for the free Dirac
  matrix), `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
  `README.md`, `SCOPE.md`. The `.lake/` build/dependency tree is **not**
  included; run `lake exe cache get` (or `lake build`) to fetch Mathlib and
  build.
- `docs/FORMALIZATION.md` — map from each paper statement to its Lean name,
  stating exactly what is and is not machine-checked.

## How to reproduce
1. Create a Python environment (NumPy/SciPy/mpmath/matplotlib) and run the
   scripts in `scripts/` and `reproducibility/selfcheck_fiber.py`.
2. For the Lean part, from `formalization/` run `lake exe cache get` then
   `lake build`.
3. Rebuild the PDF with `latexmk -pdf main.tex`.

## Spectral engine
The numerical scripts in `scripts/` depend on the **spectral engine**, which is
maintained as a **separate repository** and must be **cited by its archived
DOI**. Install it into your environment (or place it on `PYTHONPATH`) before
running the scripts; it is deliberately **not** vendored into this repository.
