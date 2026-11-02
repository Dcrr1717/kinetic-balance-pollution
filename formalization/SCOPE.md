# Lean 4 formalization scope (Paper T)

The formalization has two layers. Both are built by `lake build` in this
folder (Lean 4 + Mathlib).

1. **`FiberLemmas.lean`** (namespace `FeastLemmas`): algebraic identities
   over the reals and a few auxiliary lemmas. This is the original,
   deliberately modest layer. It is unchanged.
2. **`KineticBalance/`** (namespace `KineticBalance`): the operator-level
   layer. Here the paper's statements are formalized as statements about
   the free Dirac matrix `H₀`, its genuine spectral projectors `Λ±`,
   orthogonal projectors onto trial spaces, and operator norms. It builds
   on layer 1.

This file is the authoritative inventory. `README.md` in this folder is a
short reproduction note and must not claim more than what is listed here.
The statement-by-statement map from the paper to Lean is
`../docs/FORMALIZATION.md`.

Neither layer contains a `sorry` or adds an `axiom`. This was checked,
not merely asserted: `#print axioms` on the main declarations returns
`[propext, Classical.choice, Quot.sound]`, the three standard axioms of
Lean's logic, and in particular never `sorryAx`. A `grep` for `sorry`
over the sources finds nothing.

## Layer 1: `FiberLemmas.lean` (scalar identities)

No statement about matrices, projectors, operator norms or spectra is
made in this file. Where the paper's proof reduces such a statement to a
scalar identity, it is that scalar identity which is checked. The
manuscript reproduces this table as Table 1.

| Identifier in Lean | Informal meaning | Maps to paper |
|---|---|---|
| `w_sq`, `w_pos`, `one_lt_w` | facts about w = √(1+4t²) | (auxiliary) |
| `rho_nonneg` | ρ ≥ 0 for t ≥ 0 | (auxiliary) |
| `key_identity` | t − ρ = 4t³/(1+w)², ρ = 2t/(1+w) — the exact balanced-leakage numerator | Eq. (key) in proof of Thm. 3.1 (per-mode leakage) |
| `rho_lt` | ρ < t for t > 0 — resolves the absolute value / sign in the leakage formula | proof of Thm. 3.1 |
| `l_spl_eq` | ℓ(u_spl) = ρ/√(1+ρ²) | Eq. (lspl), Thm. 3.1 |
| `l_bal_eq_l_pos` | ℓ(u_bal) = ℓ(u_pos) — the two inner products are opposite numbers | Eq. (lbal), Thm. 3.1 |
| `l_anti_eq` | ℓ(u_anti) = (t+ρ)/√((1+ρ²)(1+t²)) | Eq. (lanti), Thm. 3.1 |
| `fiber_pythagoras` | ⟨v₊,b⟩² + ⟨v₋,b⟩² = ‖b‖², i.e. g² = 1 − ℓ² | proof step of Thm. 4.1 |
| `defect_identity` | g²(1 − 2g² + g²) = g²(1−g²) — scalar form of the per-fiber defect reduction | proof step of Thm. 4.1 (global conformity defect) |
| `bal_above_gap` | R_bal − c² = 2c²t²/(1+t²), with R_bal = c²(1+3t²)/(1+t²) | Thm. 5.1(a) |
| `bal_above_gap_nonneg` | R_bal − c² ≥ 0 | Thm. 5.1(a) |
| `anti_below_gap` | c² − R_anti = c²(2−4t²)/(1+t²) | proof of Thm. 5.1(a) |
| `anti_above_bottom` | R_anti + c² = 6c²t²/(1+t²) | proof of Thm. 5.1(a) |
| `anti_in_gap` | c²(5t²−1)/(1+t²) lies strictly in (−c², c²) iff 0 < t² < 1/2 | Thm. 5.1(a) (pollution dichotomy) |
| `anti_strict_mono` | R_anti is strictly increasing in t ≥ 0 — the gap sweep | Remark following Thm. 5.1 |
| `anti_midgap` | 5(1/√5)² − 1 = 0 — the mid-gap crossing at t = 1/√5 | Thm. 5.1(a) |

In this file the leakage lemmas are stated with the two-component inner
products written out as real expressions in the fiber coordinates. The
eigenvector components `v₊ = (1,ρ)/√(1+ρ²)`, `v₋ = (−ρ,1)/√(1+ρ²)` are
substituted by hand. Layer 2 removes this limitation.

## Layer 2: `KineticBalance/` (operator level)

| File | Content |
|---|---|
| `SpectralProjector.lean` | `Λ₊`, `Λ₋` of a symmetric operator on a finite-dimensional real inner-product space, defined as orthogonal projectors onto sums of eigenspaces; action on eigenvectors; `Λ₊ + Λ₋ = I` when 0 is not an eigenvalue |
| `GlobalDefect.lean` | abstract Thm. 4.1: `‖(I−Π)PΠ‖ = max_i ‖Pb_i‖·‖(I−P)b_i‖` for an orthogonal projector `P`, orthogonal `P`-invariant fibers and unit trial vectors `b_i` in them; the per-fiber norm identity `‖(I−bbᵀ)Pb‖ = ‖Pb‖·‖(I−P)b‖`; abstract Cor. 4.2 |
| `Fiber.lean` | abstract Dirac fiber (`T` acts as `h(2ct)` on an orthonormal pair): eigenvectors `v±` and eigenvalues `±c²√(1+4t²)` derived; `Λ±` on the fiber; Thm. 3.1 (all four leakage laws) computed from the projectors; per-fiber factor `ℓ√(1−ℓ²)`; Rayleigh values |
| `DiracMatrix.lean` | the matrix `H₀ = [[c²I, cK],[cKᵀ, −c²I]]`; Prop. 2.1 from singular triples of `K`; free spectral gap `|μ| ≥ c²`; Thm. 3.1, **Thm. 4.1** (both `Λ₊` and `Λ₋`), Cor. 4.2 and Thm. 5.1(a) (Galerkin form, spurious in-gap eigenvalues) for `H₀` |

Main theorems (all in namespace `KineticBalance`):

| Lean | Paper |
|---|---|
| `dirac_isDiracFiber`, `dirac_fiber_isOrtho`, `energy_eq` | Prop. 2.1 |
| `dirac_leakage` | Thm. 3.1 |
| `dirac_global_defect_pos`, `dirac_global_defect_neg` | **Thm. 4.1** |
| `dirac_dkb_defect_pos`, `dirac_dkb_defect_neg` | Cor. 4.2 |
| `dirac_galerkin_eigen`, `dirac_anti_galerkin_in_gap`, `dirac_bal_galerkin_above_gap`, `dirac_anti_galerkin_spurious`, `diracOp_eigenvalue_abs_ge` | Thm. 5.1(a) |

Hypotheses are explicit in each statement. The singular value
decomposition of `K` is an **input**: the theorems take any family of
singular triples (`SingularSystem`: orthonormal `u_j`, orthonormal `v_j`,
`K v_j = σ_j u_j`, `Kᵀ u_j = σ_j v_j`, `σ_j ≥ 0`), and `c > 0`.

## Claimed in the paper text but NOT in Lean

| Claim | Status |
|---|---|
| Fiber decomposition (Prop. 2.1): completeness, i.e. the fibers plus `ker K`, `ker Kᵀ` exhaust the space | not formalized. Invariance, orthogonality and the 2×2 block are formalized; the main theorems do not need completeness |
| Existence of the SVD of `K` | taken as a hypothesis (`SingularSystem`), not constructed |
| Thm. 5.1(a): the `b_j` are a complete eigenbasis of the Galerkin compression (no other Galerkin eigenvalues) | not written out. Each `b_j` is proved to be an eigenvector, and the `b_j` are orthonormal |
| Dichotomy parts (b)–(d): Weyl perturbation, Galerkin pairing | not formalized |
| Cusp lemma (Thms. 6.1, 6.2: exact representation, universal rate) | not formalized |
| Conditional exclusion window (Thm. 8.1: Schur/Feshbach argument) | not formalized |
| Conjectures 7.1, 7.2 | conjectures; not theorems, not formalized |

## How to check

A pinned Lake project ships in this folder, so the check is turnkey:

```
lake exe cache get      # prebuilt Mathlib oleans (several GB)
lake build              # checks FiberLemmas.lean and KineticBalance/
```

If the Mathlib cache host is not reachable, `lake build` compiles the
needed part of Mathlib from source. This is slow but gives the same
result.

Pins:

| | |
|---|---|
| Lean toolchain (`lean-toolchain`) | `leanprover/lean4:v4.33.0` |
| Mathlib (`lakefile.toml`) | tag `v4.33.0` = commit `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Full resolved dependency graph | `lake-manifest.json` |

The `FiberLemmas.lean` in this folder is byte-identical (modulo line
endings) to the copy in the project repository at
`paper_teorema/lean/`, commit
`e80eda6fb4ff7c6fecca4e8511553aabea4d638d`. The `KineticBalance/` layer
is new and has no counterpart there yet.
