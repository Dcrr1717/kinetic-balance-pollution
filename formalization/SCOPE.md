# Lean 4 formalization scope (Paper T)

Machine-checked in `FiberLemmas.lean` (Lean 4 + Mathlib, namespace
`FeastLemmas`). The scope is deliberately modest: **algebraic
identities over the reals**, plus a few auxiliary lemmas. Nothing else
in the paper is formalized. In particular, no statement about
matrices, projectors, operator norms or spectra is formalized; where
the paper's proof reduces such a statement to a scalar identity, it is
that scalar identity which is checked.

This file is the authoritative inventory. `README.md` in this folder
is a short reproduction note and must not claim more than what is
listed here; the manuscript reproduces this table as Table 1.

The development contains no `sorry` and introduces no `axiom`. This
was checked, not merely asserted: `#print axioms` on each of the 18
declarations returns `[propext, Classical.choice, Quot.sound]` — the
three standard axioms of Lean's logic — and in particular never
`sorryAx`.

## Included in FiberLemmas.lean

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

The leakage lemmas are stated with the two-component inner products
written out explicitly as real expressions in the fiber coordinates,
not as inner products in an abstract inner-product space; the
eigenvector components `v₊ = (1,ρ)/√(1+ρ²)`, `v₋ = (−ρ,1)/√(1+ρ²)` are
substituted by hand rather than derived inside Lean.

## Claimed in the paper text but NOT in Lean

| Claim | Status |
|---|---|
| Fiber decomposition (Prop. 2.1, SVD block-diagonalization) | not formalized |
| Full leakage formulas as inner products with fiber eigenvectors (Thm. 3.1 statement) | not formalized (only the identities listed above) |
| Global defect = max over fibers via block-diagonal norm (Thm. 4.1 statement) | not formalized (only the scalar reduction) |
| Exact conformity of the dual-balance pair space (Cor. 4.2) | not formalized |
| Dichotomy parts (b)–(d): Weyl perturbation, Galerkin pairing | not formalized |
| Cusp lemma (Thms. 6.1, 6.2: exact representation, universal rate) | not formalized |
| Conditional exclusion window (Thm. 8.1: Schur/Feshbach argument) | not formalized |
| Conjectures 7.1, 7.2 | conjectures; not theorems, not formalized |

## How to check

A pinned Lake project ships in this folder, so the check is turnkey:

```
lake exe cache get      # prebuilt Mathlib oleans (several GB)
lake build              # checks FiberLemmas.lean
```

Pins:

| | |
|---|---|
| Lean toolchain (`lean-toolchain`) | `leanprover/lean4:v4.33.0` |
| Mathlib (`lakefile.toml`) | tag `v4.33.0` = commit `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Full resolved dependency graph | `lake-manifest.json` |

The `FiberLemmas.lean` in this folder is byte-identical (modulo line
endings) to the copy in the project repository at
`paper_teorema/lean/`, commit
`e80eda6fb4ff7c6fecca4e8511553aabea4d638d`.
