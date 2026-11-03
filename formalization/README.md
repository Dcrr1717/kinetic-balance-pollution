# Machine-checked results (Lean 4 + Mathlib)

Two Lean libraries are built from this folder:

* **`FiberLemmas`** (`FiberLemmas.lean`, namespace `FeastLemmas`): the
  core algebraic identities of the paper, as identities **over the
  reals**. It is unchanged from the published version.
* **`KineticBalance`** (`KineticBalance/*.lean`, namespace
  `KineticBalance`): the operator-level statements. It covers the free
  Dirac matrix `H₀ = [[c²I, cK],[cKᵀ, −c²I]]`, its genuine spectral
  projectors `Λ±`, orthogonal projectors onto trial spaces, and operator
  norms.

`SCOPE.md` in this folder is the authoritative inventory. Just as
importantly, it lists everything the paper claims that is *not*
formalized. `../docs/FORMALIZATION.md` maps each paper statement to its
Lean name. The tables below are only a summary and must not be read as
claiming more.

## Operator level (`KineticBalance`)

| Lean theorem | What is actually proved | Paper statement |
|---|---|---|
| `dirac_isDiracFiber`, `dirac_fiber_isOrtho`, `energy_eq` | a singular triple of `K` spans an `H₀`-invariant fiber on which `H₀ = h(σ)`; distinct fibers are orthogonal; `E = √(c⁴+c²σ²)` | Prop. 2.1 |
| `dirac_leakage` | `‖Λ_wrong u‖/‖u‖` equals the closed form, for all four families, with `Λ±` the spectral projectors of `H₀` | Thm 3.1 |
| `dirac_global_defect_pos`, `dirac_global_defect_neg` | `‖(I−Π)Λ±Π‖ = max_j ℓ_j √(1−ℓ_j²)` for the single-family trial space | **Thm 4.1** |
| `dirac_dkb_defect_pos`, `dirac_dkb_defect_neg` | `(I−Π)Λ±Π = 0` for the dual-kinetic-balance pair space | Cor 4.2 |
| `dirac_galerkin_eigen`, `dirac_anti_galerkin_in_gap`, `dirac_anti_galerkin_spurious`, `dirac_bal_galerkin_above_gap` | each trial vector is an eigenvector of `ΠH₀` with eigenvalue `R_f(t_j)`; the anti-balanced ones lie in the gap iff `0 < t_j² < 1/2` and are then not eigenvalues of `H₀`; the balanced ones are `≥ c²` | Thm 5.1(a) |
| `diracBlock_isInternal`, `diracBlock_invariant`, `diracBlock_specProjPos_invariant`, `exists_dirac_block_decomposition` | the fibers, `ker Kᵀ ⊕ 0` and `0 ⊕ ker K` form an orthogonal internal direct sum of `H₀`- and `Λ±`-invariant blocks (`H₀ = ±c²` on the kernel blocks) | Prop. 2.1 (completeness) |
| `exists_completeSingularSystem` | every real `K` has a complete singular system (SVD), built from the spectral theorem for `KᵀK` | SVD existence |
| `diracOp_eigenvalue_abs_ge` | every eigenvalue `μ` of `H₀` has `|μ| ≥ c²` | free spectral gap |
| `global_defect`, `fiber_defect_norm`, `defect_eq_zero_of_invariant` | the abstract operator-norm statements behind Thm 4.1 / Cor 4.2 | proofs of Thm 4.1 / Cor 4.2 |

Most of these theorems take a family of singular triples of `K` as a
hypothesis (`SingularSystem`). `exists_completeSingularSystem` constructs a
complete one for every `K`, so the hypothesis is never vacuous.

## Scalar level (`FiberLemmas`)

| Lean theorem | What is actually proved | Paper statement |
|---|---|---|
| `key_identity` | t − ρ = 4t³/(1+w)², with w = √(1+4t²), ρ = 2t/(1+w) | Eq. (key), proof of Thm 3.1 |
| `rho_lt` | ρ < t for t > 0 | sign resolution in Thm 3.1 |
| `l_spl_eq` | ℓ(u_spl) = ρ/√(1+ρ²) | Eq. (lspl), Thm 3.1 |
| `l_bal_eq_l_pos` | the balanced and positronic leakages are absolute values of opposite numbers, hence equal | Eq. (lbal), Thm 3.1 |
| `l_anti_eq` | ℓ(u_anti) = (t+ρ)/√((1+ρ²)(1+t²)) | Eq. (lanti), Thm 3.1 |
| `fiber_pythagoras` | ⟨v₊,b⟩² + ⟨v₋,b⟩² = ‖b‖² in the fiber, i.e. g² = 1 − ℓ² | proof step of Thm 4.1 |
| `defect_identity` | the **scalar polynomial identity** g²(1 − 2g² + g²) = g²(1−g²), closed by `ring`. The norm statement is `KineticBalance.fiber_defect_norm` | proof step of Thm 4.1 |
| `bal_above_gap` | R_bal − c² = 2c²t²/(1+t²) | Thm 5.1(a) |
| `bal_above_gap_nonneg` | R_bal − c² ≥ 0 | Thm 5.1(a) |
| `anti_below_gap` | c² − R_anti = c²(2−4t²)/(1+t²) | proof of Thm 5.1(a) |
| `anti_above_bottom` | R_anti + c² = 6c²t²/(1+t²) | proof of Thm 5.1(a) |
| `anti_in_gap` | R_anti ∈ (−c²,c²) ⇔ 0 < t² < 1/2 | Thm 5.1(a) |
| `anti_strict_mono` | R_anti is strictly increasing in t ≥ 0 | Remark after Thm 5.1 |
| `anti_midgap` | 5(1/√5)² − 1 = 0 | mid-gap crossing, Thm 5.1(a) |

Auxiliary: `w_sq`, `w_pos`, `one_lt_w`, `rho_nonneg`.

There is no `sorry` and no added `axiom` in either library: `#print
axioms` on the main declarations returns exactly
`[propext, Classical.choice, Quot.sound]`, never `sorryAx`.

Verified on 2026-08-15 (`FiberLemmas` alone):
`Build completed successfully (3079 jobs)`.

Verified on 2026-11-01 (`FiberLemmas` + `KineticBalance`, with the pins
below; Mathlib compiled from source):
`Build completed successfully (3193 jobs)`. `lake env lean AxiomCheck.lean`
prints `[propext, Classical.choice, Quot.sound]` for all 29 audited
declarations.

Verified on 2026-11-03, after adding `SVD.lean` and `Completeness.lean`:
`Build completed successfully (3195 jobs)`; all 41 audited declarations
depend only on `[propext, Classical.choice, Quot.sound]`.

## Reproducing the check

A pinned Lake project ships alongside the source, so no `lake new` step
is needed:

```
# install elan (Lean toolchain manager), then, in this folder:
lake exe cache get          # prebuilt Mathlib oleans (several GB)
lake build                  # checks FiberLemmas.lean and KineticBalance/
```

If the Mathlib cache host is unreachable, skip `lake exe cache get`.
`lake build` then compiles the needed part of Mathlib from source, which
takes far longer but gives the same result.

Pins:

- `lean-toolchain` → `leanprover/lean4:v4.33.0`
- `lakefile.toml` → Mathlib tag `v4.33.0`,
  commit `db584cd6d46c92f209a44c0f1c829460d327499d`
- `lake-manifest.json` → the full resolved dependency graph
