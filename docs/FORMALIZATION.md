# Formalization map (Lean 4 + Mathlib)

This document maps each statement of the Paper T manuscript ("Exact fiber
analysis of kinetic-balance spectral pollution for the radial Dirac
operator") to its Lean declaration. It states what is machine-checked,
under which hypotheses, and what is not.

Sources: `formalization/` (Lake project, pinned to Lean `v4.33.0` and
Mathlib `v4.33.0` = commit `db584cd6d46c92f209a44c0f1c829460d327499d`).

* `FiberLemmas.lean` (namespace `FeastLemmas`): the original scalar
  identities, unchanged and byte-identical to the published copy.
* `KineticBalance/*.lean` (namespace `KineticBalance`): the operator-level
  development added on top of it, with genuine spectral projectors,
  operator norms and the concrete Dirac matrix.

> **Note on numbering.** The README lists `main.tex`, but it is not in
> this repository. The theorem numbers and equation labels below are the
> ones used in `formalization/SCOPE.md`, in the docstrings of
> `FiberLemmas.lean` and in `reproducibility/selfcheck_fiber.py`. If the
> manuscript's numbering has changed, only the "Paper" column needs to be
> updated.

## Central result

**Theorem 4.1 (exact global conformity defect), for the free Dirac matrix
itself, is a closed, machine-checked theorem:**
`KineticBalance.dirac_global_defect_pos` (with `Λ₊`) and
`KineticBalance.dirac_global_defect_neg` (with `Λ₋`).

Informally: let `H₀ = [[c² I, c K], [c Kᵀ, −c² I]]` with `c > 0`, and let
`(σ_j, u_j, v_j)` be singular triples of `K`. Pick one of the four
kinetic-balance families `f ∈ {bal, spl, pos, anti}`. Let `V` be the span
of the normalized trial vectors `b_j` of `f`, one per fiber, and `Π` the
orthogonal projector onto `V`. Then

```
‖(I − Π) Λ± Π‖ = max_j ℓ_f(t_j) · √(1 − ℓ_f(t_j)²),     t_j = σ_j / (2c),
```

where `Λ±` are the spectral projectors of `H₀` and `ℓ_f` is the
closed-form leakage of Theorem 3.1. Nothing in this chain is substituted
by hand:

1. The fiber structure of `H₀` is derived from the matrix (`diracOp_inlE`,
   `diracOp_inrE`, `dirac_isDiracFiber`).
2. The fiber eigenvectors and eigenvalues `±c²√(1+4t²)` are derived
   (`IsDiracFiber.apply_vPlus`, `IsDiracFiber.apply_vMinus`).
3. `Λ±` are defined from the eigenspaces of `H₀`
   (`specProjPos`, `specProjNeg`), and their action on each fiber is
   derived (`IsDiracFiber.specProjPos_fv`, `IsDiracFiber.specProjNeg_fv`).
4. The leakages are computed from these projectors
   (`IsDiracFiber.leakage_trialDir`).
5. The operator norm is evaluated exactly, by block-diagonalization
   (`global_defect`).

## Statement-by-statement map

Legend: **closed** means proved in Lean with no `sorry`, under exactly the
hypotheses listed. **scalar** means only the underlying real-number
identity is proved. **not formalized** means there is no Lean counterpart.

### Setting and Proposition 2.1 (fiber decomposition)

| Paper | Lean | Status |
|---|---|---|
| Free Dirac matrix `H₀ = [[c²I, cK],[cKᵀ, −c²I]]` | `diracMatrix`, `diracOp` (operator on `EuclideanSpace ℝ (m ⊕ n)`) | definition |
| `H₀` is symmetric | `diracMatrix_isHermitian`, `diracOp_isSymmetric` | closed |
| Spectral projectors `Λ±` of a symmetric operator | `posSpectralSubspace`, `negSpectralSubspace`, `specProjPos`, `specProjNeg` | definition: orthogonal projector onto the sum of the eigenspaces with positive (resp. negative) eigenvalue |
| `Λ±` act as identity / zero on eigenvectors of the right / wrong sign | `specProjPos_apply_of_pos`, `specProjPos_apply_of_nonpos`, `specProjNeg_apply_of_neg`, `specProjNeg_apply_of_nonneg` | closed |
| `Λ₊ + Λ₋ = I` when `0 ∉ spec` (sanity check of the definition) | `specProjPos_add_specProjNeg` | closed |
| Prop. 2.1: a singular triple `Kv = σu`, `Kᵀu = σv` gives an `H₀`-invariant fiber `span{(u,0),(0,v)}` on which `H₀` acts as `h(σ) = [[c², cσ],[cσ, −c²]]` | `dirac_isDiracFiber` (via `diracOp_inlE`, `diracOp_inrE`) | closed |
| Distinct fibers are orthogonal | `dirac_fiber_isOrtho` | closed |
| Fiber eigenpairs `h v± = ±E v±`, `v₊ = (1,ρ)/√(1+ρ²)`, `v₋ = (−ρ,1)/√(1+ρ²)` | `IsDiracFiber.apply_vPlus`, `IsDiracFiber.apply_vMinus`, `IsDiracFiber.norm_vPlus`, `IsDiracFiber.norm_vMinus`, `IsDiracFiber.inner_vPlus_vMinus` | closed |
| `E(σ) = √(c⁴+c²σ²) = c²√(1+4t²)` | `energy_eq` | closed |
| Fibers are `Λ±`-invariant | `IsDiracFiber.specProjPos_mem_span`, `IsDiracFiber.specProjNeg_mem_span` | closed |
| **Completeness**: for a complete singular system (`CompleteSingularSystem`: `σ_j > 0`, `span{u} ⊔ ker Kᵀ = ℝᵐ`, `span{v} ⊔ ker K = ℝⁿ`), the fibers `W_j`, the upper kernel block `ker Kᵀ ⊕ 0` and the lower kernel block `0 ⊕ ker K` (`DiracBlock`, `diracBlock`) are mutually orthogonal and span `ℝ^(m⊕n)`: an internal direct sum | `diracBlock_orthogonalFamily`, `diracBlock_iSup_eq_top`, `diracBlock_isInternal` | closed |
| Every block is `H₀`-invariant; `H₀ = +c²` on `ker Kᵀ ⊕ 0` and `H₀ = −c²` on `0 ⊕ ker K` | `diracBlock_invariant`, `diracOp_inlE_of_ker`, `diracOp_inrE_of_ker` | closed |
| The spectral projectors are block diagonal: `Λ±` map every block into itself; on the kernel blocks `Λ₊ = I, Λ₋ = 0` (upper) and `Λ₊ = 0, Λ₋ = I` (lower) | `diracBlock_specProjPos_invariant`, `diracBlock_specProjNeg_invariant`, `specProj_inlE_of_ker`, `specProj_inrE_of_ker` | closed (hyp.: `c ≠ 0`) |
| `Λ₊ + Λ₋ = I` for `H₀` | `dirac_specProjPos_add_specProjNeg` | closed (hyp.: `c ≠ 0`) |
| Existence of the SVD of `K`: every real `K` has a complete singular system | `exists_completeSingularSystem` (via the abstract `exists_singularSystem`, built from the spectral theorem for `KᵀK`) | closed |
| Unconditional form: for every `K` and `c`, an SVD whose blocks give an orthogonal internal direct sum of `H₀`-invariant subspaces | `exists_dirac_block_decomposition` | closed |

### Theorem 3.1 (exact per-mode leakage)

The leakage of a trial vector is `ℓ(u) = ‖Λ_wrong u‖ / ‖u‖`
(`leakage`), with `Λ_wrong = Λ₋` for the electronic families `bal`, `spl`
and `Λ₊` for the positronic families `pos`, `anti` (`wrongProj`). Trial
directions in fiber coordinates (`Family.coeffs`, `trialDir`):
`u_bal = (1,t)`, `u_spl = (1,0)`, `u_pos = (−t,1)`, `u_anti = (t,1)`.

| Paper | Lean | Status |
|---|---|---|
| Thm 3.1, all four laws, in an abstract Dirac fiber | `IsDiracFiber.leakage_trialDir` | closed (hyp.: `T` symmetric, `c ≠ 0`, `t ≥ 0`) |
| Thm 3.1, all four laws, for `H₀` itself | `dirac_leakage` | closed (hyp.: `SingularSystem`, `c > 0`) |
| Closed forms (lspl), (lbal), (lanti) | `Family.leak` | definition |
| (lbal) in the `4t³/(1+w)²` form, via Eq. (key) | `Family.leak_bal_eq_key` (uses `FeastLemmas.key_identity`) | closed |
| `ℓ_bal = ℓ_pos` | `Family.leak_pos_eq_leak_bal` | closed |
| Eq. (key) `t − ρ = 4t³/(1+w)²`; `ρ < t`; sign resolution | `FeastLemmas.key_identity`, `FeastLemmas.rho_lt`, `KineticBalance.rho_le`, `rho_nonneg` | closed (scalar) |
| Previous scalar forms `l_spl_eq`, `l_bal_eq_l_pos`, `l_anti_eq` | `FeastLemmas.*` | scalar, kept unchanged; now superseded by the operator-level statements above |

### Theorem 4.1 (exact global conformity defect)

| Paper | Lean | Status |
|---|---|---|
| Per-fiber identity `‖(I − bbᵀ)Pb‖ = ‖Pb‖·‖(I−P)b‖` (`= g√(1−g²)`), for any orthogonal projector `P` and unit `b`, **as a norm statement** | `fiber_defect_norm` | closed |
| `g² = 1 − ℓ²` (fiber Pythagoras) | `IsDiracFiber.norm_fv_sq`, `coordPlus_sq_add_coordMinus_sq` | closed |
| Per-fiber factor `‖Λ± b‖·‖(I−Λ±) b‖ = ℓ√(1−ℓ²)` for the normalized trial vector of each family | `IsDiracFiber.defect_factor_pos`, `IsDiracFiber.defect_factor_neg` | closed |
| Block-diagonal norm law, abstract form: `‖(I−Π)PΠ‖ = max_i ‖P b_i‖·‖(I−P) b_i‖` for orthogonal `P`-invariant fibers `W_i` and unit `b_i ∈ W_i` | `global_defect` | closed |
| **Thm 4.1 for `H₀`: `‖(I−Π)Λ₊Π‖ = max_j ℓ_j√(1−ℓ_j²)`** | **`dirac_global_defect_pos`** | **closed** (hyp.: `SingularSystem`, `c > 0`, nonempty index set) |
| **Same value with `Λ₋`** | **`dirac_global_defect_neg`** | **closed** |
| Old scalar step `g²(1 − 2g² + g²) = g²(1−g²)` | `FeastLemmas.defect_identity` | scalar, kept; superseded by `fiber_defect_norm` |

Remark: `global_defect` does not need the fibers to exhaust the space.
The singular systems it accepts include the complete one that
`exists_completeSingularSystem` constructs for every `K`
(`CompleteSingularSystem.toSingularSystem`).
`dirac_global_defect_pos/neg` therefore hold both for the untruncated
single-family space (all singular triples) and for any truncation to a
subfamily of singular triples.

### Corollary 4.2 (exact conformity of the dual-kinetic-balance pair space)

| Paper | Lean | Status |
|---|---|---|
| Abstract: a `P`-invariant trial space has `(I − Π)PΠ = 0` | `defect_eq_zero_of_invariant` | closed |
| The DKB pair space `span{u_bal, u_pos}` (per fiber) contains each fiber and is `Λ±`-invariant | `dkbSpace`, `diracFiber_le_dkbSpace`, `dkbSpace_invariant` | closed |
| **Cor 4.2 for `H₀`: `(I−Π)Λ±Π = 0`** | `dirac_dkb_defect_pos`, `dirac_dkb_defect_neg` | closed |

### Theorem 5.1 (pollution dichotomy)

| Paper | Lean | Status |
|---|---|---|
| Eq. (rayleigh): `⟨b, H₀ b⟩` for the unit trial vector of each family equals `R_bal`, `R_spl = c²`, `R_pos`, `R_anti` | `IsDiracFiber.rayleigh_trialUnit`, `Family.rayleigh` | closed |
| (a) Galerkin form: each `b_j` is an eigenvector of the compression `Π H₀` with eigenvalue `R_f(t_j)` | `dirac_galerkin_eigen` | closed |
| (a) Anti-balanced eigenvalue in the gap iff `0 < t_j² < 1/2` | `dirac_anti_galerkin_in_gap` (uses `FeastLemmas.anti_in_gap`) | closed |
| (a) Balanced eigenvalue never in the gap (`R_bal ≥ c²`) | `dirac_bal_galerkin_above_gap` | closed |
| Free spectral gap: every eigenvalue `μ` of `H₀` has `|μ| ≥ c²` | `norm_diracOp_sq`, `sq_mul_norm_le_norm_diracOp`, `diracOp_eigenvalue_abs_ge` | closed |
| (a) The in-gap anti-balanced Galerkin eigenvalues are spurious (not eigenvalues of `H₀`) | `dirac_anti_galerkin_spurious` | closed |
| (a) Scalar identities: `R_bal − c²`, `c² − R_anti`, `R_anti + c²`, monotone sweep, mid-gap at `t = 1/√5` | `FeastLemmas.bal_above_gap`, `bal_above_gap_nonneg`, `anti_below_gap`, `anti_above_bottom`, `anti_strict_mono`, `anti_midgap` | closed (scalar) |
| (a) "These are *all* the Galerkin eigenvalues" (the `b_j` form an eigenbasis of `ΠH₀|_V`) | — | not stated separately. It follows from `dirac_galerkin_eigen` because the `b_j` are an orthonormal basis of `V`, but this step is not written in Lean |
| (b)–(d): perturbation by a potential (Weyl), Galerkin pairing | — | **not formalized** |

### Remaining sections

| Paper | Status |
|---|---|
| Cusp lemma, Thms 6.1, 6.2 (exact representation, universal rate) | **not formalized**. The numbers are checked numerically in `scripts/l3_cusp_rate.py`, `scripts/test_cusp_quadrature.py` and `scripts/et1_l3c_universality.py` |
| Conjectures 7.1, 7.2 | conjectures, not theorems; not formalized |
| Conditional exclusion window, Thm 8.1 (Schur/Feshbach) | **not formalized**. Numerics in `scripts/t1_bounded_window.py`, `scripts/t1c_coulomb_step.py` |
| Coulomb-frontier numbers of Sections 7–8 | numerical only. They require the separate spectral engine (see README) |

The numerical self-check of Sections 2–5 (`reproducibility/selfcheck_fiber.py`)
covers the same statements as the Lean development above. The two are
independent checks.

## Trust base

* No `sorry` and no added `axiom` anywhere in `FiberLemmas.lean` or
  `KineticBalance/`. `formalization/AxiomCheck.lean` runs `#print axioms` on
  41 main declarations. Every one returns exactly
  `[propext, Classical.choice, Quot.sound]` (checked 2026-11-01, together
  with `lake build`: `Build completed successfully (3195 jobs)`).
* `FiberLemmas.lean` is unchanged by this layer; `KineticBalance` imports it
  and reuses `key_identity`, `rho_lt`, `rho_nonneg`, `w_sq`, `w_pos`,
  `anti_in_gap` and `bal_above_gap_nonneg`.
* Hypotheses are explicit in each statement. The only modelling choices are:
  * `Λ±` are *defined* as orthogonal projectors onto sums of eigenspaces.
    This is the standard definition in finite dimension, and
    `specProjPos_add_specProjNeg` confirms `Λ₊ + Λ₋ = I` when `H₀` has no
    zero eigenvalue.
  * The theorems take a singular system (`SingularSystem`) as input, so any
    SVD, or any subfamily of one, can be supplied. A complete one always
    exists (`exists_completeSingularSystem`), so the hypothesis is never
    vacuous.
  * The fiber parameter is `t_j = σ_j/(2c)` with `σ_j ≥ 0`, `c > 0`.

## Reproducing the check

```
cd formalization
lake exe cache get    # prebuilt Mathlib oleans; if the cache host is unreachable,
                      # `lake build` compiles the needed part of Mathlib from source
lake build            # builds FiberLemmas and KineticBalance
lake env lean AxiomCheck.lean   # axiom audit: expect only the three standard axioms
```
