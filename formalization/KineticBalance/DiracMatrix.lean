/-
The free Dirac matrix `H₀ = [[c² I, c K], [c Kᵀ, −c² I]]` and the
end-to-end statements of the fiber analysis.

`K : Matrix m n ℝ` is the discrete kinetic block. A family of singular
triples `(σ j, u j, v j)` of `K` (orthonormal `u j`, orthonormal `v j`,
`K v j = σ j u j`, `Kᵀ u j = σ j v j`, `σ j ≥ 0`) is taken as hypothesis.
It can be the full SVD, or any subfamily of it. `Λ±` are the genuine
spectral projectors of `H₀` (`SpectralProjector.lean`).

* `dirac_isDiracFiber` (**Proposition 2.1**): `span{(u j, 0), (0, v j)}`
  is a Dirac fiber of `H₀` with `t j = σ j/(2c)`. Distinct fibers are
  orthogonal (`dirac_fiber_isOrtho`), and `c²√(1+4t²) = √(c⁴+c²σ²)`
  (`energy_eq`).
* `dirac_leakage` (**Theorem 3.1**): exact per-mode leakages, measured
  with the spectral projectors of `H₀` itself.
* `dirac_global_defect_pos`, `dirac_global_defect_neg` (**Theorem 4.1**):
  for the single-family trial space `V = span{b j}` with orthogonal
  projector `Π`,
  `‖(I − Π) Λ± Π‖ = max_j ℓ(t j) √(1 − ℓ(t j)²)`.
* `dirac_dkb_defect_pos`, `dirac_dkb_defect_neg` (**Corollary 4.2**): the
  dual-kinetic-balance pair space has zero defect.
* `dirac_galerkin_eigen`, `dirac_anti_galerkin_in_gap`
  (**Theorem 5.1(a)**, Galerkin form): each `b j` is an eigenvector of
  the compression `Π H₀` with eigenvalue `R(t j)`. For the anti-balanced
  family this eigenvalue lies strictly inside `(−c², c²)` iff
  `0 < t j² < 1/2`.
-/

import KineticBalance.Fiber
import KineticBalance.GlobalDefect
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Matrix.Block

open scoped InnerProductSpace
open Matrix WithLp

namespace KineticBalance

variable {m n : Type*}

/-! ### Upper and lower components -/

/-- The upper-component embedding `u ↦ (u, 0)`. -/
def inlE (u : EuclideanSpace ℝ m) : EuclideanSpace ℝ (m ⊕ n) := toLp 2 (Sum.elim (ofLp u) 0)

/-- The lower-component embedding `v ↦ (0, v)`. -/
def inrE (v : EuclideanSpace ℝ n) : EuclideanSpace ℝ (m ⊕ n) := toLp 2 (Sum.elim 0 (ofLp v))

lemma inlE_comp_inl (u : EuclideanSpace ℝ m) :
    (fun i => (inlE u : EuclideanSpace ℝ (m ⊕ n)) (Sum.inl i)) = ofLp u := rfl

lemma inlE_comp_inr (u : EuclideanSpace ℝ m) :
    (fun j => (inlE u : EuclideanSpace ℝ (m ⊕ n)) (Sum.inr j)) = 0 := rfl

lemma inrE_comp_inl (v : EuclideanSpace ℝ n) :
    (fun i => (inrE v : EuclideanSpace ℝ (m ⊕ n)) (Sum.inl i)) = 0 := rfl

lemma inrE_comp_inr (v : EuclideanSpace ℝ n) :
    (fun j => (inrE v : EuclideanSpace ℝ (m ⊕ n)) (Sum.inr j)) = ofLp v := rfl

section Inner

variable [Fintype m] [Fintype n]

@[simp] lemma inner_inlE_inlE (u u' : EuclideanSpace ℝ m) :
    ⟪(inlE u : EuclideanSpace ℝ (m ⊕ n)), inlE u'⟫_ℝ = ⟪u, u'⟫_ℝ := by
  simp [inlE, PiLp.inner_apply, Fintype.sum_sum_type]

@[simp] lemma inner_inrE_inrE (v v' : EuclideanSpace ℝ n) :
    ⟪(inrE v : EuclideanSpace ℝ (m ⊕ n)), inrE v'⟫_ℝ = ⟪v, v'⟫_ℝ := by
  simp [inrE, PiLp.inner_apply, Fintype.sum_sum_type]

@[simp] lemma inner_inlE_inrE (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) :
    ⟪(inlE u : EuclideanSpace ℝ (m ⊕ n)), inrE v⟫_ℝ = 0 := by
  simp [inlE, inrE, PiLp.inner_apply, Fintype.sum_sum_type]

@[simp] lemma inner_inrE_inlE (u : EuclideanSpace ℝ m) (v : EuclideanSpace ℝ n) :
    ⟪(inrE v : EuclideanSpace ℝ (m ⊕ n)), inlE u⟫_ℝ = 0 := by
  rw [real_inner_comm]; exact inner_inlE_inrE u v

lemma norm_inlE (u : EuclideanSpace ℝ m) : ‖(inlE u : EuclideanSpace ℝ (m ⊕ n))‖ = ‖u‖ := by
  rw [norm_eq_sqrt_real_inner, inner_inlE_inlE, ← norm_eq_sqrt_real_inner]

lemma norm_inrE (v : EuclideanSpace ℝ n) : ‖(inrE v : EuclideanSpace ℝ (m ⊕ n))‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, inner_inrE_inrE, ← norm_eq_sqrt_real_inner]

end Inner

/-! ### The free Dirac matrix -/

section Matrix

variable [DecidableEq m] [DecidableEq n]

/-- `H₀ = [[c² I, c K], [c Kᵀ, −c² I]]`. -/
def diracMatrix (c : ℝ) (K : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks (c ^ 2 • (1 : Matrix m m ℝ)) (c • K) (c • Kᵀ) (-(c ^ 2) • (1 : Matrix n n ℝ))

lemma diracMatrix_isHermitian (c : ℝ) (K : Matrix m n ℝ) : (diracMatrix c K).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · simp [Matrix.IsHermitian]
  · simp
  · simp [Matrix.IsHermitian]

variable [Fintype m] [Fintype n]

/-- `H₀` as an operator on the Euclidean space `ℝ^(m ⊕ n)`. -/
noncomputable def diracOp (c : ℝ) (K : Matrix m n ℝ) :
    EuclideanSpace ℝ (m ⊕ n) →ₗ[ℝ] EuclideanSpace ℝ (m ⊕ n) :=
  Matrix.toEuclideanLin (diracMatrix c K)

lemma diracOp_apply (c : ℝ) (K : Matrix m n ℝ) (x : EuclideanSpace ℝ (m ⊕ n)) :
    diracOp c K x = toLp 2 (diracMatrix c K *ᵥ ofLp x) := rfl

lemma diracOp_isSymmetric (c : ℝ) (K : Matrix m n ℝ) : (diracOp c K).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (diracMatrix_isHermitian c K)

/-- `H₀ (x₁, x₂) = (c² x₁ + c K x₂, c Kᵀ x₁ − c² x₂)`. -/
lemma ofLp_diracOp (c : ℝ) (K : Matrix m n ℝ) (x : EuclideanSpace ℝ (m ⊕ n)) :
    ofLp (diracOp c K x) =
      Sum.elim (c ^ 2 • (fun i => x (Sum.inl i)) + c • (K *ᵥ fun j => x (Sum.inr j)))
        (c • (Kᵀ *ᵥ fun i => x (Sum.inl i)) - c ^ 2 • (fun j => x (Sum.inr j))) := by
  rw [diracOp_apply, WithLp.ofLp_toLp, diracMatrix, Matrix.fromBlocks_mulVec]
  simp only [neg_smul, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_add_neg]
  rfl

@[simp] lemma diracOp_inl (c : ℝ) (K : Matrix m n ℝ) (x : EuclideanSpace ℝ (m ⊕ n)) (i : m) :
    diracOp c K x (Sum.inl i) = c ^ 2 * x (Sum.inl i) + c * (K *ᵥ fun j => x (Sum.inr j)) i := by
  show ofLp (diracOp c K x) (Sum.inl i) = _
  rw [ofLp_diracOp]; rfl

@[simp] lemma diracOp_inr (c : ℝ) (K : Matrix m n ℝ) (x : EuclideanSpace ℝ (m ⊕ n)) (j : n) :
    diracOp c K x (Sum.inr j) = c * (Kᵀ *ᵥ fun i => x (Sum.inl i)) j - c ^ 2 * x (Sum.inr j) := by
  show ofLp (diracOp c K x) (Sum.inr j) = _
  rw [ofLp_diracOp]; rfl

/-- `H₀ (u, 0) = (c² u, c Kᵀ u)`, so `H₀ (u, 0) = c² (u,0) + cσ (0,v)` when
`Kᵀ u = σ v`. -/
lemma diracOp_inlE (c σ : ℝ) (K : Matrix m n ℝ) (u : EuclideanSpace ℝ m)
    (v : EuclideanSpace ℝ n) (hKu : Kᵀ *ᵥ ofLp u = σ • ofLp v) :
    diracOp c K (inlE u) = c ^ 2 • inlE u + (c * σ) • inrE v := by
  ext i
  rcases i with i | j
  · rw [diracOp_inl, inlE_comp_inr, Matrix.mulVec_zero]
    simp [inlE, inrE]
  · rw [diracOp_inr, inlE_comp_inl, hKu]
    simp [inlE, inrE]
    ring

/-- `H₀ (0, v) = (c K v, −c² v)`, so `H₀ (0, v) = cσ (u,0) − c² (0,v)` when
`K v = σ u`. -/
lemma diracOp_inrE (c σ : ℝ) (K : Matrix m n ℝ) (u : EuclideanSpace ℝ m)
    (v : EuclideanSpace ℝ n) (hKv : K *ᵥ ofLp v = σ • ofLp u) :
    diracOp c K (inrE v) = (c * σ) • inlE u - c ^ 2 • inrE v := by
  ext i
  rcases i with i | j
  · rw [diracOp_inl, inrE_comp_inr, hKv]
    simp [inlE, inrE]
    ring
  · rw [diracOp_inr, inrE_comp_inl, Matrix.mulVec_zero]
    simp [inlE, inrE]

/-- **Proposition 2.1 (fiber decomposition).** A singular triple
`K v = σ u`, `Kᵀ u = σ v` with unit `u, v` gives the Dirac fiber
`((u,0), (0,v))` of `H₀`, with parameter `t = σ/(2c)`: `H₀` acts on it as
`h(σ) = [[c², cσ], [cσ, −c²]]`. -/
theorem dirac_isDiracFiber {c : ℝ} (hc : c ≠ 0) (K : Matrix m n ℝ) {σ : ℝ}
    {u : EuclideanSpace ℝ m} {v : EuclideanSpace ℝ n} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hKv : K *ᵥ ofLp v = σ • ofLp u) (hKu : Kᵀ *ᵥ ofLp u = σ • ofLp v) :
    IsDiracFiber (diracOp c K) c (σ / (2 * c)) (inlE u) (inrE v) := by
  have hcσ : c * σ = 2 * c ^ 2 * (σ / (2 * c)) := by field_simp
  exact
    { norm_e₁ := by rw [norm_inlE, hu]
      norm_e₂ := by rw [norm_inrE, hv]
      inner_e₁_e₂ := inner_inlE_inrE u v
      apply_e₁ := by rw [diracOp_inlE c σ K u v hKu, hcσ]
      apply_e₂ := by rw [diracOp_inrE c σ K u v hKv, hcσ] }

omit [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] in
/-- Proposition 2.1, eigenvalues: `E(σ) = c²√(1+4t²) = √(c⁴ + c²σ²)` for
`t = σ/(2c)`, `c > 0`. -/
theorem energy_eq {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    c ^ 2 * wt (σ / (2 * c)) = Real.sqrt (c ^ 4 + c ^ 2 * σ ^ 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have h1 : (0 : ℝ) ≤ 1 + 4 * (σ / (2 * c)) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  rw [show c ^ 4 + c ^ 2 * σ ^ 2 = (c ^ 2) ^ 2 * (1 + 4 * (σ / (2 * c)) ^ 2) by
      field_simp; ring,
    Real.sqrt_mul' _ h1, Real.sqrt_sq h2]
  rfl

/-! ### The spectral gap of `H₀` -/

/-- `‖H₀ x‖² = c⁴ ‖x‖² + c² (‖K x₂‖² + ‖Kᵀ x₁‖²)` for `x = (x₁, x₂)`: the
cross terms cancel because `⟪x₁, K x₂⟫ = ⟪Kᵀ x₁, x₂⟫`. -/
theorem norm_diracOp_sq (c : ℝ) (K : Matrix m n ℝ) (x : EuclideanSpace ℝ (m ⊕ n)) :
    ‖diracOp c K x‖ ^ 2 = c ^ 4 * ‖x‖ ^ 2 +
      c ^ 2 * (∑ i, (K *ᵥ (fun j => x (Sum.inr j))) i ^ 2 +
        ∑ j, (Kᵀ *ᵥ (fun i => x (Sum.inl i))) j ^ 2) := by
  set x₁ : m → ℝ := fun i => x (Sum.inl i) with hx₁
  set x₂ : n → ℝ := fun j => x (Sum.inr j) with hx₂
  have hcross : x₁ ⬝ᵥ (K *ᵥ x₂) = (Kᵀ *ᵥ x₁) ⬝ᵥ x₂ := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hn : ∀ y : EuclideanSpace ℝ (m ⊕ n), ‖y‖ ^ 2 =
      ∑ i, y (Sum.inl i) ^ 2 + ∑ j, y (Sum.inr j) ^ 2 := fun y => by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  rw [hn, hn]
  simp only [diracOp_inl, diracOp_inr]
  simp only [dotProduct] at hcross
  have e1 : ∑ i, (c ^ 2 * x₁ i + c * (K *ᵥ x₂) i) ^ 2 = c ^ 4 * ∑ i, x₁ i ^ 2 +
      2 * c ^ 3 * ∑ i, x₁ i * (K *ᵥ x₂) i + c ^ 2 * ∑ i, (K *ᵥ x₂) i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j, (c * (Kᵀ *ᵥ x₁) j - c ^ 2 * x₂ j) ^ 2 = c ^ 2 * ∑ j, (Kᵀ *ᵥ x₁) j ^ 2 -
      2 * c ^ 3 * ∑ j, (Kᵀ *ᵥ x₁) j * x₂ j + c ^ 4 * ∑ j, x₂ j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  linear_combination (2 * c ^ 3) * hcross

/-- The free spectral gap: `‖H₀ x‖ ≥ c² ‖x‖`. -/
theorem sq_mul_norm_le_norm_diracOp (c : ℝ) (K : Matrix m n ℝ) (x : EuclideanSpace ℝ (m ⊕ n)) :
    c ^ 2 * ‖x‖ ≤ ‖diracOp c K x‖ := by
  have h := norm_diracOp_sq c K x
  have hnn : 0 ≤ c ^ 2 * (∑ i, (K *ᵥ (fun j => x (Sum.inr j))) i ^ 2 +
      ∑ j, (Kᵀ *ᵥ (fun i => x (Sum.inl i))) j ^ 2) := by positivity
  have h0 : 0 ≤ c ^ 2 * ‖x‖ := mul_nonneg (sq_nonneg c) (norm_nonneg x)
  rw [← sq_le_sq₀ h0 (norm_nonneg _), mul_pow, h]
  nlinarith

/-- **No free eigenvalue in the gap.** Every eigenvalue `μ` of `H₀`
satisfies `|μ| ≥ c²`, so `spec(H₀) ∩ (−c², c²) = ∅`. -/
theorem diracOp_eigenvalue_abs_ge (c : ℝ) (K : Matrix m n ℝ) {x : EuclideanSpace ℝ (m ⊕ n)}
    {μ : ℝ} (hx : x ≠ 0) (hμ : diracOp c K x = μ • x) : c ^ 2 ≤ |μ| := by
  have h := sq_mul_norm_le_norm_diracOp c K x
  rw [hμ, norm_smul, Real.norm_eq_abs] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hx)

/-! ### A family of singular triples and its fibers -/

section Fibers

variable {ι : Type*} [Fintype ι]

/-- The fiber `W j = span{(u j, 0), (0, v j)}`. -/
def diracFiber (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n) (j : ι) :
    Submodule ℝ (EuclideanSpace ℝ (m ⊕ n)) :=
  Submodule.span ℝ {inlE (u j), inrE (v j)}

omit [DecidableEq m] [DecidableEq n] [Fintype ι] in
/-- Distinct fibers are orthogonal. -/
theorem dirac_fiber_isOrtho {u : ι → EuclideanSpace ℝ m} {v : ι → EuclideanSpace ℝ n}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    Pairwise fun j k => diracFiber u v j ⟂ diracFiber u v k := by
  intro j k hjk
  rw [diracFiber, diracFiber, Submodule.isOrtho_span]
  rintro x (rfl | rfl) y (rfl | rfl) <;>
    simp [hu.2 hjk, hv.2 hjk]

/-- Fiber parameter `t j = σ j/(2c)`. -/
noncomputable def fiberParam (c : ℝ) (σ : ι → ℝ) (j : ι) : ℝ := σ j / (2 * c)

/-- The normalized trial vector of family `f` in fiber `j`. -/
noncomputable def diracTrial (c : ℝ) (f : Family) (σ : ι → ℝ) (u : ι → EuclideanSpace ℝ m)
    (v : ι → EuclideanSpace ℝ n) (j : ι) : EuclideanSpace ℝ (m ⊕ n) :=
  trialUnit f (fiberParam c σ j) (inlE (u j)) (inrE (v j))

/-- The single-family trial space `V = span{b j}`. -/
noncomputable def trialSpace (c : ℝ) (f : Family) (σ : ι → ℝ) (u : ι → EuclideanSpace ℝ m)
    (v : ι → EuclideanSpace ℝ n) : Submodule ℝ (EuclideanSpace ℝ (m ⊕ n)) :=
  Submodule.span ℝ (Set.range (diracTrial c f σ u v))

/-- Hypotheses: `(σ j, u j, v j)` is a family of singular triples of `K`. -/
structure SingularSystem (K : Matrix m n ℝ) (σ : ι → ℝ) (u : ι → EuclideanSpace ℝ m)
    (v : ι → EuclideanSpace ℝ n) : Prop where
  orthonormal_u : Orthonormal ℝ u
  orthonormal_v : Orthonormal ℝ v
  nonneg : ∀ j, 0 ≤ σ j
  mulVec_v : ∀ j, K *ᵥ ofLp (v j) = σ j • ofLp (u j)
  mulVec_u : ∀ j, Kᵀ *ᵥ ofLp (u j) = σ j • ofLp (v j)

variable {c : ℝ} {K : Matrix m n ℝ} {σ : ι → ℝ} {u : ι → EuclideanSpace ℝ m}
  {v : ι → EuclideanSpace ℝ n}

omit [Fintype ι] in
lemma SingularSystem.isDiracFiber (hS : SingularSystem K σ u v) (hc : c ≠ 0) (j : ι) :
    IsDiracFiber (diracOp c K) c (fiberParam c σ j) (inlE (u j)) (inrE (v j)) :=
  dirac_isDiracFiber hc K (hS.orthonormal_u.1 j) (hS.orthonormal_v.1 j) (hS.mulVec_v j)
    (hS.mulVec_u j)

omit [DecidableEq m] [DecidableEq n] [Fintype ι] in
lemma SingularSystem.fiberParam_nonneg (hS : SingularSystem K σ u v) (hc : 0 < c) (j : ι) :
    0 ≤ fiberParam c σ j :=
  div_nonneg (hS.nonneg j) (by linarith)

omit [Fintype ι] in
/-- **Theorem 3.1 for `H₀`.** In every fiber, the leakage of the trial
direction of family `f`, measured with the spectral projectors of `H₀`,
is the closed form `f.leak (σ j/(2c))`. -/
theorem dirac_leakage (hS : SingularSystem K σ u v) (hc : 0 < c) (f : Family) (j : ι) :
    leakage (diracOp c K) f (trialDir f (fiberParam c σ j) (inlE (u j)) (inrE (v j))) =
      f.leak (fiberParam c σ j) :=
  (hS.isDiracFiber hc.ne' j).leakage_trialDir (diracOp_isSymmetric c K) hc.ne'
    (hS.fiberParam_nonneg hc j) f

/-- **Theorem 4.1 for `H₀`, with `Λ₊` (exact global conformity defect).**
For the single-family trial space `V = span{b j}` of family `f` and its
orthogonal projector `Π`:
`‖(I − Π) Λ₊ Π‖ = max_j ℓ_f(t j) √(1 − ℓ_f(t j)²)`. -/
theorem dirac_global_defect_pos [Nonempty ι] (hS : SingularSystem K σ u v) (hc : 0 < c)
    (f : Family) :
    ‖(1 - (trialSpace c f σ u v).starProjection) * specProjPos (diracOp c K) *
        (trialSpace c f σ u v).starProjection‖ =
      Finset.univ.sup' Finset.univ_nonempty (fun j =>
        f.leak (fiberParam c σ j) * Real.sqrt (1 - f.leak (fiberParam c σ j) ^ 2)) := by
  have hT := diracOp_isSymmetric c K
  have key := global_defect (posSpectralSubspace (diracOp c K)) (diracFiber u v)
    (dirac_fiber_isOrtho hS.orthonormal_u hS.orthonormal_v)
    (fun j _ hx => (hS.isDiracFiber hc.ne' j).specProjPos_mem_span hT hc.ne' hx)
    (diracTrial c f σ u v) (fun j => trialUnit_mem_span _ _ _ _)
    (fun j => (hS.isDiracFiber hc.ne' j).norm_trialUnit f)
  rw [trialSpace, specProjPos, key]
  exact Finset.sup'_congr _ rfl fun j _ =>
    (hS.isDiracFiber hc.ne' j).defect_factor_pos hT hc.ne' (hS.fiberParam_nonneg hc j) f

/-- **Theorem 4.1 for `H₀`, with `Λ₋`.** Same value as with `Λ₊`. -/
theorem dirac_global_defect_neg [Nonempty ι] (hS : SingularSystem K σ u v) (hc : 0 < c)
    (f : Family) :
    ‖(1 - (trialSpace c f σ u v).starProjection) * specProjNeg (diracOp c K) *
        (trialSpace c f σ u v).starProjection‖ =
      Finset.univ.sup' Finset.univ_nonempty (fun j =>
        f.leak (fiberParam c σ j) * Real.sqrt (1 - f.leak (fiberParam c σ j) ^ 2)) := by
  have hT := diracOp_isSymmetric c K
  have key := global_defect (negSpectralSubspace (diracOp c K)) (diracFiber u v)
    (dirac_fiber_isOrtho hS.orthonormal_u hS.orthonormal_v)
    (fun j _ hx => (hS.isDiracFiber hc.ne' j).specProjNeg_mem_span hT hc.ne' hx)
    (diracTrial c f σ u v) (fun j => trialUnit_mem_span _ _ _ _)
    (fun j => (hS.isDiracFiber hc.ne' j).norm_trialUnit f)
  rw [trialSpace, specProjNeg, key]
  exact Finset.sup'_congr _ rfl fun j _ =>
    (hS.isDiracFiber hc.ne' j).defect_factor_neg hT hc.ne' (hS.fiberParam_nonneg hc j) f

/-! ### Corollary 4.2: the dual-kinetic-balance pair space -/

/-- The dual-kinetic-balance (DKB) pair space: in every fiber, both the
balanced and the positronic trial direction. -/
noncomputable def dkbSpace (c : ℝ) (σ : ι → ℝ) (u : ι → EuclideanSpace ℝ m)
    (v : ι → EuclideanSpace ℝ n) : Submodule ℝ (EuclideanSpace ℝ (m ⊕ n)) :=
  Submodule.span ℝ (⋃ j, {trialDir Family.bal (fiberParam c σ j) (inlE (u j)) (inrE (v j)),
    trialDir Family.pos (fiberParam c σ j) (inlE (u j)) (inrE (v j))})

omit [DecidableEq m] [DecidableEq n] [Fintype ι] in
/-- Each fiber lies in the DKB pair space: `e₁ = (u_bal − t u_pos)/(1+t²)`
and `e₂ = (t u_bal + u_pos)/(1+t²)`. -/
lemma diracFiber_le_dkbSpace (j : ι) : diracFiber u v j ≤ dkbSpace c σ u v := by
  set t := fiberParam c σ j
  have hb : trialDir Family.bal t (inlE (u j)) (inrE (v j)) ∈ dkbSpace c σ u v :=
    Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, Set.mem_insert _ _⟩)
  have hp : trialDir Family.pos t (inlE (u j)) (inrE (v j)) ∈ dkbSpace c σ u v :=
    Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, Set.mem_insert_of_mem _ rfl⟩)
  have ht : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  rw [diracFiber, Submodule.span_le]
  rintro x (rfl | rfl)
  · have : (inlE (u j) : EuclideanSpace ℝ (m ⊕ n)) = (1 + t ^ 2)⁻¹ •
        (trialDir Family.bal t (inlE (u j)) (inrE (v j)) -
          t • trialDir Family.pos t (inlE (u j)) (inrE (v j))) := by
      simp only [trialDir, Family.coeffs, fv]
      match_scalars <;> field_simp <;> ring
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hb (Submodule.smul_mem _ _ hp))
  · have : (inrE (v j) : EuclideanSpace ℝ (m ⊕ n)) = (1 + t ^ 2)⁻¹ •
        (t • trialDir Family.bal t (inlE (u j)) (inrE (v j)) +
          trialDir Family.pos t (inlE (u j)) (inrE (v j))) := by
      simp only [trialDir, Family.coeffs, fv]
      match_scalars <;> field_simp <;> ring
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hb) hp)

omit [DecidableEq m] [DecidableEq n] [Fintype ι] in
/-- The DKB pair space is invariant under any operator that maps every
fiber into itself. -/
lemma dkbSpace_invariant (P : EuclideanSpace ℝ (m ⊕ n) →ₗ[ℝ] EuclideanSpace ℝ (m ⊕ n))
    (hP : ∀ j, ∀ x ∈ diracFiber u v j, P x ∈ diracFiber u v j) :
    ∀ x ∈ dkbSpace (c := c) (σ := σ) u v, P x ∈ dkbSpace c σ u v := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    have hyW : y ∈ diracFiber u v j := by
      rcases hj with rfl | rfl
      · exact trialDir_mem_span _ _ _ _
      · exact trialDir_mem_span _ _ _ _
    exact diracFiber_le_dkbSpace j (hP j y hyW)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

omit [Fintype ι] in
/-- **Corollary 4.2, with `Λ₊`.** The DKB pair space has zero conformity
defect: `(I − Π) Λ₊ Π = 0`. -/
theorem dirac_dkb_defect_pos (hS : SingularSystem K σ u v) (hc : 0 < c) :
    (1 - (dkbSpace c σ u v).starProjection) * specProjPos (diracOp c K) *
      (dkbSpace c σ u v).starProjection = 0 :=
  defect_eq_zero_of_invariant _ _ (dkbSpace_invariant (specProjPos (diracOp c K)).toLinearMap
    fun j _ hx => (hS.isDiracFiber hc.ne' j).specProjPos_mem_span
      (diracOp_isSymmetric c K) hc.ne' hx)

omit [Fintype ι] in
/-- **Corollary 4.2, with `Λ₋`.** -/
theorem dirac_dkb_defect_neg (hS : SingularSystem K σ u v) (hc : 0 < c) :
    (1 - (dkbSpace c σ u v).starProjection) * specProjNeg (diracOp c K) *
      (dkbSpace c σ u v).starProjection = 0 :=
  defect_eq_zero_of_invariant _ _ (dkbSpace_invariant (specProjNeg (diracOp c K)).toLinearMap
    fun j _ hx => (hS.isDiracFiber hc.ne' j).specProjNeg_mem_span
      (diracOp_isSymmetric c K) hc.ne' hx)

/-! ### Theorem 5.1(a), Galerkin form -/

/-- **Theorem 5.1(a), Galerkin form.** Each trial vector `b j` of the
single-family space is an eigenvector of the Galerkin compression `Π H₀`,
with eigenvalue the fiber Rayleigh value `R_f(t j)` of Eq. (rayleigh). -/
theorem dirac_galerkin_eigen (hS : SingularSystem K σ u v) (hc : 0 < c) (f : Family) (j : ι) :
    (trialSpace c f σ u v).starProjection (diracOp c K (diracTrial c f σ u v j)) =
      f.rayleigh c (fiberParam c σ j) • diracTrial c f σ u v j := by
  classical
  have hW := dirac_fiber_isOrtho hS.orthonormal_u hS.orthonormal_v
  have hbW : ∀ k, diracTrial c f σ u v k ∈ diracFiber u v k := fun k =>
    trialUnit_mem_span _ _ _ _
  have hon : Orthonormal ℝ (diracTrial c f σ u v) :=
    ⟨fun k => (hS.isDiracFiber hc.ne' k).norm_trialUnit f,
      fun k l hkl => (hW hkl).inner_eq (hbW k) (hbW l)⟩
  have hHW : diracOp c K (diracTrial c f σ u v j) ∈ diracFiber u v j :=
    (hS.isDiracFiber hc.ne' j).apply_mem_span (hbW j)
  rw [trialSpace, starProjection_span_orthonormal hon, Finset.sum_eq_single j]
  · rw [real_inner_comm, diracTrial, (hS.isDiracFiber hc.ne' j).rayleigh_trialUnit f]
  · intro k _ hkj
    rw [(hW hkj).inner_eq (hbW k) hHW, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Theorem 5.1(a), pollution by the anti-balanced family.** The Galerkin
eigenvalue `R_anti(t j)` carried by the anti-balanced trial vector `b j`
lies strictly inside the spectral gap `(−c², c²)` iff
`0 < t j² < 1/2`. -/
theorem dirac_anti_galerkin_in_gap (hS : SingularSystem K σ u v) (hc : 0 < c) (j : ι) :
    (trialSpace c Family.anti σ u v).starProjection
        (diracOp c K (diracTrial c Family.anti σ u v j)) =
      Family.anti.rayleigh c (fiberParam c σ j) • diracTrial c Family.anti σ u v j ∧
    ((-c ^ 2 < Family.anti.rayleigh c (fiberParam c σ j) ∧
        Family.anti.rayleigh c (fiberParam c σ j) < c ^ 2) ↔
      (0 < fiberParam c σ j ^ 2 ∧ fiberParam c σ j ^ 2 < 1 / 2)) :=
  ⟨dirac_galerkin_eigen hS hc Family.anti j, FeastLemmas.anti_in_gap c _ hc⟩

/-- **Spectral pollution, anti-balanced family.** If `0 < t j² < 1/2`, then
the anti-balanced Galerkin eigenvalue `R_anti(t j)` is *spurious*: it is
not an eigenvalue of `H₀`. (Every eigenvalue of `H₀` satisfies
`|μ| ≥ c²`, by `diracOp_eigenvalue_abs_ge`.) -/
theorem dirac_anti_galerkin_spurious (hS : SingularSystem K σ u v) (hc : 0 < c) (j : ι)
    (ht : 0 < fiberParam c σ j ^ 2) (ht' : fiberParam c σ j ^ 2 < 1 / 2) :
    (trialSpace c Family.anti σ u v).starProjection
        (diracOp c K (diracTrial c Family.anti σ u v j)) =
      Family.anti.rayleigh c (fiberParam c σ j) • diracTrial c Family.anti σ u v j ∧
    ∀ y : EuclideanSpace ℝ (m ⊕ n), y ≠ 0 →
      diracOp c K y ≠ Family.anti.rayleigh c (fiberParam c σ j) • y := by
  obtain ⟨hgal, hgap⟩ := dirac_anti_galerkin_in_gap hS hc j
  refine ⟨hgal, fun y hy hEig => ?_⟩
  obtain ⟨hlo, hhi⟩ := hgap.mpr ⟨ht, ht'⟩
  exact absurd (diracOp_eigenvalue_abs_ge c K hy hEig) (not_le.mpr (abs_lt.mpr ⟨hlo, hhi⟩))

/-- **Theorem 5.1(a), balanced family.** The Galerkin eigenvalue
`R_bal(t j)` carried by the balanced trial vector never lies in the gap:
`R_bal(t j) ≥ c²`. -/
theorem dirac_bal_galerkin_above_gap (hS : SingularSystem K σ u v) (hc : 0 < c) (j : ι) :
    (trialSpace c Family.bal σ u v).starProjection
        (diracOp c K (diracTrial c Family.bal σ u v j)) =
      Family.bal.rayleigh c (fiberParam c σ j) • diracTrial c Family.bal σ u v j ∧
    c ^ 2 ≤ Family.bal.rayleigh c (fiberParam c σ j) :=
  ⟨dirac_galerkin_eigen hS hc Family.bal j,
    sub_nonneg.mp (FeastLemmas.bal_above_gap_nonneg c _)⟩

end Fibers

end Matrix

end KineticBalance
