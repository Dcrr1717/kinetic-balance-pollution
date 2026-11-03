/-
Completeness of the fiber decomposition of the free Dirac matrix
(Proposition 2.1 of the paper, the part not covered by `DiracMatrix.lean`).

For a *complete* singular system of `K` (positive singular values; the
singular vectors together with the kernels span both spaces), the space
`ℝ^(m ⊕ n)` splits as an orthogonal internal direct sum of `H₀`-invariant
blocks:

  ℝ^(m ⊕ n) = (⨁_j W_j) ⊕ (ker Kᵀ ⊕ 0) ⊕ (0 ⊕ ker K),
  W_j = span{(u_j, 0), (0, v_j)}.

On `W_j`, `H₀` is the 2×2 matrix `h(σ_j)` (`dirac_isDiracFiber`). On the two
kernel blocks, `H₀ = +c²` and `H₀ = −c²`. The spectral projectors `Λ±` are
block diagonal, and such a complete singular system always exists (the SVD).

Main results (namespace `KineticBalance`):

* `diracBlock_orthogonalFamily`: the blocks are mutually orthogonal;
* `diracBlock_iSup_eq_top`: the blocks span `ℝ^(m ⊕ n)`;
* `diracBlock_isInternal`: together, an internal direct sum decomposition;
* `diracBlock_invariant`, `diracOp_inlE_of_ker`, `diracOp_inrE_of_ker`:
  every block is `H₀`-invariant, and `H₀ = ±c²` on the kernel blocks;
* `diracBlock_specProjPos_invariant`, `diracBlock_specProjNeg_invariant`,
  `specProj_inlE_of_ker`, `specProj_inrE_of_ker`: `Λ±` are block diagonal;
* `dirac_specProjPos_add_specProjNeg`: `Λ₊ + Λ₋ = I` for `c ≠ 0`;
* `exists_completeSingularSystem`: every real matrix has a complete singular
  system (from `exists_singularSystem` in `SVD.lean`);
* `exists_dirac_block_decomposition`: the unconditional statement.
-/

import KineticBalance.DiracMatrix
import KineticBalance.SVD

open scoped InnerProductSpace
open Matrix WithLp

namespace KineticBalance

variable {m n : Type*}

/-! ### Embeddings as linear maps -/

/-- `inlE` as a linear map `u ↦ (u, 0)`. -/
def inlLin : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ (m ⊕ n) where
  toFun := inlE
  map_add' x y := by ext (i | j) <;> simp [inlE]
  map_smul' r x := by ext (i | j) <;> simp [inlE]

/-- `inrE` as a linear map `v ↦ (0, v)`. -/
def inrLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ (m ⊕ n) where
  toFun := inrE
  map_add' x y := by ext (i | j) <;> simp [inrE]
  map_smul' r x := by ext (i | j) <;> simp [inrE]

lemma inlLin_apply (x : EuclideanSpace ℝ m) : (inlLin x : EuclideanSpace ℝ (m ⊕ n)) = inlE x :=
  rfl

lemma inrLin_apply (x : EuclideanSpace ℝ n) : (inrLin x : EuclideanSpace ℝ (m ⊕ n)) = inrE x :=
  rfl

/-- Every vector splits into its upper and lower components: `x = (x₁, 0) + (0, x₂)`. -/
lemma inlE_add_inrE (x : EuclideanSpace ℝ (m ⊕ n)) :
    inlE (toLp 2 fun i => x (Sum.inl i)) + inrE (toLp 2 fun j => x (Sum.inr j)) = x := by
  ext (i | j) <;> simp [inlE, inrE]

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Over `ℝ`, the transpose is the adjoint: `toEuclideanLin Kᵀ = (toEuclideanLin K)†`. -/
lemma toEuclideanLin_transpose_eq_adjoint (K : Matrix m n ℝ) :
    Matrix.toEuclideanLin Kᵀ = LinearMap.adjoint (Matrix.toEuclideanLin K) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]

variable {ι : Type*} {K : Matrix m n ℝ} {σ : ι → ℝ} {u : ι → EuclideanSpace ℝ m}
  {v : ι → EuclideanSpace ℝ n}

omit [DecidableEq m] in
lemma SingularSystem.toEuclideanLin_v (hS : SingularSystem K σ u v) (j : ι) :
    Matrix.toEuclideanLin K (v j) = σ j • u j :=
  WithLp.ofLp_injective 2 (by rw [WithLp.ofLp_smul]; exact hS.mulVec_v j)

omit [DecidableEq n] in
lemma SingularSystem.toEuclideanLin_u (hS : SingularSystem K σ u v) (j : ι) :
    Matrix.toEuclideanLin Kᵀ (u j) = σ j • v j :=
  WithLp.ofLp_injective 2 (by rw [WithLp.ofLp_smul]; exact hS.mulVec_u j)

/-- `⟪z, u j⟫ = 0` for `z ∈ ker Kᵀ` (the left singular vectors span `range K`). -/
lemma SingularSystem.inner_ker_transpose (hS : SingularSystem K σ u v) (hσ : σ j ≠ 0)
    {z : EuclideanSpace ℝ m} (hz : z ∈ LinearMap.ker (Matrix.toEuclideanLin Kᵀ)) :
    ⟪z, u j⟫_ℝ = 0 := by
  have h : ⟪z, Matrix.toEuclideanLin K (v j)⟫_ℝ = 0 := by
    rw [← LinearMap.adjoint_inner_left, ← toEuclideanLin_transpose_eq_adjoint,
      LinearMap.mem_ker.mp hz, inner_zero_left]
  rw [hS.toEuclideanLin_v, real_inner_smul_right] at h
  exact (mul_eq_zero.mp h).resolve_left hσ

lemma SingularSystem.inner_ker (hS : SingularSystem K σ u v) (hσ : σ j ≠ 0)
    {z : EuclideanSpace ℝ n} (hz : z ∈ LinearMap.ker (Matrix.toEuclideanLin K)) :
    ⟪z, v j⟫_ℝ = 0 := by
  have h : ⟪z, Matrix.toEuclideanLin Kᵀ (u j)⟫_ℝ = 0 := by
    rw [toEuclideanLin_transpose_eq_adjoint, LinearMap.adjoint_inner_right,
      LinearMap.mem_ker.mp hz, inner_zero_left]
  rw [hS.toEuclideanLin_u, real_inner_smul_right] at h
  exact (mul_eq_zero.mp h).resolve_left hσ

/-- A *complete* singular system of `K`: positive singular values, and the
singular vectors together with the kernels span both spaces,
`span{v_j} ⊕ ker K = ℝⁿ` and `span{u_j} ⊕ ker Kᵀ = ℝᵐ` (a compact SVD). -/
structure CompleteSingularSystem (K : Matrix m n ℝ) (σ : ι → ℝ) (u : ι → EuclideanSpace ℝ m)
    (v : ι → EuclideanSpace ℝ n) : Prop extends SingularSystem K σ u v where
  pos : ∀ j, 0 < σ j
  span_v_sup_ker : Submodule.span ℝ (Set.range v) ⊔ LinearMap.ker (Matrix.toEuclideanLin K) = ⊤
  span_u_sup_ker : Submodule.span ℝ (Set.range u) ⊔ LinearMap.ker (Matrix.toEuclideanLin Kᵀ) = ⊤

/-- The blocks of the fiber decomposition of `H₀`. -/
inductive DiracBlock (ι : Type*)
  | fiber (j : ι)
  | upper
  | lower
  deriving DecidableEq

/-- The block subspaces: the fibers `W j = span{(u j, 0), (0, v j)}`, the upper
kernel block `ker Kᵀ ⊕ 0` and the lower kernel block `0 ⊕ ker K`. -/
noncomputable def diracBlock (K : Matrix m n ℝ) (u : ι → EuclideanSpace ℝ m)
    (v : ι → EuclideanSpace ℝ n) : DiracBlock ι → Submodule ℝ (EuclideanSpace ℝ (m ⊕ n))
  | .fiber j => diracFiber u v j
  | .upper => (LinearMap.ker (Matrix.toEuclideanLin Kᵀ)).map inlLin
  | .lower => (LinearMap.ker (Matrix.toEuclideanLin K)).map inrLin

lemma fiber_isOrtho_upper (hS : CompleteSingularSystem K σ u v) (j : ι) :
    diracFiber u v j ⟂ diracBlock K u v .upper := by
  rw [diracFiber, Submodule.isOrtho_iff_le, Submodule.span_le]
  rintro g (rfl | rfl) <;> rw [SetLike.mem_coe, Submodule.mem_orthogonal'] <;>
    intro y hy <;> obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  · rw [inlLin_apply, inner_inlE_inlE, real_inner_comm]
    exact hS.inner_ker_transpose (hS.pos j).ne' hz
  · rw [inlLin_apply, real_inner_comm, inner_inlE_inrE]

lemma fiber_isOrtho_lower (hS : CompleteSingularSystem K σ u v) (j : ι) :
    diracFiber u v j ⟂ diracBlock K u v .lower := by
  rw [diracFiber, Submodule.isOrtho_iff_le, Submodule.span_le]
  rintro g (rfl | rfl) <;> rw [SetLike.mem_coe, Submodule.mem_orthogonal'] <;>
    intro y hy <;> obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  · rw [inrLin_apply, real_inner_comm, inner_inrE_inlE]
  · rw [inrLin_apply, inner_inrE_inrE, real_inner_comm]
    exact hS.inner_ker (hS.pos j).ne' hz

lemma upper_isOrtho_lower : diracBlock K u v .upper ⟂ diracBlock K u v .lower := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨z', -, rfl⟩ := Submodule.mem_map.mp hy
  exact inner_inlE_inrE z z'

/-- **Completeness of the fiber decomposition, orthogonality.** The blocks are
mutually orthogonal. -/
theorem diracBlock_orthogonalFamily (hS : CompleteSingularSystem K σ u v) :
    OrthogonalFamily ℝ (fun b => diracBlock K u v b) (fun b => (diracBlock K u v b).subtypeₗᵢ) := by
  refine OrthogonalFamily.of_pairwise ?_
  rintro (j | _ | _) (k | _ | _) hne
  · exact dirac_fiber_isOrtho hS.orthonormal_u hS.orthonormal_v (fun h => hne (by rw [h]))
  · exact fiber_isOrtho_upper hS j
  · exact fiber_isOrtho_lower hS j
  · exact (fiber_isOrtho_upper hS k).symm
  · exact absurd rfl hne
  · exact upper_isOrtho_lower
  · exact (fiber_isOrtho_lower hS k).symm
  · exact upper_isOrtho_lower.symm
  · exact absurd rfl hne

/-- **Completeness of the fiber decomposition, spanning.** The blocks span the
whole space `ℝ^(m ⊕ n)`. -/
theorem diracBlock_iSup_eq_top (hS : CompleteSingularSystem K σ u v) :
    ⨆ b, diracBlock K u v b = ⊤ := by
  set S := ⨆ b, diracBlock K u v b with hSdef
  have hup : Submodule.span ℝ (Set.range u) ⊔ LinearMap.ker (Matrix.toEuclideanLin Kᵀ) ≤
      S.comap inlLin := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact le_iSup (diracBlock K u v) (.fiber j) (Submodule.subset_span (Set.mem_insert _ _))
    · intro z hz
      exact le_iSup (diracBlock K u v) .upper (Submodule.mem_map_of_mem hz)
  have hlo : Submodule.span ℝ (Set.range v) ⊔ LinearMap.ker (Matrix.toEuclideanLin K) ≤
      S.comap inrLin := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact le_iSup (diracBlock K u v) (.fiber j)
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    · intro z hz
      exact le_iSup (diracBlock K u v) .lower (Submodule.mem_map_of_mem hz)
  rw [hS.span_u_sup_ker, top_le_iff] at hup
  rw [hS.span_v_sup_ker, top_le_iff] at hlo
  rw [eq_top_iff]
  intro x _
  rw [← inlE_add_inrE x]
  refine S.add_mem ?_ ?_
  · have : (toLp 2 fun i => x (Sum.inl i) : EuclideanSpace ℝ m) ∈ S.comap inlLin :=
      hup ▸ Submodule.mem_top
    exact this
  · have : (toLp 2 fun j => x (Sum.inr j) : EuclideanSpace ℝ n) ∈ S.comap inrLin :=
      hlo ▸ Submodule.mem_top
    exact this

/-- **Completeness of the fiber decomposition (Proposition 2.1).** The blocks form
an internal direct sum decomposition of `ℝ^(m ⊕ n)`. -/
theorem diracBlock_isInternal [DecidableEq ι] (hS : CompleteSingularSystem K σ u v) :
    DirectSum.IsInternal (diracBlock K u v) :=
  (diracBlock_orthogonalFamily hS).isInternal_iff.mpr
    (by rw [diracBlock_iSup_eq_top hS, Submodule.top_orthogonal_eq_bot])

/-! ### Invariance and the action of `H₀`, `Λ±` on the blocks -/

variable {c : ℝ}

/-- `H₀ (z, 0) = c² (z, 0)` for `z ∈ ker Kᵀ`. -/
lemma diracOp_inlE_of_ker {z : EuclideanSpace ℝ m}
    (hz : z ∈ LinearMap.ker (Matrix.toEuclideanLin Kᵀ)) :
    diracOp c K (inlE z) = c ^ 2 • inlE z := by
  have hz' : Kᵀ *ᵥ ofLp z = (0 : ℝ) • ofLp (0 : EuclideanSpace ℝ n) := by
    rw [zero_smul]; exact congrArg ofLp (LinearMap.mem_ker.mp hz)
  rw [diracOp_inlE c 0 K z 0 hz', mul_zero, zero_smul, add_zero]

/-- `H₀ (0, z) = −c² (0, z)` for `z ∈ ker K`. -/
lemma diracOp_inrE_of_ker {z : EuclideanSpace ℝ n}
    (hz : z ∈ LinearMap.ker (Matrix.toEuclideanLin K)) :
    diracOp c K (inrE z) = (-(c ^ 2)) • inrE z := by
  have hz' : K *ᵥ ofLp z = (0 : ℝ) • ofLp (0 : EuclideanSpace ℝ m) := by
    rw [zero_smul]; exact congrArg ofLp (LinearMap.mem_ker.mp hz)
  rw [diracOp_inrE c 0 K 0 z hz', mul_zero, zero_smul, zero_sub, neg_smul]

/-- Every block is invariant under `H₀`. -/
theorem diracBlock_invariant (hS : SingularSystem K σ u v) (b : DiracBlock ι) :
    ∀ x ∈ diracBlock K u v b, diracOp c K x ∈ diracBlock K u v b := by
  intro x hx
  rcases b with j | _ | _
  · obtain ⟨a, a', rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [map_add, map_smul, map_smul, diracOp_inlE c (σ j) K (u j) (v j) (hS.mulVec_u j),
      diracOp_inrE c (σ j) K (u j) (v j) (hS.mulVec_v j)]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    rw [inlLin_apply, diracOp_inlE_of_ker hz]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hz)
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    rw [inrLin_apply, diracOp_inrE_of_ker hz]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hz)

/-- On the upper kernel block `Λ₊ = I` and `Λ₋ = 0`. -/
lemma specProj_inlE_of_ker (hc : c ≠ 0) {z : EuclideanSpace ℝ m}
    (hz : z ∈ LinearMap.ker (Matrix.toEuclideanLin Kᵀ)) :
    specProjPos (diracOp c K) (inlE z) = inlE z ∧ specProjNeg (diracOp c K) (inlE z) = 0 :=
  have hc2 : 0 < c ^ 2 := by positivity
  ⟨specProjPos_apply_of_pos (diracOp_inlE_of_ker hz) hc2,
    specProjNeg_apply_of_nonneg (diracOp_isSymmetric c K) (diracOp_inlE_of_ker hz) hc2.le⟩

/-- On the lower kernel block `Λ₊ = 0` and `Λ₋ = I`. -/
lemma specProj_inrE_of_ker (hc : c ≠ 0) {z : EuclideanSpace ℝ n}
    (hz : z ∈ LinearMap.ker (Matrix.toEuclideanLin K)) :
    specProjPos (diracOp c K) (inrE z) = 0 ∧ specProjNeg (diracOp c K) (inrE z) = inrE z :=
  have hc2 : 0 < c ^ 2 := by positivity
  ⟨specProjPos_apply_of_nonpos (diracOp_isSymmetric c K) (diracOp_inrE_of_ker hz)
      (by linarith),
    specProjNeg_apply_of_neg (diracOp_inrE_of_ker hz) (by linarith)⟩

/-- `Λ₊` maps every block into itself: the spectral projectors are block
diagonal in the fiber decomposition. -/
theorem diracBlock_specProjPos_invariant (hS : SingularSystem K σ u v) (hc : c ≠ 0)
    (b : DiracBlock ι) :
    ∀ x ∈ diracBlock K u v b, specProjPos (diracOp c K) x ∈ diracBlock K u v b := by
  intro x hx
  rcases b with j | _ | _
  · exact (hS.isDiracFiber hc j).specProjPos_mem_span (diracOp_isSymmetric c K) hc hx
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    rw [inlLin_apply, (specProj_inlE_of_ker hc hz).1]
    exact Submodule.mem_map_of_mem hz
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    rw [inrLin_apply, (specProj_inrE_of_ker hc hz).1]
    exact Submodule.zero_mem _

/-- `Λ₋` maps every block into itself. -/
theorem diracBlock_specProjNeg_invariant (hS : SingularSystem K σ u v) (hc : c ≠ 0)
    (b : DiracBlock ι) :
    ∀ x ∈ diracBlock K u v b, specProjNeg (diracOp c K) x ∈ diracBlock K u v b := by
  intro x hx
  rcases b with j | _ | _
  · exact (hS.isDiracFiber hc j).specProjNeg_mem_span (diracOp_isSymmetric c K) hc hx
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    rw [inlLin_apply, (specProj_inlE_of_ker hc hz).2]
    exact Submodule.zero_mem _
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    rw [inrLin_apply, (specProj_inrE_of_ker hc hz).2]
    exact Submodule.mem_map_of_mem hz

/-- For `c ≠ 0`, `H₀` has no zero eigenvalue, so `Λ₊ + Λ₋ = I`. -/
theorem dirac_specProjPos_add_specProjNeg (hc : c ≠ 0) :
    specProjPos (diracOp c K) + specProjNeg (diracOp c K) = 1 := by
  refine specProjPos_add_specProjNeg (diracOp_isSymmetric c K) fun x hx => ?_
  have h := sq_mul_norm_le_norm_diracOp c K x
  rw [hx, norm_zero] at h
  have hc2 : 0 < c ^ 2 := by positivity
  exact norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg x]) (norm_nonneg x))

/-! ### Existence of a complete singular system (the SVD) -/

/-- **SVD of `K`.** Every real matrix `K` has a complete singular system. -/
theorem exists_completeSingularSystem (K : Matrix m n ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (σ : ι → ℝ)
      (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n),
      CompleteSingularSystem K σ u v := by
  obtain ⟨ι, hι, hdec, σ, u, v, hu, hv, hσ, hAv, hAu, hspv, hspu⟩ :=
    exists_singularSystem (Matrix.toEuclideanLin K)
  rw [← toEuclideanLin_transpose_eq_adjoint] at hAu hspu
  refine ⟨ι, hι, hdec, σ, u, v,
    { orthonormal_u := hu
      orthonormal_v := hv
      nonneg := fun j => (hσ j).le
      mulVec_v := fun j => ?_
      mulVec_u := fun j => ?_
      pos := hσ
      span_v_sup_ker := hspv
      span_u_sup_ker := hspu }⟩
  · rw [← WithLp.ofLp_smul, ← hAv j]; rfl
  · rw [← WithLp.ofLp_smul, ← hAu j]; rfl

/-- **Completeness of the fiber decomposition, unconditional form.** For every
real matrix `K` and every `c`, there is a complete singular system of `K` whose
fibers, together with `ker Kᵀ ⊕ 0` and `0 ⊕ ker K`, form an orthogonal
internal direct sum decomposition of `ℝ^(m ⊕ n)` into `H₀`-invariant blocks.
For `c ≠ 0` the blocks are also `Λ±`-invariant, each fiber is a Dirac fiber
with `t j = σ j/(2c)`, and `H₀ = ±c²` on the two kernel blocks. -/
theorem exists_dirac_block_decomposition (c : ℝ) (K : Matrix m n ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (σ : ι → ℝ)
      (u : ι → EuclideanSpace ℝ m) (v : ι → EuclideanSpace ℝ n),
      CompleteSingularSystem K σ u v ∧
      OrthogonalFamily ℝ (fun b => diracBlock K u v b)
        (fun b => (diracBlock K u v b).subtypeₗᵢ) ∧
      DirectSum.IsInternal (diracBlock K u v) ∧
      ∀ b, ∀ x ∈ diracBlock K u v b, diracOp c K x ∈ diracBlock K u v b := by
  obtain ⟨ι, hι, hdec, σ, u, v, hS⟩ := exists_completeSingularSystem K
  exact ⟨ι, hι, hdec, σ, u, v, hS, diracBlock_orthogonalFamily hS, diracBlock_isInternal hS,
    diracBlock_invariant hS.toSingularSystem⟩

end KineticBalance
