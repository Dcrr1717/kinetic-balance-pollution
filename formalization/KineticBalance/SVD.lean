/-
Existence of a complete singular system (a compact singular value
decomposition) for a linear map between finite-dimensional real
inner-product spaces.

The fiber analysis of the paper starts from an SVD of the kinetic block `K`.
The rest of the development takes a family of singular triples as an input
(`SingularSystem`). This file proves that a *complete* one always exists, so
that input is never vacuous.

* `exists_singularSystem`: for every `A : F →ₗ[ℝ] G` there are orthonormal
  `u j ∈ G`, orthonormal `v j ∈ F` and `σ j > 0` with `A v j = σ j u j`,
  `A† u j = σ j v j`, `span{v} ⊔ ker A = F` and `span{u} ⊔ ker A† = G`.

Proof: take an orthonormal eigenbasis `b i` of the symmetric operator `A† A`
(spectral theorem, `LinearMap.IsSymmetric.eigenvectorBasis`). Its eigenvalues
are `λ i = ‖A b i‖² ≥ 0`. Keep the indices with `λ i > 0` and set
`σ = √λ`, `v = b`, `u = σ⁻¹ A b`. Basis vectors with `λ i = 0` lie in `ker A`,
and every `A x` lies in `span{u}`, which gives the two completeness
statements.
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped InnerProductSpace

namespace KineticBalance

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- **SVD, abstract form.** Every linear map `A : F → G` between
finite-dimensional real inner-product spaces has a complete singular system:
orthonormal `u j`, orthonormal `v j`, `σ j > 0`, `A v j = σ j u j`,
`A† u j = σ j v j`, `span{v} ⊔ ker A = F` and `span{u} ⊔ ker A† = G`. -/
theorem exists_singularSystem (A : F →ₗ[ℝ] G) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (σ : ι → ℝ) (u : ι → G) (v : ι → F),
      Orthonormal ℝ u ∧ Orthonormal ℝ v ∧ (∀ j, 0 < σ j) ∧
      (∀ j, A (v j) = σ j • u j) ∧ (∀ j, LinearMap.adjoint A (u j) = σ j • v j) ∧
      Submodule.span ℝ (Set.range v) ⊔ LinearMap.ker A = ⊤ ∧
      Submodule.span ℝ (Set.range u) ⊔ LinearMap.ker (LinearMap.adjoint A) = ⊤ := by
  classical
  set T : F →ₗ[ℝ] F := LinearMap.adjoint A ∘ₗ A with hTdef
  have hT : T.IsSymmetric := LinearMap.isSymmetric_adjoint_comp_self A
  set b := hT.eigenvectorBasis rfl with hbdef
  set lam := hT.eigenvalues rfl with hlamdef
  have hTb : ∀ i, T (b i) = lam i • b i := fun i =>
    hT.apply_eigenvectorBasis rfl i
  -- ⟪A x, A y⟫ = ⟪x, T y⟫
  have hAA : ∀ x y, ⟪A x, A y⟫_ℝ = ⟪x, T y⟫_ℝ := fun x y => by
    rw [hTdef, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  have hAb : ∀ i j, ⟪A (b i), A (b j)⟫_ℝ = lam j * ⟪b i, b j⟫_ℝ := fun i j => by
    rw [hAA, hTb, real_inner_smul_right]
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => by
    have h := hAb i i
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h
    nlinarith [sq_nonneg ‖A (b i)‖]
  -- index set: the positive eigenvalues
  let ι := {i : Fin (Module.finrank ℝ F) // 0 < lam i}
  let σ : ι → ℝ := fun j => Real.sqrt (lam j.1)
  have hσ : ∀ j : ι, 0 < σ j := fun j => Real.sqrt_pos.mpr j.2
  have hσsq : ∀ j : ι, σ j ^ 2 = lam j.1 := fun j => Real.sq_sqrt (hlam0 j.1)
  let v : ι → F := fun j => b j.1
  let u : ι → G := fun j => (σ j)⁻¹ • A (b j.1)
  have hAv : ∀ j, A (v j) = σ j • u j := fun j => by
    simp only [u, v, smul_smul, mul_inv_cancel₀ (hσ j).ne', one_smul]
  have hAu : ∀ j, LinearMap.adjoint A (u j) = σ j • v j := fun j => by
    have h1 : LinearMap.adjoint A (A (b j.1)) = lam j.1 • b j.1 := hTb j.1
    simp only [u, v, map_smul, h1, smul_smul, ← hσsq j]
    congr 1
    field_simp [(hσ j).ne']
  have hv : Orthonormal ℝ v := b.orthonormal.comp _ Subtype.val_injective
  have hu : Orthonormal ℝ u := by
    refine ⟨fun j => ?_, fun j k hjk => ?_⟩
    · have h := hAb j.1 j.1
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, b.orthonormal.1 j.1,
        one_pow, mul_one, ← hσsq j] at h
      simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hσ j)]
      have hn : ‖A (b j.1)‖ = σ j := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (hσ j).le]; exact h
      rw [hn, inv_mul_cancel₀ (hσ j).ne']
    · have hne : j.1 ≠ k.1 := fun h => hjk (Subtype.ext h)
      simp only [u, real_inner_smul_left, real_inner_smul_right, hAb, b.orthonormal.2 hne,
        mul_zero]
  -- `A b i = 0` for a zero eigenvalue
  have hker : ∀ i, ¬ 0 < lam i → A (b i) = 0 := fun i hi => by
    have hl : lam i = 0 := le_antisymm (not_lt.mp hi) (hlam0 i)
    have h := hAb i i
    rw [hl, zero_mul] at h
    exact inner_self_eq_zero.mp h
  -- every `A x` lies in `span u`
  have hrange : ∀ x, A x ∈ Submodule.span ℝ (Set.range u) := fun x => by
    rw [← b.sum_repr' x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hi : 0 < lam i
    · have : A (b i) = σ ⟨i, hi⟩ • u ⟨i, hi⟩ := hAv ⟨i, hi⟩
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · rw [hker i hi]; exact Submodule.zero_mem _
  refine ⟨ι, inferInstance, inferInstance, σ, u, v, hu, hv, hσ, hAv, hAu, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [← b.sum_repr' x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    by_cases hi : 0 < lam i
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · exact Submodule.mem_sup_right (hker i hi)
  · rw [eq_top_iff]
    intro y _
    set S := Submodule.span ℝ (Set.range u)
    have hp : S.starProjection y ∈ S := S.starProjection_apply_mem y
    have hq : y - S.starProjection y ∈ LinearMap.ker (LinearMap.adjoint A) := by
      rw [LinearMap.mem_ker]
      set z := LinearMap.adjoint A (y - S.starProjection y)
      have h0 : ⟪z, z⟫_ℝ = 0 := by
        have horth := S.sub_starProjection_mem_orthogonal y
        calc ⟪z, z⟫_ℝ = ⟪y - S.starProjection y, A z⟫_ℝ := LinearMap.adjoint_inner_left A z _
          _ = 0 := (Submodule.mem_orthogonal' S _).mp horth _ (hrange z)
      exact inner_self_eq_zero.mp h0
    have : y = S.starProjection y + (y - S.starProjection y) := by abel
    rw [this]
    exact Submodule.add_mem_sup hp hq

end KineticBalance
