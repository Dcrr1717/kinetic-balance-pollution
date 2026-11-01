/-
Spectral projectors of a symmetric operator on a finite-dimensional real
inner-product space.

The paper writes `Λ₊` and `Λ₋` for the orthogonal projectors onto the
positive and negative spectral subspaces of the free Dirac matrix `H₀`.
This file defines them for an arbitrary symmetric operator `T`, from the
eigenspaces of `T` (no extra hypotheses), and proves the facts that the
fiber analysis uses:

* `specProjPos_apply_of_pos`, `specProjPos_apply_of_nonpos`: `Λ₊` fixes
  every eigenvector with a positive eigenvalue and kills every eigenvector
  with a nonpositive eigenvalue;
* `specProjNeg_apply_of_neg`, `specProjNeg_apply_of_nonneg`: the same for
  `Λ₋`;
* `specProjPos_add_specProjNeg`: if `T` is injective (no zero eigenvalue),
  then `Λ₊ + Λ₋ = 1`. This is a sanity check that the definition is the
  usual one. The rest of the development does not use it.
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped InnerProductSpace

namespace KineticBalance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The positive spectral subspace of `T`: the sum of the eigenspaces of `T`
for positive eigenvalues. -/
def posSpectralSubspace (T : E →ₗ[ℝ] E) : Submodule ℝ E :=
  ⨆ (μ : ℝ) (_ : 0 < μ), Module.End.eigenspace T μ

/-- The negative spectral subspace of `T`: the sum of the eigenspaces of `T`
for negative eigenvalues. -/
def negSpectralSubspace (T : E →ₗ[ℝ] E) : Submodule ℝ E :=
  ⨆ (μ : ℝ) (_ : μ < 0), Module.End.eigenspace T μ

/-- `Λ₊`: the orthogonal projector onto the positive spectral subspace. -/
noncomputable def specProjPos (T : E →ₗ[ℝ] E) : E →L[ℝ] E :=
  (posSpectralSubspace T).starProjection

/-- `Λ₋`: the orthogonal projector onto the negative spectral subspace. -/
noncomputable def specProjNeg (T : E →ₗ[ℝ] E) : E →L[ℝ] E :=
  (negSpectralSubspace T).starProjection

variable {T : E →ₗ[ℝ] E}

lemma eigenspace_le_posSpectralSubspace {μ : ℝ} (hμ : 0 < μ) :
    Module.End.eigenspace T μ ≤ posSpectralSubspace T :=
  le_iSup₂ (f := fun (μ : ℝ) (_ : 0 < μ) => Module.End.eigenspace T μ) μ hμ

lemma eigenspace_le_negSpectralSubspace {μ : ℝ} (hμ : μ < 0) :
    Module.End.eigenspace T μ ≤ negSpectralSubspace T :=
  le_iSup₂ (f := fun (μ : ℝ) (_ : μ < 0) => Module.End.eigenspace T μ) μ hμ

/-- For symmetric `T`, an eigenspace with a nonpositive eigenvalue is
orthogonal to the positive spectral subspace. -/
lemma eigenspace_isOrtho_posSpectralSubspace (hT : T.IsSymmetric) {μ : ℝ} (hμ : μ ≤ 0) :
    Module.End.eigenspace T μ ⟂ posSpectralSubspace T :=
  Submodule.isOrtho_iSup_right.mpr fun ν => Submodule.isOrtho_iSup_right.mpr fun hν =>
    hT.orthogonalFamily_eigenspaces.isOrtho (ne_of_lt (lt_of_le_of_lt hμ hν))

/-- For symmetric `T`, an eigenspace with a nonnegative eigenvalue is
orthogonal to the negative spectral subspace. -/
lemma eigenspace_isOrtho_negSpectralSubspace (hT : T.IsSymmetric) {μ : ℝ} (hμ : 0 ≤ μ) :
    Module.End.eigenspace T μ ⟂ negSpectralSubspace T :=
  Submodule.isOrtho_iSup_right.mpr fun ν => Submodule.isOrtho_iSup_right.mpr fun hν =>
    hT.orthogonalFamily_eigenspaces.isOrtho (ne_of_gt (lt_of_lt_of_le hν hμ))

/-- `Λ₊ v = v` for an eigenvector `v` with positive eigenvalue. -/
theorem specProjPos_apply_of_pos {μ : ℝ} {v : E} (hv : T v = μ • v) (hμ : 0 < μ) :
    specProjPos T v = v :=
  Submodule.starProjection_eq_self_iff.mpr
    (eigenspace_le_posSpectralSubspace hμ (Module.End.mem_eigenspace_iff.mpr hv))

/-- `Λ₊ v = 0` for an eigenvector `v` with nonpositive eigenvalue
(`T` symmetric). -/
theorem specProjPos_apply_of_nonpos (hT : T.IsSymmetric) {μ : ℝ} {v : E}
    (hv : T v = μ • v) (hμ : μ ≤ 0) : specProjPos T v = 0 :=
  Submodule.starProjection_apply_eq_zero_iff.mpr
    (eigenspace_isOrtho_posSpectralSubspace hT hμ (Module.End.mem_eigenspace_iff.mpr hv))

/-- `Λ₋ v = v` for an eigenvector `v` with negative eigenvalue. -/
theorem specProjNeg_apply_of_neg {μ : ℝ} {v : E} (hv : T v = μ • v) (hμ : μ < 0) :
    specProjNeg T v = v :=
  Submodule.starProjection_eq_self_iff.mpr
    (eigenspace_le_negSpectralSubspace hμ (Module.End.mem_eigenspace_iff.mpr hv))

/-- `Λ₋ v = 0` for an eigenvector `v` with nonnegative eigenvalue
(`T` symmetric). -/
theorem specProjNeg_apply_of_nonneg (hT : T.IsSymmetric) {μ : ℝ} {v : E}
    (hv : T v = μ • v) (hμ : 0 ≤ μ) : specProjNeg T v = 0 :=
  Submodule.starProjection_apply_eq_zero_iff.mpr
    (eigenspace_isOrtho_negSpectralSubspace hT hμ (Module.End.mem_eigenspace_iff.mpr hv))

/-- The negative and positive spectral subspaces of a symmetric operator are
orthogonal. -/
lemma negSpectralSubspace_isOrtho_pos (hT : T.IsSymmetric) :
    negSpectralSubspace T ⟂ posSpectralSubspace T :=
  Submodule.isOrtho_iSup_left.mpr fun _ => Submodule.isOrtho_iSup_left.mpr fun hμ =>
    eigenspace_isOrtho_posSpectralSubspace hT hμ.le

/-- Sanity check of the definitions: for a symmetric operator with trivial
kernel (no zero eigenvalue), `Λ₊ + Λ₋ = 1`. -/
theorem specProjPos_add_specProjNeg (hT : T.IsSymmetric) (hker : ∀ v, T v = 0 → v = 0) :
    specProjPos T + specProjNeg T = 1 := by
  -- the eigenspaces of `T` span `E`
  have htop : (⨆ μ, Module.End.eigenspace T μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hT.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hsup : posSpectralSubspace T ⊔ negSpectralSubspace T = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun μ => ?_
    rcases lt_trichotomy μ 0 with hμ | hμ | hμ
    · exact (eigenspace_le_negSpectralSubspace hμ).trans le_sup_right
    · intro x hx
      rw [hμ, Module.End.mem_eigenspace_iff, zero_smul] at hx
      rw [hker x hx]
      exact Submodule.zero_mem _
    · exact (eigenspace_le_posSpectralSubspace hμ).trans le_sup_left
  have hNP := negSpectralSubspace_isOrtho_pos hT
  ext x
  have hx : x ∈ posSpectralSubspace T ⊔ negSpectralSubspace T := by
    rw [hsup]; exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
  have h1 : specProjPos T p = p := Submodule.starProjection_eq_self_iff.mpr hp
  have h2 : specProjPos T q = 0 := Submodule.starProjection_apply_eq_zero_iff.mpr (hNP hq)
  have h3 : specProjNeg T p = 0 :=
    Submodule.starProjection_apply_eq_zero_iff.mpr (hNP.symm hp)
  have h4 : specProjNeg T q = q := Submodule.starProjection_eq_self_iff.mpr hq
  simp [h1, h2, h3, h4]

end KineticBalance
