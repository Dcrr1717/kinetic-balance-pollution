/-
The two-dimensional Dirac fiber, with the genuine spectral projectors.

Proposition 2.1 of the paper reduces the free Dirac matrix `H₀` to
orthogonal, invariant two-dimensional fibers. On each fiber `H₀` acts, in
an orthonormal frame `(e₁, e₂)`, as the 2×2 matrix

  h(σ) = [[c², cσ], [cσ, −c²]],   σ = 2ct.

`IsDiracFiber T c t e₁ e₂` records exactly this, for an arbitrary
operator `T`. The concrete matrix `H₀` is handled in `DiracMatrix.lean`.

In this file everything is *derived*, nothing is substituted by hand:

* `IsDiracFiber.apply_vPlus`, `IsDiracFiber.apply_vMinus`: the vectors
  `v₊ = (e₁ + ρ e₂)/√(1+ρ²)` and `v₋ = (−ρ e₁ + e₂)/√(1+ρ²)` are
  eigenvectors of `T` with eigenvalues `±E`, `E = c²√(1+4t²)`;
* `IsDiracFiber.specProjPos_fv`, `IsDiracFiber.specProjNeg_fv`: the
  spectral projectors `Λ±` of a symmetric `T` (`SpectralProjector.lean`)
  act on the fiber as `x ↦ ⟪v±, x⟫ v±`;
* `IsDiracFiber.leakage_trialDir` (**Theorem 3.1**): for each of the four
  trial families the leakage `‖Λ_wrong u‖/‖u‖`, computed from the actual
  projector, equals the closed form printed in the paper;
* `IsDiracFiber.defect_factor_pos/neg`: the per-fiber factor of
  Theorem 4.1, `‖Λ b‖·‖(I−Λ) b‖ = ℓ √(1 − ℓ²)` for the normalized trial
  vector;
* `IsDiracFiber.rayleigh_trialUnit` (operator form of Eq. (rayleigh)).
-/

import KineticBalance.SpectralProjector
import FiberLemmas

open scoped InnerProductSpace

namespace KineticBalance

/-! ### Scalar quantities attached to a fiber -/

/-- `w = √(1+4t²)`. -/
noncomputable def wt (t : ℝ) : ℝ := Real.sqrt (1 + 4 * t ^ 2)

/-- `ρ = 2t/(1+w)`: the slope of the positive-energy eigenvector of `h(2ct)`. -/
noncomputable def rho (t : ℝ) : ℝ := 2 * t / (1 + wt t)

/-- `√(1+ρ²)`: the normalization of the fiber eigenvectors. -/
noncomputable def nrho (t : ℝ) : ℝ := Real.sqrt (1 + rho t ^ 2)

lemma wt_sq (t : ℝ) : wt t ^ 2 = 1 + 4 * t ^ 2 := FeastLemmas.w_sq t

lemma wt_pos (t : ℝ) : 0 < wt t := FeastLemmas.w_pos t

lemma one_add_wt_pos (t : ℝ) : 0 < 1 + wt t := by
  have := wt_pos t
  linarith

lemma rho_mul (t : ℝ) : rho t * (1 + wt t) = 2 * t :=
  div_mul_cancel₀ _ (one_add_wt_pos t).ne'

/-- `1 + 2tρ = w`. -/
lemma one_add_two_mul_rho (t : ℝ) : 1 + 2 * t * rho t = wt t := by
  have h := rho_mul t
  have hw := wt_sq t
  have hprod : (1 + 2 * t * rho t - wt t) * (1 + wt t) = 0 := by
    linear_combination (2 * t) * h - hw
  rcases mul_eq_zero.mp hprod with h0 | h0
  · linarith
  · exact absurd h0 (one_add_wt_pos t).ne'

lemma rho_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ rho t := FeastLemmas.rho_nonneg ht

lemma rho_le {t : ℝ} (ht : 0 ≤ t) : rho t ≤ t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    simp [rho]
  · exact (FeastLemmas.rho_lt h).le

lemma nrho_pos (t : ℝ) : 0 < nrho t := Real.sqrt_pos.mpr (by positivity)

lemma nrho_sq (t : ℝ) : nrho t ^ 2 = 1 + rho t ^ 2 := Real.sq_sqrt (by positivity)

lemma nrho_inv_sq_mul (t : ℝ) : (nrho t)⁻¹ ^ 2 * (1 + rho t ^ 2) = 1 := by
  rw [← nrho_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (nrho_pos t).ne')]

/-- `|A| |B| = |B| √(1−B²)` when `A² + B² = 1`. -/
lemma abs_mul_abs_eq_of_sq_add_sq {A B : ℝ} (h : A ^ 2 + B ^ 2 = 1) :
    |A| * |B| = |B| * Real.sqrt (1 - |B| ^ 2) := by
  rw [sq_abs, show 1 - B ^ 2 = A ^ 2 by linarith, Real.sqrt_sq_eq_abs, mul_comm]

/-! ### Fiber coordinates -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vector with fiber coordinates `(a, b)`: `a e₁ + b e₂`. -/
def fv (e₁ e₂ : E) (a b : ℝ) : E := a • e₁ + b • e₂

lemma smul_fv (e₁ e₂ : E) (s a b : ℝ) : s • fv e₁ e₂ a b = fv e₁ e₂ (s * a) (s * b) := by
  simp only [fv, smul_add, smul_smul]

lemma smul_fv_add_smul_fv (e₁ e₂ : E) (s s' a b a' b' : ℝ) :
    s • fv e₁ e₂ a b + s' • fv e₁ e₂ a' b' = fv e₁ e₂ (s * a + s' * a') (s * b + s' * b') := by
  simp only [fv]
  module

lemma fv_mem_span (e₁ e₂ : E) (a b : ℝ) : fv e₁ e₂ a b ∈ Submodule.span ℝ {e₁, e₂} :=
  Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩

/-- `T` acts on the orthonormal frame `(e₁, e₂)` as `h(σ)` with `σ = 2ct`
(Proposition 2.1): `T e₁ = c² e₁ + cσ e₂` and `T e₂ = cσ e₁ − c² e₂`. -/
structure IsDiracFiber (T : E →ₗ[ℝ] E) (c t : ℝ) (e₁ e₂ : E) : Prop where
  norm_e₁ : ‖e₁‖ = 1
  norm_e₂ : ‖e₂‖ = 1
  inner_e₁_e₂ : ⟪e₁, e₂⟫_ℝ = 0
  apply_e₁ : T e₁ = c ^ 2 • e₁ + (2 * c ^ 2 * t) • e₂
  apply_e₂ : T e₂ = (2 * c ^ 2 * t) • e₁ - c ^ 2 • e₂

/-- The positive-energy fiber eigenvector `v₊ = (e₁ + ρ e₂)/√(1+ρ²)`. -/
noncomputable def vPlus (t : ℝ) (e₁ e₂ : E) : E :=
  fv e₁ e₂ (nrho t)⁻¹ ((nrho t)⁻¹ * rho t)

/-- The negative-energy fiber eigenvector `v₋ = (−ρ e₁ + e₂)/√(1+ρ²)`. -/
noncomputable def vMinus (t : ℝ) (e₁ e₂ : E) : E :=
  fv e₁ e₂ (-((nrho t)⁻¹ * rho t)) (nrho t)⁻¹

/-- First fiber coordinate in the eigenbasis: `⟪v₊, a e₁ + b e₂⟫`. -/
noncomputable def coordPlus (t a b : ℝ) : ℝ := (nrho t)⁻¹ * (a + rho t * b)

/-- Second fiber coordinate in the eigenbasis: `⟪v₋, a e₁ + b e₂⟫`. -/
noncomputable def coordMinus (t a b : ℝ) : ℝ := (nrho t)⁻¹ * (-(rho t) * a + b)

/-- Every fiber vector splits along the eigenbasis:
`a e₁ + b e₂ = ⟪v₊,·⟫ v₊ + ⟪v₋,·⟫ v₋`. Pure linear algebra. -/
lemma fv_eq_coord (t : ℝ) (e₁ e₂ : E) (a b : ℝ) :
    fv e₁ e₂ a b = coordPlus t a b • vPlus t e₁ e₂ + coordMinus t a b • vMinus t e₁ e₂ := by
  rw [vPlus, vMinus, smul_fv_add_smul_fv]
  have h := nrho_inv_sq_mul t
  congr 1
  · simp only [coordPlus, coordMinus]
    linear_combination (-a) * h
  · simp only [coordPlus, coordMinus]
    linear_combination (-b) * h

lemma coordPlus_sq_add_coordMinus_sq (t a b : ℝ) :
    coordPlus t a b ^ 2 + coordMinus t a b ^ 2 = a ^ 2 + b ^ 2 := by
  have h := nrho_inv_sq_mul t
  simp only [coordPlus, coordMinus]
  linear_combination (a ^ 2 + b ^ 2) * h

namespace IsDiracFiber

variable {T : E →ₗ[ℝ] E} {c t : ℝ} {e₁ e₂ : E}

lemma inner_fv (h : IsDiracFiber T c t e₁ e₂) (a b a' b' : ℝ) :
    ⟪fv e₁ e₂ a b, fv e₁ e₂ a' b'⟫_ℝ = a * a' + b * b' := by
  have h21 : ⟪e₂, e₁⟫_ℝ = 0 := by rw [real_inner_comm]; exact h.inner_e₁_e₂
  simp only [fv, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h.inner_e₁_e₂, h21, real_inner_self_eq_norm_sq, h.norm_e₁, h.norm_e₂]
  ring

lemma norm_fv (h : IsDiracFiber T c t e₁ e₂) (a b : ℝ) :
    ‖fv e₁ e₂ a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [norm_eq_sqrt_real_inner, h.inner_fv]
  congr 1
  ring

lemma apply_fv (h : IsDiracFiber T c t e₁ e₂) (a b : ℝ) :
    T (fv e₁ e₂ a b) =
      fv e₁ e₂ (c ^ 2 * a + 2 * c ^ 2 * t * b) (2 * c ^ 2 * t * a - c ^ 2 * b) := by
  simp only [fv, map_add, map_smul, h.apply_e₁, h.apply_e₂]
  module

/-- `T v₊ = E v₊` with `E = c²√(1+4t²)` (Proposition 2.1). -/
theorem apply_vPlus (h : IsDiracFiber T c t e₁ e₂) :
    T (vPlus t e₁ e₂) = (c ^ 2 * wt t) • vPlus t e₁ e₂ := by
  have h1 := one_add_two_mul_rho t
  have hρ := rho_mul t
  rw [vPlus, h.apply_fv, smul_fv]
  congr 1
  · linear_combination (c ^ 2 * (nrho t)⁻¹) * h1
  · linear_combination (-(c ^ 2 * (nrho t)⁻¹)) * hρ

/-- `T v₋ = −E v₋` with `E = c²√(1+4t²)` (Proposition 2.1). -/
theorem apply_vMinus (h : IsDiracFiber T c t e₁ e₂) :
    T (vMinus t e₁ e₂) = (-(c ^ 2 * wt t)) • vMinus t e₁ e₂ := by
  have h1 := one_add_two_mul_rho t
  have hρ := rho_mul t
  rw [vMinus, h.apply_fv, smul_fv]
  congr 1
  · linear_combination (-(c ^ 2 * (nrho t)⁻¹)) * hρ
  · linear_combination (-(c ^ 2 * (nrho t)⁻¹)) * h1

lemma norm_vPlus (h : IsDiracFiber T c t e₁ e₂) : ‖vPlus t e₁ e₂‖ = 1 := by
  rw [vPlus, h.norm_fv, show (nrho t)⁻¹ ^ 2 + ((nrho t)⁻¹ * rho t) ^ 2 = 1 by
    linear_combination nrho_inv_sq_mul t, Real.sqrt_one]

lemma norm_vMinus (h : IsDiracFiber T c t e₁ e₂) : ‖vMinus t e₁ e₂‖ = 1 := by
  rw [vMinus, h.norm_fv, show (-((nrho t)⁻¹ * rho t)) ^ 2 + (nrho t)⁻¹ ^ 2 = 1 by
    linear_combination nrho_inv_sq_mul t, Real.sqrt_one]

lemma inner_vPlus_vMinus (h : IsDiracFiber T c t e₁ e₂) :
    ⟪vPlus t e₁ e₂, vMinus t e₁ e₂⟫_ℝ = 0 := by
  rw [vPlus, vMinus, h.inner_fv]
  ring

/-- `‖a e₁ + b e₂‖² = ⟪v₊,·⟫² + ⟪v₋,·⟫²` (fiber Pythagoras, used for
`g² = 1 − ℓ²` in the proof of Theorem 4.1). -/
lemma norm_fv_sq (h : IsDiracFiber T c t e₁ e₂) (a b : ℝ) :
    ‖fv e₁ e₂ a b‖ ^ 2 = coordPlus t a b ^ 2 + coordMinus t a b ^ 2 := by
  rw [h.norm_fv, Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b)),
    coordPlus_sq_add_coordMinus_sq]

variable [FiniteDimensional ℝ E]

lemma energy_pos (hc : c ≠ 0) : 0 < c ^ 2 * wt t :=
  mul_pos (pow_pos (abs_pos.mpr hc) 2 |>.trans_eq (sq_abs c)) (wt_pos t)

lemma specProjPos_vPlus (h : IsDiracFiber T c t e₁ e₂) (hc : c ≠ 0) :
    specProjPos T (vPlus t e₁ e₂) = vPlus t e₁ e₂ :=
  specProjPos_apply_of_pos h.apply_vPlus (energy_pos hc)

lemma specProjPos_vMinus (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0) :
    specProjPos T (vMinus t e₁ e₂) = 0 :=
  specProjPos_apply_of_nonpos hT h.apply_vMinus (by linarith [energy_pos (t := t) hc])

lemma specProjNeg_vPlus (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0) :
    specProjNeg T (vPlus t e₁ e₂) = 0 :=
  specProjNeg_apply_of_nonneg hT h.apply_vPlus (energy_pos hc).le

lemma specProjNeg_vMinus (h : IsDiracFiber T c t e₁ e₂) (hc : c ≠ 0) :
    specProjNeg T (vMinus t e₁ e₂) = vMinus t e₁ e₂ :=
  specProjNeg_apply_of_neg h.apply_vMinus (by linarith [energy_pos (t := t) hc])

/-- On the fiber, `Λ₊ x = ⟪v₊, x⟫ v₊`. -/
theorem specProjPos_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (a b : ℝ) : specProjPos T (fv e₁ e₂ a b) = coordPlus t a b • vPlus t e₁ e₂ := by
  rw [fv_eq_coord t, map_add, map_smul, map_smul, h.specProjPos_vPlus hc,
    h.specProjPos_vMinus hT hc, smul_zero, add_zero]

/-- On the fiber, `Λ₋ x = ⟪v₋, x⟫ v₋`. -/
theorem specProjNeg_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (a b : ℝ) : specProjNeg T (fv e₁ e₂ a b) = coordMinus t a b • vMinus t e₁ e₂ := by
  rw [fv_eq_coord t, map_add, map_smul, map_smul, h.specProjNeg_vPlus hT hc,
    h.specProjNeg_vMinus hc, smul_zero, zero_add]

lemma sub_specProjPos_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (a b : ℝ) :
    fv e₁ e₂ a b - specProjPos T (fv e₁ e₂ a b) = coordMinus t a b • vMinus t e₁ e₂ := by
  rw [h.specProjPos_fv hT hc]
  conv_lhs => rw [fv_eq_coord t]
  abel

lemma sub_specProjNeg_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (a b : ℝ) :
    fv e₁ e₂ a b - specProjNeg T (fv e₁ e₂ a b) = coordPlus t a b • vPlus t e₁ e₂ := by
  rw [h.specProjNeg_fv hT hc]
  conv_lhs => rw [fv_eq_coord t]
  abel

lemma norm_specProjPos_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (a b : ℝ) : ‖specProjPos T (fv e₁ e₂ a b)‖ = |coordPlus t a b| := by
  rw [h.specProjPos_fv hT hc, norm_smul, h.norm_vPlus, mul_one, Real.norm_eq_abs]

lemma norm_specProjNeg_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (a b : ℝ) : ‖specProjNeg T (fv e₁ e₂ a b)‖ = |coordMinus t a b| := by
  rw [h.specProjNeg_fv hT hc, norm_smul, h.norm_vMinus, mul_one, Real.norm_eq_abs]

lemma norm_sub_specProjPos_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric)
    (hc : c ≠ 0) (a b : ℝ) :
    ‖fv e₁ e₂ a b - specProjPos T (fv e₁ e₂ a b)‖ = |coordMinus t a b| := by
  rw [h.sub_specProjPos_fv hT hc, norm_smul, h.norm_vMinus, mul_one, Real.norm_eq_abs]

lemma norm_sub_specProjNeg_fv (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric)
    (hc : c ≠ 0) (a b : ℝ) :
    ‖fv e₁ e₂ a b - specProjNeg T (fv e₁ e₂ a b)‖ = |coordPlus t a b| := by
  rw [h.sub_specProjNeg_fv hT hc, norm_smul, h.norm_vPlus, mul_one, Real.norm_eq_abs]

/-- The fiber `span {e₁, e₂}` is invariant under `Λ₊`. -/
theorem specProjPos_mem_span (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    {x : E} (hx : x ∈ Submodule.span ℝ {e₁, e₂}) :
    specProjPos T x ∈ Submodule.span ℝ {e₁, e₂} := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [show a • e₁ + b • e₂ = fv e₁ e₂ a b from rfl, h.specProjPos_fv hT hc, vPlus, smul_fv]
  exact fv_mem_span _ _ _ _

/-- The fiber `span {e₁, e₂}` is invariant under `Λ₋`. -/
theorem specProjNeg_mem_span (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    {x : E} (hx : x ∈ Submodule.span ℝ {e₁, e₂}) :
    specProjNeg T x ∈ Submodule.span ℝ {e₁, e₂} := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [show a • e₁ + b • e₂ = fv e₁ e₂ a b from rfl, h.specProjNeg_fv hT hc, vMinus, smul_fv]
  exact fv_mem_span _ _ _ _

omit [FiniteDimensional ℝ E] in
/-- The fiber `span {e₁, e₂}` is invariant under `T` itself. -/
theorem apply_mem_span (h : IsDiracFiber T c t e₁ e₂) {x : E}
    (hx : x ∈ Submodule.span ℝ {e₁, e₂}) : T x ∈ Submodule.span ℝ {e₁, e₂} := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [show a • e₁ + b • e₂ = fv e₁ e₂ a b from rfl, h.apply_fv]
  exact fv_mem_span _ _ _ _

end IsDiracFiber

/-! ### The four kinetic-balance trial families (Eq. (families)) -/

/-- The four single-family prescriptions of the paper: balanced, split,
positronic (inverse balance) and anti-balanced. -/
inductive Family
  | bal
  | spl
  | pos
  | anti
  deriving DecidableEq

namespace Family

/-- Fiber coordinates `(x, y)` of the trial direction `u = x e₁ + y e₂`:
`u_bal = (1, t)`, `u_spl = (1, 0)`, `u_pos = (−t, 1)`, `u_anti = (t, 1)`. -/
def coeffs : Family → ℝ → ℝ × ℝ
  | bal, t => (1, t)
  | spl, _ => (1, 0)
  | pos, t => (-t, 1)
  | anti, t => (t, 1)

/-- The closed-form leakages of Theorem 3.1, Eqs. (lspl), (lbal), (lanti). -/
noncomputable def leak : Family → ℝ → ℝ
  | bal, t => (t - rho t) / (nrho t * Real.sqrt (1 + t ^ 2))
  | spl, t => rho t / nrho t
  | pos, t => (t - rho t) / (nrho t * Real.sqrt (1 + t ^ 2))
  | anti, t => (t + rho t) / (nrho t * Real.sqrt (1 + t ^ 2))

/-- The fiber Rayleigh values of Eq. (rayleigh). -/
noncomputable def rayleigh : Family → ℝ → ℝ → ℝ
  | bal, c, t => c ^ 2 * (1 + 3 * t ^ 2) / (1 + t ^ 2)
  | spl, c, _ => c ^ 2
  | pos, c, t => -(c ^ 2 * (1 + 3 * t ^ 2) / (1 + t ^ 2))
  | anti, c, t => c ^ 2 * (5 * t ^ 2 - 1) / (1 + t ^ 2)

lemma coeffs_sq_pos (f : Family) (t : ℝ) : 0 < (f.coeffs t).1 ^ 2 + (f.coeffs t).2 ^ 2 := by
  cases f <;> simp only [coeffs] <;> positivity

/-- Eq. (lbal) in the form printed after the key identity (Eq. (key)):
`ℓ_bal = 4t³ / ((1+w)² √(1+ρ²) √(1+t²))`. -/
theorem leak_bal_eq_key (t : ℝ) :
    leak bal t = 4 * t ^ 3 / ((1 + wt t) ^ 2 * (nrho t * Real.sqrt (1 + t ^ 2))) := by
  simp only [leak, rho, wt]
  rw [FeastLemmas.key_identity, div_div]

lemma leak_pos_eq_leak_bal (t : ℝ) : leak pos t = leak bal t := rfl

/-! Scalar evaluation of the four leakages from the eigenbasis coordinates. -/

lemma leak_bal_of_coord {t : ℝ} (ht : 0 ≤ t) :
    |coordMinus t 1 t| / Real.sqrt (1 ^ 2 + t ^ 2) = leak bal t := by
  show _ = (t - rho t) / (nrho t * Real.sqrt (1 + t ^ 2))
  have hN := nrho_pos t
  have hρt := rho_le ht
  rw [coordMinus, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hN.le)
    (by linarith : (0 : ℝ) ≤ -rho t * 1 + t)), one_pow, mul_one, neg_add_eq_sub,
    inv_mul_eq_div, div_div]

lemma leak_spl_of_coord {t : ℝ} (ht : 0 ≤ t) :
    |coordMinus t 1 0| / Real.sqrt (1 ^ 2 + 0 ^ 2) = leak spl t := by
  show _ = rho t / nrho t
  have hN := nrho_pos t
  have hρ0 := rho_nonneg ht
  have h1 : Real.sqrt (1 ^ 2 + 0 ^ 2) = 1 := by norm_num
  rw [coordMinus, mul_one, add_zero, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hN),
    abs_of_nonneg hρ0, h1, div_one, inv_mul_eq_div]

lemma leak_pos_of_coord {t : ℝ} (ht : 0 ≤ t) :
    |coordPlus t (-t) 1| / Real.sqrt ((-t) ^ 2 + 1 ^ 2) = leak pos t := by
  show _ = (t - rho t) / (nrho t * Real.sqrt (1 + t ^ 2))
  have hN := nrho_pos t
  have hρt := rho_le ht
  have h2 : (-t) ^ 2 + 1 ^ 2 = 1 + t ^ 2 := by ring
  rw [coordPlus, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hN.le)
    (by linarith : -t + rho t * 1 ≤ 0)), h2,
    show -((nrho t)⁻¹ * (-t + rho t * 1)) = (nrho t)⁻¹ * (t - rho t) by ring,
    inv_mul_eq_div, div_div]

lemma leak_anti_of_coord {t : ℝ} (ht : 0 ≤ t) :
    |coordPlus t t 1| / Real.sqrt (t ^ 2 + 1 ^ 2) = leak anti t := by
  show _ = (t + rho t) / (nrho t * Real.sqrt (1 + t ^ 2))
  have hN := nrho_pos t
  have hρ0 := rho_nonneg ht
  have h2 : t ^ 2 + 1 ^ 2 = 1 + t ^ 2 := by ring
  rw [coordPlus, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hN.le)
    (by linarith : (0 : ℝ) ≤ t + rho t * 1)), h2, mul_one, inv_mul_eq_div, div_div]

end Family

variable [FiniteDimensional ℝ E]

/-- The wrong-sector projector of a family: `Λ₋` for the electronic
families `bal`, `spl`, and `Λ₊` for the positronic families `pos`, `anti`. -/
noncomputable def wrongProj (T : E →ₗ[ℝ] E) : Family → (E →L[ℝ] E)
  | .bal => specProjNeg T
  | .spl => specProjNeg T
  | .pos => specProjPos T
  | .anti => specProjPos T

/-- The leakage of a trial vector, `ℓ(u) = ‖Λ_wrong u‖ / ‖u‖`. -/
noncomputable def leakage (T : E →ₗ[ℝ] E) (f : Family) (u : E) : ℝ :=
  ‖wrongProj T f u‖ / ‖u‖

/-- The (unnormalized) trial direction of family `f` in a fiber. -/
def trialDir (f : Family) (t : ℝ) (e₁ e₂ : E) : E :=
  fv e₁ e₂ (f.coeffs t).1 (f.coeffs t).2

/-- The normalized trial vector of family `f` in a fiber. -/
noncomputable def trialUnit (f : Family) (t : ℝ) (e₁ e₂ : E) : E :=
  ‖trialDir f t e₁ e₂‖⁻¹ • trialDir f t e₁ e₂

omit [FiniteDimensional ℝ E] in
lemma trialDir_mem_span (f : Family) (t : ℝ) (e₁ e₂ : E) :
    trialDir f t e₁ e₂ ∈ Submodule.span ℝ {e₁, e₂} := fv_mem_span _ _ _ _

omit [FiniteDimensional ℝ E] in
lemma trialUnit_mem_span (f : Family) (t : ℝ) (e₁ e₂ : E) :
    trialUnit f t e₁ e₂ ∈ Submodule.span ℝ {e₁, e₂} :=
  Submodule.smul_mem _ _ (trialDir_mem_span f t e₁ e₂)

namespace IsDiracFiber

variable {T : E →ₗ[ℝ] E} {c t : ℝ} {e₁ e₂ : E}

omit [FiniteDimensional ℝ E] in
lemma norm_trialDir_pos (h : IsDiracFiber T c t e₁ e₂) (f : Family) :
    0 < ‖trialDir f t e₁ e₂‖ := by
  rw [trialDir, h.norm_fv]
  exact Real.sqrt_pos.mpr (f.coeffs_sq_pos t)

omit [FiniteDimensional ℝ E] in
lemma norm_trialUnit (h : IsDiracFiber T c t e₁ e₂) (f : Family) :
    ‖trialUnit f t e₁ e₂‖ = 1 := by
  have hpos := h.norm_trialDir_pos f
  rw [trialUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hpos.ne']

/-- **Theorem 3.1 (exact per-mode leakage).** In a Dirac fiber of a
symmetric operator, the leakage `‖Λ_wrong u‖/‖u‖` of each trial direction,
with `Λ±` the genuine spectral projectors, equals the paper's closed form:

* `ℓ(u_bal)  = (t−ρ)/(√(1+ρ²)√(1+t²))`,
* `ℓ(u_spl)  = ρ/√(1+ρ²)`,
* `ℓ(u_pos)  = (t−ρ)/(√(1+ρ²)√(1+t²))`,
* `ℓ(u_anti) = (t+ρ)/(√(1+ρ²)√(1+t²))`. -/
theorem leakage_trialDir (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (ht : 0 ≤ t) (f : Family) : leakage T f (trialDir f t e₁ e₂) = f.leak t := by
  cases f
  · -- balanced, measured with `Λ₋`
    show ‖specProjNeg T (fv e₁ e₂ 1 t)‖ / ‖fv e₁ e₂ 1 t‖ = Family.leak .bal t
    rw [h.norm_specProjNeg_fv hT hc, h.norm_fv]
    exact Family.leak_bal_of_coord ht
  · -- split, measured with `Λ₋`
    show ‖specProjNeg T (fv e₁ e₂ 1 0)‖ / ‖fv e₁ e₂ 1 0‖ = Family.leak .spl t
    rw [h.norm_specProjNeg_fv hT hc, h.norm_fv]
    exact Family.leak_spl_of_coord ht
  · -- positronic, measured with `Λ₊`
    show ‖specProjPos T (fv e₁ e₂ (-t) 1)‖ / ‖fv e₁ e₂ (-t) 1‖ = Family.leak .pos t
    rw [h.norm_specProjPos_fv hT hc, h.norm_fv]
    exact Family.leak_pos_of_coord ht
  · -- anti-balanced, measured with `Λ₊`
    show ‖specProjPos T (fv e₁ e₂ t 1)‖ / ‖fv e₁ e₂ t 1‖ = Family.leak .anti t
    rw [h.norm_specProjPos_fv hT hc, h.norm_fv]
    exact Family.leak_anti_of_coord ht

/-- The leakage is scale invariant; for the unit trial vector it is
`‖Λ_wrong b‖`. -/
lemma leakage_trialDir_eq_norm (h : IsDiracFiber T c t e₁ e₂) (f : Family) :
    leakage T f (trialDir f t e₁ e₂) = ‖wrongProj T f (trialUnit f t e₁ e₂)‖ := by
  rw [leakage, trialUnit, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (h.norm_trialDir_pos f)), div_eq_inv_mul]

omit [FiniteDimensional ℝ E] in
/-- Coordinates of the unit trial vector. -/
lemma trialUnit_eq_fv (f : Family) :
    trialUnit f t e₁ e₂ = fv e₁ e₂ (‖trialDir f t e₁ e₂‖⁻¹ * (f.coeffs t).1)
      (‖trialDir f t e₁ e₂‖⁻¹ * (f.coeffs t).2) := by
  simp only [trialUnit, trialDir, smul_fv]

/-- **Per-fiber factor of Theorem 4.1, with `Λ₊`.** For the unit trial
vector `b` of family `f`: `‖Λ₊ b‖ · ‖(I − Λ₊) b‖ = ℓ √(1 − ℓ²)`, where
`ℓ = f.leak t` is the closed form of Theorem 3.1. -/
theorem defect_factor_pos (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (ht : 0 ≤ t) (f : Family) :
    ‖specProjPos T (trialUnit f t e₁ e₂)‖ *
        ‖trialUnit f t e₁ e₂ - specProjPos T (trialUnit f t e₁ e₂)‖ =
      f.leak t * Real.sqrt (1 - f.leak t ^ 2) := by
  set A := coordPlus t (‖trialDir f t e₁ e₂‖⁻¹ * (f.coeffs t).1)
    (‖trialDir f t e₁ e₂‖⁻¹ * (f.coeffs t).2) with hA
  set B := coordMinus t (‖trialDir f t e₁ e₂‖⁻¹ * (f.coeffs t).1)
    (‖trialDir f t e₁ e₂‖⁻¹ * (f.coeffs t).2) with hB
  have hAB : A ^ 2 + B ^ 2 = 1 := by
    rw [hA, hB, ← h.norm_fv_sq, ← trialUnit_eq_fv, h.norm_trialUnit, one_pow]
  have hP : ‖specProjPos T (trialUnit f t e₁ e₂)‖ = |A| := by
    rw [trialUnit_eq_fv, h.norm_specProjPos_fv hT hc]
  have hQ : ‖trialUnit f t e₁ e₂ - specProjPos T (trialUnit f t e₁ e₂)‖ = |B| := by
    rw [trialUnit_eq_fv, h.norm_sub_specProjPos_fv hT hc]
  have hNeg : ‖specProjNeg T (trialUnit f t e₁ e₂)‖ = |B| := by
    rw [trialUnit_eq_fv, h.norm_specProjNeg_fv hT hc]
  have hleak := h.leakage_trialDir hT hc ht f
  rw [h.leakage_trialDir_eq_norm] at hleak
  rw [hP, hQ, ← hleak]
  cases f <;> simp only [wrongProj]
  · rw [hNeg]; exact abs_mul_abs_eq_of_sq_add_sq hAB
  · rw [hNeg]; exact abs_mul_abs_eq_of_sq_add_sq hAB
  · rw [hP, mul_comm]; exact abs_mul_abs_eq_of_sq_add_sq (by linarith)
  · rw [hP, mul_comm]; exact abs_mul_abs_eq_of_sq_add_sq (by linarith)

/-- **Per-fiber factor of Theorem 4.1, with `Λ₋`.** Same value as with
`Λ₊`. -/
theorem defect_factor_neg (h : IsDiracFiber T c t e₁ e₂) (hT : T.IsSymmetric) (hc : c ≠ 0)
    (ht : 0 ≤ t) (f : Family) :
    ‖specProjNeg T (trialUnit f t e₁ e₂)‖ *
        ‖trialUnit f t e₁ e₂ - specProjNeg T (trialUnit f t e₁ e₂)‖ =
      f.leak t * Real.sqrt (1 - f.leak t ^ 2) := by
  rw [← h.defect_factor_pos hT hc ht f, trialUnit_eq_fv, h.norm_specProjNeg_fv hT hc,
    h.norm_sub_specProjNeg_fv hT hc, h.norm_specProjPos_fv hT hc,
    h.norm_sub_specProjPos_fv hT hc, mul_comm]

omit [FiniteDimensional ℝ E] in
/-- **Eq. (rayleigh), operator form.** The Rayleigh quotient
`⟪T b, b⟫` of the unit trial vector of each family is the fiber Rayleigh
value: `R_bal = c²(1+3t²)/(1+t²)`, `R_spl = c²`,
`R_pos = −c²(1+3t²)/(1+t²)`, `R_anti = c²(5t²−1)/(1+t²)`. -/
theorem rayleigh_trialUnit (h : IsDiracFiber T c t e₁ e₂) (f : Family) :
    ⟪T (trialUnit f t e₁ e₂), trialUnit f t e₁ e₂⟫_ℝ = f.rayleigh c t := by
  have hn := h.norm_trialDir_pos f
  have hn2 : ‖trialDir f t e₁ e₂‖ ^ 2 = (f.coeffs t).1 ^ 2 + (f.coeffs t).2 ^ 2 := by
    rw [trialDir, h.norm_fv, Real.sq_sqrt (f.coeffs_sq_pos t).le]
  rw [trialUnit_eq_fv, h.apply_fv, h.inner_fv]
  set n := ‖trialDir f t e₁ e₂‖
  have hn0 : n ≠ 0 := hn.ne'
  cases f <;> simp only [Family.coeffs, Family.rayleigh] at hn2 ⊢
  · have h1 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp
    linear_combination (-(c ^ 2 * (1 + 3 * t ^ 2))) * hn2
  · field_simp
    linear_combination (-c ^ 2) * hn2
  · have h1 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp
    linear_combination (c ^ 2 * (1 + 3 * t ^ 2)) * hn2
  · have h1 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp
    linear_combination (-(c ^ 2 * (5 * t ^ 2 - 1))) * hn2

end IsDiracFiber

end KineticBalance
