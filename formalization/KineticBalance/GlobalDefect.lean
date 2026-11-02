/-
Theorem 4.1 (exact global conformity defect) and Corollary 4.2 (exact
conformity of an invariant trial space), in the abstract form that the
paper's proof uses.

Setting. `E` is a finite-dimensional real inner-product space and
`P = K.starProjection` is an orthogonal projector (in the application,
`P = Λ₊` or `P = Λ₋`). The space carries a family `W i` of mutually
orthogonal subspaces (the fibers), each mapped into itself by `P`. A
single-family trial space is `V = span {b i}`, with one unit trial vector
`b i ∈ W i` per fiber, and `Π` is the orthogonal projector onto `V`.

Main results.

* `fiber_defect_norm` (per-fiber identity, proof of Thm 4.1): for a unit
  vector `b`, `‖(I − b bᵀ) P b‖ = ‖P b‖ · ‖(I − P) b‖`. With `ℓ` the
  leakage of `b` out of the range of `P`, this is `ℓ √(1 − ℓ²)`.
* `global_defect` (Thm 4.1, abstract form): the operator norm
  `‖(I − Π) P Π‖` equals `max_i ‖P b i‖ · ‖(I − P) b i‖`.
* `defect_eq_zero_of_invariant` (Cor 4.2, abstract form): if `P` maps the
  trial space `V` into itself, then `(I − Π_V) P Π_V = 0`.

Everything here is proved with no `sorry`.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Orthonormal

open scoped InnerProductSpace
open Finset

namespace KineticBalance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `⟪b, P b⟫ = ‖P b‖²` for an orthogonal projector `P`. -/
lemma inner_self_starProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection] (b : E) :
    ⟪b, K.starProjection b⟫_ℝ = ‖K.starProjection b‖ ^ 2 := by
  have hpp : K.starProjection (K.starProjection b) = K.starProjection b :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem b)
  calc ⟪b, K.starProjection b⟫_ℝ = ⟪b, K.starProjection (K.starProjection b)⟫_ℝ := by rw [hpp]
    _ = ⟪K.starProjection b, K.starProjection b⟫_ℝ :=
        (Submodule.inner_starProjection_left_eq_right K b _).symm
    _ = ‖K.starProjection b‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- **Per-fiber defect identity** (step in the proof of Theorem 4.1).
For a unit vector `b` and an orthogonal projector `P`,
`‖(I − b bᵀ) P b‖ = ‖P b‖ · ‖(I − P) b‖`, where
`(I − b bᵀ) P b = P b − ⟪b, P b⟫ b`. -/
theorem fiber_defect_norm (K : Submodule ℝ E) [K.HasOrthogonalProjection] {b : E}
    (hb : ‖b‖ = 1) :
    ‖K.starProjection b - ⟪b, K.starProjection b⟫_ℝ • b‖ =
      ‖K.starProjection b‖ * ‖b - K.starProjection b‖ := by
  have hγ := inner_self_starProjection K b
  set p := K.starProjection b with hp
  have hγ' : ⟪p, b⟫_ℝ = ‖p‖ ^ 2 := by rw [real_inner_comm]; exact hγ
  have h1 : ‖p - ⟪b, p⟫_ℝ • b‖ ^ 2 = ‖p‖ ^ 2 * (1 - ‖p‖ ^ 2) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, hγ, hγ', hb,
      Real.norm_eq_abs, sq_abs]
    ring
  have h2 : ‖b - p‖ ^ 2 = 1 - ‖p‖ ^ 2 := by
    rw [norm_sub_sq_real, hγ, hb]
    ring
  have h3 : ‖p - ⟪b, p⟫_ℝ • b‖ ^ 2 = (‖p‖ * ‖b - p‖) ^ 2 := by
    rw [h1, mul_pow, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h3

/-- The orthogonal projector onto the span of a finite orthonormal family:
`Π x = ∑ i, ⟪b i, x⟫ b i`. -/
theorem starProjection_span_orthonormal [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    {b : ι → E} (hb : Orthonormal ℝ b) (x : E) :
    (Submodule.span ℝ (Set.range b)).starProjection x = ∑ i, ⟪b i, x⟫_ℝ • b i := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [inner_sub_left, hb.inner_left_fintype, real_inner_comm]
      simp
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
    | smul a y _ hy => rw [real_inner_smul_right, hy, mul_zero]

/-- Pythagoras for a pairwise-orthogonal family:
`‖∑ a i • w i‖² = ∑ (a i)² ‖w i‖²`. -/
lemma norm_sq_sum_smul_of_pairwise_inner_eq_zero {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (w : ι → E) (hw : Pairwise fun i j => ⟪w i, w j⟫_ℝ = 0) :
    ‖∑ i, a i • w i‖ ^ 2 = ∑ i, a i ^ 2 * ‖w i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  · intro j _ hji
    rw [real_inner_smul_left, real_inner_smul_right, hw (Ne.symm hji), mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Theorem 4.1, abstract form (exact global conformity defect).**

Let `P = K.starProjection` be an orthogonal projector and `W i` mutually
orthogonal subspaces, each mapped into itself by `P`. Pick one unit vector
`b i ∈ W i` per fiber and let `Π` be the orthogonal projector onto
`span {b i}`. Then
`‖(I − Π) P Π‖ = max_i ‖P b i‖ · ‖(I − P) b i‖`.
-/
theorem global_defect [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : Submodule ℝ E) (W : ι → Submodule ℝ E) (hW : Pairwise fun i j => W i ⟂ W j)
    (hKW : ∀ i, ∀ x ∈ W i, K.starProjection x ∈ W i)
    (b : ι → E) (hbW : ∀ i, b i ∈ W i) (hb : ∀ i, ‖b i‖ = 1) :
    ‖(1 - (Submodule.span ℝ (Set.range b)).starProjection) * K.starProjection *
        (Submodule.span ℝ (Set.range b)).starProjection‖ =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => ‖K.starProjection (b i)‖ * ‖b i - K.starProjection (b i)‖) := by
  classical
  set Q := (Submodule.span ℝ (Set.range b)).starProjection with hQdef
  set P := K.starProjection with hPdef
  set D := (1 - Q) * P * Q with hDdef
  -- the trial vectors are orthonormal
  have hon : Orthonormal ℝ b := ⟨hb, fun i j hij => (hW hij).inner_eq (hbW i) (hbW j)⟩
  have hQ : ∀ x, Q x = ∑ i, ⟪b i, x⟫_ℝ • b i := starProjection_span_orthonormal hon
  -- `Π P b i` only sees the `i`-th trial vector
  have hQP : ∀ i, Q (P (b i)) = ⟪b i, P (b i)⟫_ℝ • b i := by
    intro i
    rw [hQ]
    refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rw [(hW hki).inner_eq (hbW k) (hKW i _ (hbW i)), zero_smul]
  -- the per-fiber defect vectors
  set w : ι → E := fun i => P (b i) - ⟪b i, P (b i)⟫_ℝ • b i with hwdef
  have hwW : ∀ i, w i ∈ W i := fun i =>
    Submodule.sub_mem _ (hKW i _ (hbW i)) (Submodule.smul_mem _ _ (hbW i))
  have hwo : Pairwise fun i j => ⟪w i, w j⟫_ℝ = 0 := fun i j hij =>
    (hW hij).inner_eq (hwW i) (hwW j)
  -- `(I − Π) P Π` is block diagonal: it sends `x` to `∑ ⟪b i, x⟫ w i`
  have hD : ∀ x, D x = ∑ i, ⟪b i, x⟫_ℝ • w i := by
    intro x
    have hPQ : P (Q x) = ∑ i, ⟪b i, x⟫_ℝ • P (b i) := by
      rw [hQ x, map_sum]
      simp only [map_smul]
    have hQPQ : Q (P (Q x)) = ∑ i, ⟪b i, x⟫_ℝ • (⟪b i, P (b i)⟫_ℝ • b i) := by
      rw [hPQ, map_sum]
      simp only [map_smul, hQP]
    simp only [hDdef, mul_apply_eq_comp, sub_apply,
      one_apply_eq_self]
    rw [hQPQ, hPQ, ← Finset.sum_sub_distrib]
    simp only [hwdef, smul_sub]
  set M := Finset.univ.sup' Finset.univ_nonempty (fun i => ‖w i‖) with hMdef
  have hwM : ∀ i, ‖w i‖ ≤ M := fun i =>
    Finset.le_sup' (fun i => ‖w i‖) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hwM (Classical.arbitrary ι))
  -- upper bound, by Pythagoras and Bessel
  have hle : ‖D‖ ≤ M := by
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun x => ?_
    have hbessel : ∑ i, ⟪b i, x⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 := by
      have := hon.sum_inner_products_le x (s := Finset.univ)
      simpa [Real.norm_eq_abs, sq_abs] using this
    have h1 : ‖D x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
      rw [hD, norm_sq_sum_smul_of_pairwise_inner_eq_zero _ _ hwo, mul_pow]
      calc ∑ i, ⟪b i, x⟫_ℝ ^ 2 * ‖w i‖ ^ 2 ≤ ∑ i, ⟪b i, x⟫_ℝ ^ 2 * M ^ 2 := by
            gcongr with i
            exact hwM i
        _ = M ^ 2 * ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ M ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left hbessel (sq_nonneg M)
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1
  -- lower bound: test on the trial vectors themselves
  have hDb : ∀ i, D (b i) = w i := by
    intro i
    rw [hD, Finset.sum_eq_single i]
    · rw [real_inner_self_eq_norm_sq, hb i, one_pow, one_smul]
    · intro k _ hki
      rw [hon.2 hki, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hge : M ≤ ‖D‖ := by
    refine Finset.sup'_le _ _ fun i _ => ?_
    calc ‖w i‖ = ‖D (b i)‖ := by rw [hDb]
      _ ≤ ‖D‖ * ‖b i‖ := D.le_opNorm _
      _ = ‖D‖ := by rw [hb i, mul_one]
  rw [le_antisymm hle hge, hMdef]
  exact Finset.sup'_congr _ rfl fun i _ => fiber_defect_norm K (hb i)

/-- **Corollary 4.2, abstract form (exact conformity).** If the orthogonal
projector `P = K.starProjection` maps the trial space `V` into itself, the
conformity defect `(I − Π_V) P Π_V` vanishes identically. -/
theorem defect_eq_zero_of_invariant [FiniteDimensional ℝ E] (K V : Submodule ℝ E)
    (hKV : ∀ x ∈ V, K.starProjection x ∈ V) :
    (1 - V.starProjection) * K.starProjection * V.starProjection = 0 := by
  ext x
  simp only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, zero_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (hKV _ (V.starProjection_apply_mem x)),
    sub_self]

end KineticBalance
