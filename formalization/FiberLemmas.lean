/-
Machine-checked core identities of the fiber analysis
(companion to "Exact fiber analysis of kinetic-balance spectral
pollution for the radial Dirac operator").

Everything below is an identity or an inequality **over the reals**.
No statement about matrices, projectors, operator norms or spectra is
formalized: where the paper's proof reduces such a statement to a
scalar identity, it is that scalar identity which is checked here.
`SCOPE.md` in this folder is the authoritative inventory and states
explicitly what is NOT covered.  There is no `sorry` and no added
`axiom`.

Notation: `t` is the fiber parameter, `w = √(1+4t²)`, `ρ = 2t/(1+w)`,
`c` the speed of light, `R_bal = c²(1+3t²)/(1+t²)` and
`R_anti = c²(5t²−1)/(1+t²)` the fiber Rayleigh values of Eq. (rayleigh).

Auxiliary
  `w_sq`, `w_pos`, `one_lt_w`  : facts about w = √(1+4t²)
  `rho_nonneg`                 : ρ ≥ 0 for t ≥ 0

Theorem 3.1 (per-mode leakage laws)
  1. `key_identity`     : t − ρ = 4t³/(1+w)²
                          (the exact balanced-leakage numerator, Eq. (key))
  2. `rho_lt`           : ρ < t for t > 0 (resolves the absolute values)
  3. `l_spl_eq`         : ℓ(u_spl)  = ρ/√(1+ρ²)                  Eq. (lspl)
  4. `l_bal_eq_l_pos`   : ℓ(u_bal)  = ℓ(u_pos)                   Eq. (lbal)
  5. `l_anti_eq`        : ℓ(u_anti) = (t+ρ)/√((1+ρ²)(1+t²))      Eq. (lanti)

Theorem 4.1 (exact global defect) — the two scalar steps of its proof
  6. `fiber_pythagoras` : ⟨v₊,b⟩² + ⟨v₋,b⟩² = ‖b‖², i.e. g² = 1 − ℓ²
  7. `defect_identity`  : g²(1 − 2g² + g²) = g²(1 − g²)
                          (per-fiber defect, scalar form; NOT the norm
                           statement ‖(I−bbᵀ)Λ₊b‖² = g²(1−g²))

Theorem 5.1(a) (pollution dichotomy)
  8.  `bal_above_gap`        : R_bal − c² = 2c²t²/(1+t²)
  9.  `bal_above_gap_nonneg` : R_bal − c² ≥ 0
  10. `anti_below_gap`       : c² − R_anti = c²(2−4t²)/(1+t²)
  11. `anti_above_bottom`    : R_anti + c² = 6c²t²/(1+t²)
  12. `anti_in_gap`          : R_anti lies strictly inside (−c², c²)
                               iff 0 < t² < 1/2
  13. `anti_strict_mono`     : R_anti is strictly increasing in t ≥ 0
                               (the gap sweep, Remark after Thm 5.1)
  14. `anti_midgap`          : 5(1/√5)² − 1 = 0, the mid-gap crossing
                               at t = 1/√5
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Real

namespace FeastLemmas

variable {t : ℝ}

/-- Auxiliary facts about w = √(1+4t²). -/
lemma w_sq (t : ℝ) : (Real.sqrt (1 + 4 * t ^ 2)) ^ 2 = 1 + 4 * t ^ 2 := by
  rw [sq_sqrt]; positivity

lemma w_pos (t : ℝ) : 0 < Real.sqrt (1 + 4 * t ^ 2) := by
  apply Real.sqrt_pos.mpr; positivity

lemma one_lt_w (ht : 0 < t) : 1 < Real.sqrt (1 + 4 * t ^ 2) := by
  have h : (1 : ℝ) < 1 + 4 * t ^ 2 := by nlinarith
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt (1 + 4 * t ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h

/-- The key algebraic identity behind the exact balanced leakage
    (Theorem 3.1): with w = √(1+4t²) and ρ = 2t/(1+w),
    t − ρ = 4t³/(1+w)². -/
theorem key_identity (t : ℝ) :
    t - 2 * t / (1 + Real.sqrt (1 + 4 * t ^ 2)) =
    4 * t ^ 3 / (1 + Real.sqrt (1 + 4 * t ^ 2)) ^ 2 := by
  set w := Real.sqrt (1 + 4 * t ^ 2) with hw
  have hw2 : w ^ 2 = 1 + 4 * t ^ 2 := w_sq t
  have hwpos : 0 < w := w_pos t
  have h1w : (1 + w) ≠ 0 := by positivity
  field_simp
  linear_combination t * hw2

/-- ρ < t for t > 0: the balanced trial ratio overshoots the exact
    eigenvector ratio, which fixes the sign in the leakage formula. -/
theorem rho_lt (ht : 0 < t) :
    2 * t / (1 + Real.sqrt (1 + 4 * t ^ 2)) < t := by
  have hw := one_lt_w ht
  have h2 : (2 : ℝ) < 1 + Real.sqrt (1 + 4 * t ^ 2) := by linarith
  have hpos : (0 : ℝ) < 1 + Real.sqrt (1 + 4 * t ^ 2) := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- Per-fiber defect identity (Theorem 4.1): for unit vectors the
    squared norm of (I−bbᵀ)Λ₊b reduces to g²(1−g²) with g = ⟨v₊,b⟩.
    Scalar form: g²·(1 − 2g² + g²·1) = g²(1−g²). -/
theorem defect_identity (g : ℝ) :
    g ^ 2 * (1 - 2 * g ^ 2 + g ^ 2 * 1) = g ^ 2 * (1 - g ^ 2) := by
  ring

/-- Pollution dichotomy, part (a) of Theorem 5.1: the anti-balanced
    fiber Rayleigh value R = c²(5t²−1)/(1+t²) lies strictly inside the
    gap (−c², c²) if and only if 0 < t and t² < 1/2. -/
theorem anti_in_gap (c t : ℝ) (hc : 0 < c) :
    (-c ^ 2 < c ^ 2 * (5 * t ^ 2 - 1) / (1 + t ^ 2) ∧
      c ^ 2 * (5 * t ^ 2 - 1) / (1 + t ^ 2) < c ^ 2) ↔
    (0 < t ^ 2 ∧ t ^ 2 < 1 / 2) := by
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra h
      have h' : t ^ 2 <= 0 := not_lt.mp h
      have ht0 : t ^ 2 = 0 := le_antisymm h' (sq_nonneg t)
      rw [div_lt_iff₀ hden] at hhi
      rw [lt_div_iff₀ hden] at hlo
      nlinarith
    · rw [div_lt_iff₀ hden] at hhi
      nlinarith
  · rintro ⟨ht0, ht2⟩
    constructor
    · rw [lt_div_iff₀ hden]
      nlinarith
    · rw [div_lt_iff₀ hden]
      nlinarith

/-- The anti-balanced Rayleigh value crosses the exact gap midpoint at
    t = 1/√5: 5t² − 1 = 0 there. -/
theorem anti_midgap :
    5 * (1 / Real.sqrt 5) ^ 2 - 1 = 0 := by
  have h5 : (Real.sqrt 5) ^ 2 = 5 := by
    rw [sq_sqrt]; norm_num
  have hpos : Real.sqrt 5 ≠ 0 := by
    have := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
    exact ne_of_gt this
  field_simp
  nlinarith [h5]
/-! ### Closed forms of the per-mode leakages (Theorem 3.1)

In the fiber coordinates of Proposition 2.1 the normalized eigenvectors
of the fiber matrix `h(2ct)` are `v₊ = (1, ρ)/√(1+ρ²)` and
`v₋ = (-ρ, 1)/√(1+ρ²)`, with `ρ = 2t/(1+w)` and `w = √(1+4t²)`.  The
leakage `ℓ(u)` of a trial direction is the absolute value of the inner
product of the *normalized* trial vector with the wrong-sector
eigenvector.  The lemmas below record, as identities between real
numbers with the two-component inner products written out explicitly,
the closed forms printed in Theorem 3.1. -/

/-- `ρ ≥ 0` whenever `t ≥ 0`.  This is what resolves the absolute value
    in the split-family leakage `ℓ(u_spl)`. -/
lemma rho_nonneg (ht : 0 ≤ t) :
    0 ≤ 2 * t / (1 + Real.sqrt (1 + 4 * t ^ 2)) := by
  have hw : (0 : ℝ) < 1 + Real.sqrt (1 + 4 * t ^ 2) := by
    have := w_pos t
    linarith
  exact div_nonneg (by linarith) (le_of_lt hw)

/-- Split-family leakage, Eq. (lspl) of Theorem 3.1:
    `ℓ(u_spl) = |⟨v₋, (1,0)⟩| = ρ/√(1+ρ²)`.  The trial vector `(1,0)`
    is already normalized. -/
theorem l_spl_eq (ρ : ℝ) (hρ : 0 ≤ ρ) :
    |(-ρ) * 1 + 1 * 0| / Real.sqrt (1 + ρ ^ 2)
      = ρ / Real.sqrt (1 + ρ ^ 2) := by
  rw [show (-ρ) * 1 + 1 * 0 = -ρ by ring, abs_neg, abs_of_nonneg hρ]

/-- Anti-balanced leakage, Eq. (lanti) of Theorem 3.1:
    `ℓ(u_anti) = |⟨v₊, (t,1)⟩|/√(1+t²) = (t+ρ)/(√(1+ρ²)√(1+t²))`. -/
theorem l_anti_eq (t ρ : ℝ) (ht : 0 ≤ t) (hρ : 0 ≤ ρ) :
    |1 * t + ρ * 1| / (Real.sqrt (1 + ρ ^ 2) * Real.sqrt (1 + t ^ 2))
      = (t + ρ) / (Real.sqrt (1 + ρ ^ 2) * Real.sqrt (1 + t ^ 2)) := by
  rw [show (1 : ℝ) * t + ρ * 1 = t + ρ by ring,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ t + ρ)]

/-- Theorem 3.1 asserts `ℓ(u_bal) = ℓ(u_pos)`.  In fiber coordinates
    the two inner products are `(t−ρ)/√(1+ρ²)` (balanced, against `v₋`)
    and `(ρ−t)/√(1+ρ²)` (positronic, against `v₊`); the leakages agree
    because they are the absolute values of opposite numbers. -/
theorem l_bal_eq_l_pos (t ρ : ℝ) :
    |(-ρ) * 1 + 1 * t| / (Real.sqrt (1 + ρ ^ 2) * Real.sqrt (1 + t ^ 2))
      = |1 * (-t) + ρ * 1|
          / (Real.sqrt (1 + ρ ^ 2) * Real.sqrt (1 + t ^ 2)) := by
  rw [show (-ρ) * 1 + 1 * t = -(1 * (-t) + ρ * 1) by ring, abs_neg]

/-- Fiber Pythagoras, the step `g² = 1 − ℓ²` in the proof of
    Theorem 4.1: the fiber eigenbasis `v±` is orthonormal, so for any
    `b = (x,y)` one has `⟨v₊,b⟩² + ⟨v₋,b⟩² = ‖b‖²`. -/
theorem fiber_pythagoras (ρ x y : ℝ) :
    ((x + ρ * y) / Real.sqrt (1 + ρ ^ 2)) ^ 2
      + ((-ρ * x + y) / Real.sqrt (1 + ρ ^ 2)) ^ 2
      = x ^ 2 + y ^ 2 := by
  have hpos : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
  have hne : (1 : ℝ) + ρ ^ 2 ≠ 0 := ne_of_gt hpos
  have hs : (Real.sqrt (1 + ρ ^ 2)) ^ 2 = 1 + ρ ^ 2 := by
    rw [sq_sqrt]; positivity
  rw [div_pow, div_pow, hs, ← add_div, div_eq_iff hne]
  ring

/-! ### The fiber Rayleigh values (Theorem 5.1(a))

`R_bal = c²(1+3t²)/(1+t²)` and `R_anti = c²(5t²−1)/(1+t²)` are the
free Rayleigh values of Eq. (rayleigh).  Part (a) of Theorem 5.1
consists of the four identities below together with `anti_in_gap` and
`anti_midgap`. -/

/-- Theorem 5.1(a), first half: the balanced fiber Rayleigh value sits
    at or above the top of the gap, with the exact excess
    `R_bal − c² = 2c²t²/(1+t²)`. -/
theorem bal_above_gap (c t : ℝ) :
    c ^ 2 * (1 + 3 * t ^ 2) / (1 + t ^ 2) - c ^ 2
      = 2 * c ^ 2 * t ^ 2 / (1 + t ^ 2) := by
  have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Theorem 5.1(a), first half, sign: `R_bal − c² ≥ 0`, so the balanced
    family never produces a Rayleigh value inside the gap. -/
theorem bal_above_gap_nonneg (c t : ℝ) :
    0 ≤ c ^ 2 * (1 + 3 * t ^ 2) / (1 + t ^ 2) - c ^ 2 := by
  rw [bal_above_gap]
  positivity

/-- Theorem 5.1(a), displayed in its proof: the distance of the
    anti-balanced Rayleigh value from the top of the gap,
    `c² − R_anti = c²(2−4t²)/(1+t²)`. -/
theorem anti_below_gap (c t : ℝ) :
    c ^ 2 - c ^ 2 * (5 * t ^ 2 - 1) / (1 + t ^ 2)
      = c ^ 2 * (2 - 4 * t ^ 2) / (1 + t ^ 2) := by
  have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Theorem 5.1(a), displayed in its proof: the distance of the
    anti-balanced Rayleigh value from the bottom of the gap,
    `R_anti + c² = 6c²t²/(1+t²)`. -/
theorem anti_above_bottom (c t : ℝ) :
    c ^ 2 * (5 * t ^ 2 - 1) / (1 + t ^ 2) + c ^ 2
      = 6 * c ^ 2 * t ^ 2 / (1 + t ^ 2) := by
  have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The anti-balanced Rayleigh value *sweeps* the gap: it is strictly
    increasing in `t ≥ 0` (the Remark following Theorem 5.1). -/
theorem anti_strict_mono (c : ℝ) (hc : 0 < c) {t₁ t₂ : ℝ}
    (h1 : 0 ≤ t₁) (h12 : t₁ < t₂) :
    c ^ 2 * (5 * t₁ ^ 2 - 1) / (1 + t₁ ^ 2)
      < c ^ 2 * (5 * t₂ ^ 2 - 1) / (1 + t₂ ^ 2) := by
  have hd1 : (0 : ℝ) < 1 + t₁ ^ 2 := by positivity
  have hd2 : (0 : ℝ) < 1 + t₂ ^ 2 := by positivity
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hs : t₁ ^ 2 < t₂ ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith [mul_pos hc2 (sub_pos.mpr hs)]

end FeastLemmas
