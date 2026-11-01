/-
Axiom audit. This file is not a build target. After `lake build`, run

    lake env lean AxiomCheck.lean

Every line should print `[propext, Classical.choice, Quot.sound]`. In
particular, no line may mention `sorryAx`.
-/
import KineticBalance

-- Proposition 2.1
#print axioms KineticBalance.dirac_isDiracFiber
#print axioms KineticBalance.dirac_fiber_isOrtho
#print axioms KineticBalance.energy_eq
#print axioms KineticBalance.IsDiracFiber.apply_vPlus
#print axioms KineticBalance.IsDiracFiber.apply_vMinus
-- spectral projectors
#print axioms KineticBalance.specProjPos_apply_of_pos
#print axioms KineticBalance.specProjPos_apply_of_nonpos
#print axioms KineticBalance.specProjNeg_apply_of_neg
#print axioms KineticBalance.specProjNeg_apply_of_nonneg
#print axioms KineticBalance.specProjPos_add_specProjNeg
-- Theorem 3.1
#print axioms KineticBalance.IsDiracFiber.leakage_trialDir
#print axioms KineticBalance.dirac_leakage
#print axioms KineticBalance.Family.leak_bal_eq_key
-- Theorem 4.1
#print axioms KineticBalance.fiber_defect_norm
#print axioms KineticBalance.global_defect
#print axioms KineticBalance.IsDiracFiber.defect_factor_pos
#print axioms KineticBalance.IsDiracFiber.defect_factor_neg
#print axioms KineticBalance.dirac_global_defect_pos
#print axioms KineticBalance.dirac_global_defect_neg
-- Corollary 4.2
#print axioms KineticBalance.defect_eq_zero_of_invariant
#print axioms KineticBalance.dirac_dkb_defect_pos
#print axioms KineticBalance.dirac_dkb_defect_neg
-- Theorem 5.1(a)
#print axioms KineticBalance.IsDiracFiber.rayleigh_trialUnit
#print axioms KineticBalance.dirac_galerkin_eigen
#print axioms KineticBalance.dirac_anti_galerkin_in_gap
#print axioms KineticBalance.dirac_anti_galerkin_spurious
#print axioms KineticBalance.dirac_bal_galerkin_above_gap
#print axioms KineticBalance.norm_diracOp_sq
#print axioms KineticBalance.diracOp_eigenvalue_abs_ge
