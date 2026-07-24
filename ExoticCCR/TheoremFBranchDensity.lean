/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardBranch

/-!
# Algebraic density and branch-supported deficiency data

This module records the absolute algebraic Jacobian value of the anchor map and
defines the candidate deficiency density on the positive forward branch.  It
does not assert a change-of-variables theorem, ambient `L²` membership, or an
adjoint-domain statement.
-/

noncomputable section

open Function MvPolynomial Set

namespace ExoticCCR

/-- The evaluated algebraic Jacobian determinant of `F` has absolute value `2`
at every real point. -/
theorem abs_eval_jacobianDet_F (q : Fin 3 → ℝ) :
    |eval q (jacobianDet (F ℝ))| = 2 := by
  rw [jacobianDet_F]
  norm_num

/-- The reciprocal absolute algebraic Jacobian factor associated with `F`. -/
def flowboxDensityFactor : ℝ := 1 / 2

/-- The displayed factor is the reciprocal of the absolute evaluated
algebraic Jacobian determinant.  This is an algebraic identity, not by itself a
measure change-of-variables theorem. -/
theorem flowboxDensityFactor_eq_inverse_abs_eval_jacobianDet_F (q : Fin 3 → ℝ) :
    flowboxDensityFactor = 1 / |eval q (jacobianDet (F ℝ))| := by
  rw [abs_eval_jacobianDet_F]
  norm_num [flowboxDensityFactor]

/-- The target coordinates `(a, β(a,c)-τ², c)` of the branch reconstruction. -/
def ForwardBranchOpen.targetMap (O : ForwardBranchOpen)
    (p : (ℝ × ℝ) × ℝ) : Fin 3 → ℝ :=
  ![p.1.1, O.germ.sCoord p, p.1.2]

/-- The branch map is a right inverse of `F` onto its displayed target
coordinates on the punctured domain. -/
theorem ForwardBranchOpen.evalMap_branch_eq_targetMap (O : ForwardBranchOpen)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.W) :
    evalMap (F ℝ) (O.germ.branchMap p) = O.targetMap p := by
  exact O.evalMap_branch hp

/-- Along the branch parameterization, `s-β=-τ²`. -/
theorem ForwardBranchOpen.sCoord_sub_beta (O : ForwardBranchOpen)
    (p : (ℝ × ℝ) × ℝ) :
    O.germ.sCoord p - O.germ.β p.1 = -p.2 ^ 2 := by
  simp [ForwardBranchGerm.sCoord]

/-- Candidate deficiency density in branch parameters. -/
def ForwardBranchOpen.deficiencyDensity (_O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  χ p.1 * Complex.exp (-p.2 ^ 2)

/-- The branch-supported candidate function, extended by zero away from the
positive branch image.  Injectivity on `Wpos` makes the selected value
independent of the inverse implementation. -/
def ForwardBranchOpen.uMinus (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ) :
    (Fin 3 → ℝ) → ℂ := by
  classical
  exact fun q =>
    if q ∈ O.germ.branchMap '' O.Wpos then
      O.deficiencyDensity χ (Function.invFunOn O.germ.branchMap O.Wpos q)
    else
      0

/-- On the positive branch image, `uMinus` recovers its parameter density. -/
theorem ForwardBranchOpen.uMinus_on_image (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.Wpos) :
    O.uMinus χ (O.germ.branchMap p) = O.deficiencyDensity χ p := by
  rw [uMinus, if_pos ⟨p, hp, rfl⟩]
  rw [O.branchMap_injOn_Wpos.leftInvOn_invFunOn hp]

/-- Away from the positive branch image, `uMinus` is zero. -/
theorem ForwardBranchOpen.uMinus_off_image (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) {q : Fin 3 → ℝ}
    (hq : q ∉ O.germ.branchMap '' O.Wpos) :
    O.uMinus χ q = 0 := by
  simp [uMinus, hq]

end ExoticCCR
