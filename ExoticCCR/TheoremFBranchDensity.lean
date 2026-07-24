/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardBranch
import ExoticCCR.TheoremFJacobianFDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Algebraic density and branch-supported deficiency data

This module records the absolute algebraic Jacobian value of the anchor map and
defines the candidate deficiency density on the positive forward branch.  It
does not assert a change-of-variables theorem, ambient `L²` membership, or an
adjoint-domain statement.
-/

noncomputable section

open Function MeasureTheory MvPolynomial Set

namespace ExoticCCR

/-- Coordinates `((a, c), τ)` as a function on `Fin 3`, in the order
`0 ↦ a`, `1 ↦ c`, `2 ↦ τ`. -/
def paramToFin3 : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => ![p.1.1, p.1.2, p.2]
      invFun := fun v => ((v 0, v 1), v 2)
      left_inv := by
        rintro ⟨⟨a, c⟩, τ⟩
        rfl
      right_inv := by
        intro v
        funext i
        fin_cases i <;> rfl
      map_add' := by
        intro p q
        funext i
        fin_cases i <;> rfl
      map_smul' := by
        intro r p
        funext i
        fin_cases i <;> rfl }

/-- A parameter-space map transported to standard `Fin 3` coordinates. -/
def asFin3Map (g : ((ℝ × ℝ) × ℝ) → Fin 3 → ℝ) :
    (Fin 3 → ℝ) → Fin 3 → ℝ :=
  g ∘ paramToFin3.symm

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

/-- On the open branch domain, the branch reconstruction is differentiable in
the ambient finite-dimensional real spaces. -/
theorem ForwardBranchOpen.differentiableAt_branchMap (O : ForwardBranchOpen)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.W) :
    DifferentiableAt ℝ O.germ.branchMap p := by
  exact ((O.contDiff_branchMap p hp).differentiableWithinAt (by simp)).differentiableAt
    (O.isOpen_W.mem_nhds hp)

/-- Chain rule for the polynomial anchor evaluated on the local branch. -/
theorem ForwardBranchOpen.hasFDerivAt_evalMap_comp_branchMap
    (O : ForwardBranchOpen) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.W) :
    HasFDerivAt (evalMap (F ℝ) ∘ O.germ.branchMap)
      ((evalJacobianF (O.germ.branchMap p)).comp
        (fderiv ℝ O.germ.branchMap p)) p := by
  exact (hasFDerivAt_evalMap_F (O.germ.branchMap p)).comp p
    (O.differentiableAt_branchMap hp).hasFDerivAt

/-- The derivative of the anchor after the branch map is the composition of
the two derivatives. -/
theorem ForwardBranchOpen.hasFDerivAt_comp (O : ForwardBranchOpen)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.W) :
    fderiv ℝ (evalMap (F ℝ) ∘ O.germ.branchMap) p =
      (fderiv ℝ (evalMap (F ℝ)) (O.germ.branchMap p)).comp
        (fderiv ℝ O.germ.branchMap p) := by
  rw [fderiv_evalMap_F]
  exact (O.hasFDerivAt_evalMap_comp_branchMap hp).fderiv

/-- Local analytic chain identity: differentiating the branch reconstruction
identity on the open domain gives the derivative of the displayed target map. -/
theorem ForwardBranchOpen.fderiv_F_comp_branchMap_eq_fderiv_targetMap
    (O : ForwardBranchOpen) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.W) :
    (fderiv ℝ (evalMap (F ℝ)) (O.germ.branchMap p)).comp
        (fderiv ℝ O.germ.branchMap p) =
      fderiv ℝ O.targetMap p := by
  rw [← O.hasFDerivAt_comp hp]
  apply Filter.EventuallyEq.fderiv_eq
  exact Set.EqOn.eventuallyEq_of_mem
    (fun x hx => O.evalMap_branch_eq_targetMap hx)
    (O.isOpen_W.mem_nhds hp)

/-- Absolute local Jacobian identity in the standard `Fin 3` coordinates.
This is a determinant consequence of the local chain identity and
`det D F = -2`; it is not a measure change-of-variables theorem. -/
theorem ForwardBranchOpen.abs_det_fderiv_branchMap_eq
    (O : ForwardBranchOpen) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.W) :
    |((fderiv ℝ O.germ.branchMap p).comp paramToFin3.symm.toContinuousLinearMap).det| =
      |((fderiv ℝ O.targetMap p).comp paramToFin3.symm.toContinuousLinearMap).det| / 2 := by
  have hchain := O.fderiv_F_comp_branchMap_eq_fderiv_targetMap hp
  have hcomp :
      (fderiv ℝ (evalMap (F ℝ)) (O.germ.branchMap p)).comp
          ((fderiv ℝ O.germ.branchMap p).comp paramToFin3.symm.toContinuousLinearMap) =
        (fderiv ℝ O.targetMap p).comp paramToFin3.symm.toContinuousLinearMap := by
    ext v i
    exact congrFun (congrArg (fun L => L (paramToFin3.symm v)) hchain) i
  have hdet := congrArg ContinuousLinearMap.det hcomp
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ← ContinuousLinearMap.det] at hdet
  rw [det_fderiv_evalMap_F] at hdet
  calc
    _ = |-2 * ((fderiv ℝ O.germ.branchMap p).comp
        paramToFin3.symm.toContinuousLinearMap).det| / 2 := by
      rw [abs_mul, abs_neg]
      norm_num
    _ = _ := by rw [hdet]

/-- Candidate deficiency density in branch parameters. -/
def ForwardBranchOpen.deficiencyDensity (_O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  χ p.1 * Complex.exp (-p.2 ^ 2)

/-- The squared norm of the parameter-space deficiency density is integrable.
This is an ambient parameter-space estimate; restricting it to `Wpos` is an
immediate corollary below and requires no change of variables. -/
theorem ForwardBranchOpen.integrable_deficiencyDensity (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => ‖O.deficiencyDensity χ p‖ ^ 2)
      (volume : Measure ((ℝ × ℝ) × ℝ)) := by
  have hχ2 : Integrable (fun x : ℝ × ℝ => ‖χ x‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hχ.aestronglyMeasurable).mp
      (hχ.memLp_of_hasCompactSupport hχc)
  have hgauss : Integrable
      (fun τ : ℝ => ‖Complex.exp (-(τ : ℂ) ^ 2)‖ ^ 2) := by
    convert integrable_exp_neg_mul_sq (b := 2) (by norm_num) using 1
    ext τ
    rw [Complex.norm_exp]
    rw [pow_two, ← Real.exp_add]
    congr 1
    have hre : ((τ : ℂ) ^ 2).re = τ ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    rw [Complex.neg_re, hre]
    ring
  rw [Measure.volume_eq_prod]
  simpa [ForwardBranchOpen.deficiencyDensity, norm_mul, mul_pow] using
    hχ2.mul_prod hgauss

/-- The parameter-space deficiency density remains square-integrable after
restriction to the positive branch domain. -/
theorem ForwardBranchOpen.integrableOn_deficiencyDensity_Wpos (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    IntegrableOn (fun p : (ℝ × ℝ) × ℝ => ‖O.deficiencyDensity χ p‖ ^ 2) O.Wpos
      (volume : Measure ((ℝ × ℝ) × ℝ)) :=
  (O.integrable_deficiencyDensity χ hχ hχc).integrableOn

/-- The candidate density is in `L²` on the full parameter space.  This does
not imply `L²` membership of its branch-image pushforward without a
measure-theoretic change-of-variables theorem. -/
theorem ForwardBranchOpen.memLp_deficiencyDensity (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (O.deficiencyDensity χ) 2 (volume : Measure ((ℝ × ℝ) × ℝ)) := by
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr
    (O.integrable_deficiencyDensity χ hχ hχc)
  apply Continuous.aestronglyMeasurable
  unfold ForwardBranchOpen.deficiencyDensity
  fun_prop

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
