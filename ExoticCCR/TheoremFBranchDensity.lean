/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardBranch
import ExoticCCR.TheoremFJacobianFDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.Jacobian
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
open scoped ENNReal

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

/-- The positive branch domain in standard `Fin 3` coordinates. -/
def ForwardBranchOpen.WposFin3 (O : ForwardBranchOpen) : Set (Fin 3 → ℝ) :=
  paramToFin3.symm ⁻¹' O.Wpos

/-- The positive branch domain is open. -/
theorem ForwardBranchOpen.isOpen_Wpos (O : ForwardBranchOpen) : IsOpen O.Wpos := by
  exact O.isOpen_W.inter (isOpen_lt continuous_const continuous_snd)

/-- The positive branch domain is measurable. -/
theorem ForwardBranchOpen.measurableSet_Wpos (O : ForwardBranchOpen) :
    MeasurableSet O.Wpos :=
  O.isOpen_Wpos.measurableSet

/-- The positive branch domain remains open in standard `Fin 3` coordinates. -/
theorem ForwardBranchOpen.isOpen_WposFin3 (O : ForwardBranchOpen) :
    IsOpen O.WposFin3 := by
  exact O.isOpen_Wpos.preimage paramToFin3.symm.continuous

/-- The positive branch domain is measurable in standard `Fin 3` coordinates. -/
theorem ForwardBranchOpen.measurableSet_WposFin3 (O : ForwardBranchOpen) :
    MeasurableSet O.WposFin3 :=
  O.isOpen_WposFin3.measurableSet

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

/-- The branch reconstruction has its ambient derivative as a derivative within
the positive branch domain. -/
theorem ForwardBranchOpen.hasFDerivWithinAt_branchMap_Wpos
    (O : ForwardBranchOpen) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.Wpos) :
    HasFDerivWithinAt O.germ.branchMap (fderiv ℝ O.germ.branchMap p) O.Wpos p :=
  (O.differentiableAt_branchMap hp.1).hasFDerivAt.hasFDerivWithinAt

/-- In standard coordinates, the branch derivative is obtained by composing
with the inverse parameter-coordinate equivalence. -/
theorem ForwardBranchOpen.hasFDerivWithinAt_asFin3Map_WposFin3
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    HasFDerivWithinAt (asFin3Map O.germ.branchMap)
      ((fderiv ℝ O.germ.branchMap (paramToFin3.symm v)).comp
        paramToFin3.symm.toContinuousLinearMap) O.WposFin3 v := by
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  exact ((O.differentiableAt_branchMap hp.1).hasFDerivAt.comp v
    paramToFin3.symm.toContinuousLinearMap.hasFDerivAt).hasFDerivWithinAt

/-- The standard-coordinate branch map is injective on its positive domain. -/
theorem ForwardBranchOpen.asFin3Map_injOn_WposFin3 (O : ForwardBranchOpen) :
    Set.InjOn (asFin3Map O.germ.branchMap) O.WposFin3 := by
  intro v hv w hw hvw
  apply paramToFin3.symm.injective
  exact O.branchMap_injOn_Wpos hv hw hvw

/-- The image in standard coordinates is exactly the original positive branch image. -/
theorem ForwardBranchOpen.image_asFin3Map_WposFin3 (O : ForwardBranchOpen) :
    asFin3Map O.germ.branchMap '' O.WposFin3 = O.germ.branchMap '' O.Wpos := by
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨paramToFin3.symm v, hv, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨paramToFin3 p, by simpa [ForwardBranchOpen.WposFin3], by
      simp [asFin3Map]⟩

/-- The positive branch image is measurable. -/
theorem ForwardBranchOpen.measurableSet_image_branchMap_Wpos (O : ForwardBranchOpen) :
    MeasurableSet (O.germ.branchMap '' O.Wpos) := by
  rw [← O.image_asFin3Map_WposFin3]
  exact measurable_image_of_fderivWithin O.measurableSet_WposFin3
    (fun v hv => O.hasFDerivWithinAt_asFin3Map_WposFin3 hv)
    O.asFin3Map_injOn_WposFin3

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

/-- The target map in standard coordinates is differentiable on the branch domain. -/
theorem ForwardBranchOpen.differentiableAt_asFin3Map_targetMap
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    DifferentiableAt ℝ (asFin3Map O.targetMap) v := by
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  have ht : DifferentiableAt ℝ O.targetMap (paramToFin3.symm v) := by
    apply (O.hasFDerivAt_evalMap_comp_branchMap hp.1).differentiableAt.congr_of_eventuallyEq
    exact (Set.EqOn.eventuallyEq_of_mem
      (fun x hx => (O.evalMap_branch_eq_targetMap hx).symm)
      (O.isOpen_W.mem_nhds hp.1))
  exact ht.comp v paramToFin3.symm.differentiableAt

/-- The first target coordinate has derivative `h ↦ h 0`. -/
theorem ForwardBranchOpen.fderiv_asFin3Map_targetMap_apply_zero
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) (h : Fin 3 → ℝ) :
    fderiv ℝ (asFin3Map O.targetMap) v h 0 = h 0 := by
  have hd := O.differentiableAt_asFin3Map_targetMap hv
  have hc := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L h) (fderiv_apply hd 0)
  have hc' : fderiv ℝ (asFin3Map O.targetMap) v h 0 =
      fderiv ℝ (fun x => asFin3Map O.targetMap x 0) v h := by
    simpa using hc.symm
  rw [hc']
  let e0 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hp : HasFDerivAt (fun x : Fin 3 → ℝ => x 0) e0 v := e0.hasFDerivAt
  simpa [asFin3Map, ForwardBranchOpen.targetMap, paramToFin3, e0] using
    congrArg (fun L => L h) hp.fderiv

/-- The third target coordinate has derivative `h ↦ h 1`. -/
theorem ForwardBranchOpen.fderiv_asFin3Map_targetMap_apply_two
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) (h : Fin 3 → ℝ) :
    fderiv ℝ (asFin3Map O.targetMap) v h 2 = h 1 := by
  have hd := O.differentiableAt_asFin3Map_targetMap hv
  have hc := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L h) (fderiv_apply hd 2)
  have hc' : fderiv ℝ (asFin3Map O.targetMap) v h 2 =
      fderiv ℝ (fun x => asFin3Map O.targetMap x 2) v h := by
    simpa using hc.symm
  rw [hc']
  let e1 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have hp : HasFDerivAt (fun x : Fin 3 → ℝ => x 1) e1 v := e1.hasFDerivAt
  simpa [asFin3Map, ForwardBranchOpen.targetMap, paramToFin3, e1] using
    congrArg (fun L => L h) hp.fderiv

/-- In the pure `τ` direction, the middle target coordinate has derivative `-2τ`. -/
theorem ForwardBranchOpen.fderiv_asFin3Map_targetMap_apply_one_basis_two
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    fderiv ℝ (asFin3Map O.targetMap) v (Pi.single 2 1) 1 = -2 * v 2 := by
  have hd := O.differentiableAt_asFin3Map_targetMap hv
  have hc := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (Pi.single 2 1))
    (fderiv_apply hd 1)
  have hc' : fderiv ℝ (asFin3Map O.targetMap) v (Pi.single 2 1) 1 =
      fderiv ℝ (fun x => asFin3Map O.targetMap x 1) v (Pi.single 2 1) := by
    simpa using hc.symm
  rw [hc']
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  have hβ : HasFDerivAt O.germ.β (fderiv ℝ O.germ.β (v 0, v 1)) (v 0, v 1) :=
    ((O.germ.contDiff_β.contDiffAt
      (O.germ.isOpen_U.mem_nhds (O.germ.proj_mem _ (O.subset_V hp.1)))).differentiableAt
        (by simp)).hasFDerivAt
  let e0 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let e1 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  let e2 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  have hpair : HasFDerivAt (fun x : Fin 3 → ℝ => (x 0, x 1))
      (e0.prod e1) v := e0.hasFDerivAt.prodMk e1.hasFDerivAt
  have hmiddle := (hβ.comp v hpair).sub (e2.hasFDerivAt.pow 2)
  change fderiv ℝ (fun x : Fin 3 → ℝ => O.germ.β (x 0, x 1) - x 2 ^ 2) v
      (Pi.single 2 1) = -2 * v 2
  have hfun : (fun x : Fin 3 → ℝ => O.germ.β (x 0, x 1) - x 2 ^ 2) =
      ((O.germ.β ∘ fun x : Fin 3 → ℝ => (x 0, x 1)) - fun x => e2 x ^ 2) := by
    funext x
    rfl
  rw [hfun, hmiddle.fderiv]
  simp [e0, e1, e2]
  exact (fderiv ℝ O.germ.β (v 0, v 1)).map_zero

/-- The absolute target Jacobian in standard coordinates is `2 |τ|`. -/
theorem ForwardBranchOpen.abs_det_fderiv_asFin3Map_targetMap
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    |(fderiv ℝ (asFin3Map O.targetMap) v).det| = 2 * |v 2| := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)),
    Matrix.det_fin_three]
  simp only [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  norm_cast
  simp_rw [O.fderiv_asFin3Map_targetMap_apply_zero hv,
    O.fderiv_asFin3Map_targetMap_apply_two hv]
  rw [O.fderiv_asFin3Map_targetMap_apply_one_basis_two hv]
  simp

/-- The derivative of the standard-coordinate branch map is the coordinate
transport of the original branch derivative. -/
theorem ForwardBranchOpen.fderiv_asFin3Map_branchMap
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    fderiv ℝ (asFin3Map O.germ.branchMap) v =
      (fderiv ℝ O.germ.branchMap (paramToFin3.symm v)).comp
        paramToFin3.symm.toContinuousLinearMap := by
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  exact ((O.differentiableAt_branchMap hp.1).hasFDerivAt.comp v
    paramToFin3.symm.toContinuousLinearMap.hasFDerivAt).fderiv

/-- The derivative of the standard-coordinate target map is the coordinate
transport of the original target derivative. -/
theorem ForwardBranchOpen.fderiv_asFin3Map_targetMap
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    fderiv ℝ (asFin3Map O.targetMap) v =
      (fderiv ℝ O.targetMap (paramToFin3.symm v)).comp
        paramToFin3.symm.toContinuousLinearMap := by
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  have ht : DifferentiableAt ℝ O.targetMap (paramToFin3.symm v) := by
    apply (O.hasFDerivAt_evalMap_comp_branchMap hp.1).differentiableAt.congr_of_eventuallyEq
    exact (Set.EqOn.eventuallyEq_of_mem
      (fun x hx => (O.evalMap_branch_eq_targetMap hx).symm)
      (O.isOpen_W.mem_nhds hp.1))
  exact (ht.hasFDerivAt.comp v paramToFin3.symm.toContinuousLinearMap.hasFDerivAt).fderiv

/-- The standard-coordinate branch Jacobian is exactly `|τ|` on the positive sheet. -/
theorem ForwardBranchOpen.abs_det_fderiv_asFin3Map_branchMap
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    |(fderiv ℝ (asFin3Map O.germ.branchMap) v).det| = |v 2| := by
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  rw [O.fderiv_asFin3Map_branchMap hv, O.abs_det_fderiv_branchMap_eq hp.1,
    ← O.fderiv_asFin3Map_targetMap hv, O.abs_det_fderiv_asFin3Map_targetMap hv]
  ring

/-- Mathlib's Jacobian change-of-variables formula for the positive branch,
expressed in standard `Fin 3` coordinates. -/
theorem ForwardBranchOpen.lintegral_image_branchMap_eq
    (O : ForwardBranchOpen) (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ q in O.germ.branchMap '' O.Wpos, g q ∂volume =
      ∫⁻ v in O.WposFin3,
        ENNReal.ofReal |(fderiv ℝ (asFin3Map O.germ.branchMap) v).det| *
          g (asFin3Map O.germ.branchMap v) ∂volume := by
  rw [← O.image_asFin3Map_WposFin3]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul (f' := fun v =>
      fderiv ℝ (asFin3Map O.germ.branchMap) v) volume
    O.measurableSet_WposFin3
    (fun v hv => by
      rw [O.fderiv_asFin3Map_branchMap hv]
      exact O.hasFDerivWithinAt_asFin3Map_WposFin3 hv)
    O.asFin3Map_injOn_WposFin3 g

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

/-- Change of variables for the squared norm of the branch-supported candidate.
The right-hand side displays the exact branch Jacobian `|τ|`. -/
theorem ForwardBranchOpen.lintegral_sq_norm_uMinus_image_eq
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ) :
    ∫⁻ q in O.germ.branchMap '' O.Wpos,
        ENNReal.ofReal (‖O.uMinus χ q‖ ^ 2) ∂volume =
      ∫⁻ v in O.WposFin3, ENNReal.ofReal |v 2| *
        ENNReal.ofReal (‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2) ∂volume := by
  rw [O.lintegral_image_branchMap_eq]
  apply setLIntegral_congr_fun O.measurableSet_WposFin3
  intro v hv
  change ENNReal.ofReal |(fderiv ℝ (asFin3Map O.germ.branchMap) v).det| *
      ENNReal.ofReal (‖O.uMinus χ (asFin3Map O.germ.branchMap v)‖ ^ 2) =
    ENNReal.ofReal |v 2| *
      ENNReal.ofReal (‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2)
  rw [O.abs_det_fderiv_asFin3Map_branchMap hv]
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  congr 1
  simpa [asFin3Map] using congrArg (fun z => ‖z‖ₑ ^ 2)
    (O.uMinus_on_image χ hp)

end ExoticCCR
