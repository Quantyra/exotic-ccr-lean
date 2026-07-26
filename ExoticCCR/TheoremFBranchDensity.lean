/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardBranch
import ExoticCCR.TheoremFJacobianFDeriv
import ExoticCCR.TheoremD
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Algebraic density and branch-supported deficiency data

This module records the absolute algebraic Jacobian value of the anchor map and
defines the candidate deficiency density on the positive forward branch.  It
proves the required change-of-variables and ambient `L²` estimates, but does
not assert an adjoint-domain statement.
-/

noncomputable section

open Filter Function MeasureTheory MvPolynomial Set
open scoped ENNReal Topology

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

/-- The standard-coordinate identification preserves Lebesgue volume. -/
theorem measurePreserving_paramToFin3_symm :
    MeasurePreserving paramToFin3.symm
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure ((ℝ × ℝ) × ℝ)) := by
  let hsplit : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3))
      (volume : Measure (Fin 3 → ℝ))
      (volume : Measure (ℝ × (Fin 2 → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  let hswap : MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  let hpair := (volume_preserving_finTwoArrow ℝ).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have h := hpair.comp (hswap.comp hsplit)
  refine h.congr paramToFin3.symm.continuous.measurable ?_
  filter_upwards with v
  ext <;> simp [paramToFin3, Fin.removeNth_apply, Fin.succAbove]

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

/-- The standard-coordinate branch map is smooth at every point of its positive
domain. -/
theorem ForwardBranchOpen.contDiffAt_asFin3Map_branchMap
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    ContDiffAt ℝ ⊤ (asFin3Map O.germ.branchMap) v := by
  have hp : paramToFin3.symm v ∈ O.Wpos := hv
  exact (O.contDiff_branchMap (paramToFin3.symm v) hp.1).contDiffAt
    (O.isOpen_W.mem_nhds hp.1) |>.comp v
      (paramToFin3.symm : (Fin 3 → ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ)).contDiff.contDiffAt

/-- The derivative of the standard-coordinate branch map is bijective at every
point of the positive domain. -/
theorem ForwardBranchOpen.bijective_fderiv_asFin3Map_branchMap
    (O : ForwardBranchOpen) {v : Fin 3 → ℝ} (hv : v ∈ O.WposFin3) :
    Function.Bijective (fderiv ℝ (asFin3Map O.germ.branchMap) v) := by
  let L := fderiv ℝ (asFin3Map O.germ.branchMap) v
  have hdet : L.det ≠ 0 := by
    intro hzero
    have habs := O.abs_det_fderiv_asFin3Map_branchMap hv
    rw [hzero, abs_zero] at habs
    have hvτ : 0 < v 2 := hv.2
    exact (ne_of_gt hvτ) (abs_eq_zero.mp habs.symm)
  have hunitDet : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet
  have hunitLinear : IsUnit (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :=
    (LinearMap.isUnit_iff_isUnit_det
      (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))).mpr hunitDet
  have hunit : IsUnit L := ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr hunitLinear
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hunit

/-- The positive local branch image is open in ambient `ℝ³`.  This is the
local-diffeomorphism step: the branch derivative has determinant of absolute
value `τ`, hence is invertible throughout the positive domain. -/
theorem ForwardBranchOpen.isOpen_image_branchMap_Wpos (O : ForwardBranchOpen) :
    IsOpen (O.germ.branchMap '' O.Wpos) := by
  rw [← O.image_asFin3Map_WposFin3]
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  rcases hq with ⟨v, hv, rfl⟩
  let L := fderiv ℝ (asFin3Map O.germ.branchMap) v
  have hbij : Function.Bijective L :=
    O.bijective_fderiv_asFin3Map_branchMap hv
  let e : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot_of_injective hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2)
  have hstrict : HasStrictFDerivAt (asFin3Map O.germ.branchMap)
      (e : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) v := by
    have h := (O.contDiffAt_asFin3Map_branchMap hv).hasStrictFDerivAt (by simp)
    change HasStrictFDerivAt (asFin3Map O.germ.branchMap) L v
    exact h
  rw [← hstrict.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (O.isOpen_WposFin3.mem_nhds hv)

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

/-- There are nonzero continuous compactly supported complex cutoffs on the
branch base coordinates. -/
theorem exists_continuous_hasCompactSupport_nonzero_baseCutoff :
    ∃ χ : ℝ × ℝ → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ χ ≠ 0 := by
  let c : ℝ × ℝ := (0, 2)
  let b : ContDiffBump c := ⟨1, 2, zero_lt_one, one_lt_two⟩
  refine ⟨fun x => (b x : ℂ), ?_, ?_, ?_⟩
  · exact Complex.continuous_ofReal.comp b.continuous
  · exact b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  · intro hzero
    have hcenter := congrFun hzero c
    have hb : b c = 1 := b.one_of_mem_closedBall
      (Metric.mem_closedBall_self b.rIn_pos.le)
    rw [hb] at hcenter
    norm_num at hcenter

/-- A compactly supported continuous cutoff can be chosen to equal one at any
prescribed branch-base point. -/
theorem exists_continuous_hasCompactSupport_baseCutoff_at (c : ℝ × ℝ) :
    ∃ χ : ℝ × ℝ → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ χ c = 1 := by
  let b : ContDiffBump c := ⟨1, 2, zero_lt_one, one_lt_two⟩
  refine ⟨fun x => (b x : ℂ), Complex.continuous_ofReal.comp b.continuous,
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero, ?_⟩
  change (b c : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  norm_num

/-- The candidate density satisfies the expected Gaussian differential in the
positive-branch time coordinate. -/
theorem ForwardBranchOpen.hasDerivAt_deficiencyDensity_tau (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => O.deficiencyDensity χ (x, t))
      (((-2 * τ : ℝ) : ℂ) * O.deficiencyDensity χ (x, τ)) τ := by
  unfold ForwardBranchOpen.deficiencyDensity
  have hsq : HasDerivAt (-((fun t : ℝ => (t : ℂ)) * (fun t : ℝ => (t : ℂ))))
      (((-2 * τ : ℝ) : ℂ)) τ := by
    have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) τ := by
      simpa using (hasDerivAt_id (x := τ)).ofReal_comp
    have hpow : HasDerivAt ((fun t : ℝ => (t : ℂ)) * (fun t : ℝ => (t : ℂ)))
        (2 * (τ : ℂ)) τ := by
      simpa [pow_two, two_mul] using hcast.mul hcast
    simpa [two_mul] using hpow.neg
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
    ((Complex.hasDerivAt_exp ((-((fun t : ℝ => (t : ℂ)) *
      (fun t : ℝ => (t : ℂ)))) τ)).comp τ hsq).const_mul (χ x)

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

/-- Along a vertical parameter line inside the open positive branch domain,
the pullback of `uMinus` has the expected Gaussian derivative. -/
theorem ForwardBranchOpen.hasDerivAt_uMinus_comp_branchMap_tau
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ)
    {x : ℝ × ℝ} {τ : ℝ} (hp : (x, τ) ∈ O.Wpos) :
    HasDerivAt (fun t : ℝ => O.uMinus χ (O.germ.branchMap (x, t)))
      (((-2 * τ : ℝ) : ℂ) * O.uMinus χ (O.germ.branchMap (x, τ))) τ := by
  have hline : (fun t : ℝ => (x, t)) ⁻¹' O.Wpos ∈ nhds τ :=
    (O.isOpen_Wpos.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp
  have heq : (fun t : ℝ => O.uMinus χ (O.germ.branchMap (x, t))) =ᶠ[nhds τ]
      (fun t : ℝ => O.deficiencyDensity χ (x, t)) := by
    filter_upwards [hline] with t ht
    exact O.uMinus_on_image χ ht
  simpa only [O.uMinus_on_image χ hp] using
    (O.hasDerivAt_deficiencyDensity_tau χ x τ).congr_of_eventuallyEq heq

/-- The evaluated anchor derivative sends the first dual field to the unit
vector in the middle target coordinate. -/
theorem evalJacobianF_apply_X1 (q : Fin 3 → ℝ) :
    evalJacobianF q (X1 q) = ![0, 1, 0] := by
  funext i
  have hij := congrArg (fun M => M i (1 : Fin 3))
    (jacobian_mul_dualMatrixF_transpose ℝ (by norm_num))
  change (∑ x, MvPolynomial.eval q (jacobianMatrix (F ℝ) i x) *
    MvPolynomial.eval q (dualMatrixF ℝ 1 x)) = (![0, 1, 0] : Fin 3 → ℝ) i
  fin_cases i <;>
    simpa [evalJacobianF, X1, dualVectorField, Matrix.toLin'_apply,
      Matrix.mulVec, Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul] using
      congrArg (MvPolynomial.eval q) hij

/-- On the positive local branch, differentiation in `τ` is the vector field
`X1` multiplied by the target speed `-2τ`.  This is the honest local
characteristic identity; it does not control a boundary of `Wpos`. -/
theorem ForwardBranchOpen.hasDerivAt_branchMap_tau
    (O : ForwardBranchOpen) {x : ℝ × ℝ} {τ : ℝ} (hp : (x, τ) ∈ O.Wpos) :
    HasDerivAt (fun t : ℝ => O.germ.branchMap (x, t))
      ((-2 * τ) • X1 (O.germ.branchMap (x, τ))) τ := by
  let q := O.germ.branchMap (x, τ)
  have hline : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) τ :=
    (hasDerivAt_const τ x).prodMk (hasDerivAt_id τ)
  have hbranchDiff : DifferentiableAt ℝ (fun t : ℝ => O.germ.branchMap (x, t)) τ :=
    (O.differentiableAt_branchMap hp.1).comp τ hline.differentiableAt
  have hbranch := hbranchDiff.hasDerivAt
  have hcomp : HasDerivAt
      (fun t : ℝ => evalMap (F ℝ) (O.germ.branchMap (x, t)))
      (evalJacobianF q (deriv (fun t : ℝ => O.germ.branchMap (x, t)) τ)) τ := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_evalMap_F q).comp_hasDerivAt τ hbranch
  have htarget : HasDerivAt (fun t : ℝ => O.targetMap (x, t))
      (![0, -2 * τ, 0] : Fin 3 → ℝ) τ := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [ForwardBranchOpen.targetMap] using (hasDerivAt_const τ x.1)
    · change HasDerivAt (fun t : ℝ => O.germ.β x - t ^ 2) (-2 * τ) τ
      simpa [id_eq, two_mul] using
        ((hasDerivAt_id τ).pow 2).const_sub (O.germ.β x)
    · simpa [ForwardBranchOpen.targetMap] using (hasDerivAt_const τ x.2)
  have heq : (fun t : ℝ => evalMap (F ℝ) (O.germ.branchMap (x, t))) =ᶠ[𝓝 τ]
      (fun t : ℝ => O.targetMap (x, t)) := by
    have hmem : (fun t : ℝ => (x, t)) ⁻¹' O.W ∈ 𝓝 τ :=
      (O.isOpen_W.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp.1
    filter_upwards [hmem] with t ht
    exact O.evalMap_branch_eq_targetMap ht
  have hJbranch : evalJacobianF q (deriv (fun t : ℝ => O.germ.branchMap (x, t)) τ) =
      (![0, -2 * τ, 0] : Fin 3 → ℝ) :=
    hcomp.unique (htarget.congr_of_eventuallyEq heq)
  have hdet : (evalJacobianF q).det ≠ 0 := by
    rw [← fderiv_evalMap_F, det_fderiv_evalMap_F]
    norm_num
  have hunitDet : IsUnit (evalJacobianF q).det := isUnit_iff_ne_zero.mpr hdet
  have hunitLinear : IsUnit (evalJacobianF q : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr hunitDet
  have hJinj : Function.Injective (evalJacobianF q) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp
      (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr hunitLinear)).1
  apply hbranch.congr_deriv
  apply hJinj
  rw [hJbranch, map_smul, evalJacobianF_apply_X1]
  funext i
  fin_cases i <;> simp

/-- Reparameterizing the local positive branch by its target `s` coordinate
gives the deficiency equation `d u / ds = u` at every interior point.  This is
a pointwise characteristic identity only, not a global weak identity for the
zero extension. -/
theorem ForwardBranchOpen.hasDerivAt_uMinus_along_s
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ)
    {x : ℝ × ℝ} {τ : ℝ} (hp : (x, τ) ∈ O.Wpos) :
    HasDerivAt
      (fun s : ℝ => O.uMinus χ
        (O.germ.branchMap (x, Real.sqrt (O.germ.β x - s))))
      (O.uMinus χ (O.germ.branchMap (x, τ)))
      (O.germ.β x - τ ^ 2) := by
  have hτ : 0 < τ := hp.2
  have hsqrt : Real.sqrt (O.germ.β x - (O.germ.β x - τ ^ 2)) = τ := by
    rw [show O.germ.β x - (O.germ.β x - τ ^ 2) = τ ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hτ]
  have hinner : HasDerivAt (fun s : ℝ => O.germ.β x - s) (-1)
      (O.germ.β x - τ ^ 2) := by
    exact (hasDerivAt_id (O.germ.β x - τ ^ 2)).const_sub (O.germ.β x)
  have hsqrtOuter : HasDerivAt Real.sqrt (1 / (2 * τ)) (τ ^ 2) := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hτ] using
      Real.hasDerivAt_sqrt (by positivity : τ ^ 2 ≠ 0)
  have hs := hsqrtOuter.comp_of_eq (O.germ.β x - τ ^ 2) hinner
    (show τ ^ 2 = O.germ.β x - (O.germ.β x - τ ^ 2) by ring)
  have huOuter := O.hasDerivAt_uMinus_comp_branchMap_tau χ hp
  have hu := huOuter.scomp_of_eq (O.germ.β x - τ ^ 2) hs hsqrt.symm
  have hscalar : (1 / (2 * τ) * (-1)) •
      (((-2 * τ : ℝ) : ℂ) * O.uMinus χ (O.germ.branchMap (x, τ))) =
      O.uMinus χ (O.germ.branchMap (x, τ)) := by
    change (((1 / (2 * τ) * (-1) : ℝ) : ℂ) *
      (((-2 * τ : ℝ) : ℂ) * O.uMinus χ (O.germ.branchMap (x, τ)))) = _
    rw [← mul_assoc]
    have hone : (((1 / (2 * τ) * (-1) : ℝ) : ℂ) * ((-2 * τ : ℝ) : ℂ)) = 1 := by
      norm_cast
      field_simp [ne_of_gt hτ]
      norm_num
    rw [hone, one_mul]
  simpa only [Function.comp_def] using hu.congr_deriv hscalar

/-- Precise finite-boundary residual for the zero extension: if an interior
branch parameter approaches a finite parameter whose image lies outside the
chosen local image, continuity of `uMinus` would force the parameter density
to tend to zero.  The local construction presently supplies no such vanishing
at artificial ends of `Wpos`. -/
theorem ForwardBranchOpen.tendsto_deficiencyDensity_zero_of_continuousAt_boundary
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ) {p : (ℝ × ℝ) × ℝ}
    (hpW : p ∈ O.W) (hout : O.germ.branchMap p ∉ O.germ.branchMap '' O.Wpos)
    (hu : ContinuousAt (O.uMinus χ) (O.germ.branchMap p)) :
    Tendsto (O.deficiencyDensity χ) (𝓝[O.Wpos] p) (𝓝 0) := by
  have hb : Tendsto O.germ.branchMap (𝓝[O.Wpos] p)
      (𝓝 (O.germ.branchMap p)) :=
    ((O.contDiff_branchMap p hpW).contDiffAt
      (O.isOpen_W.mem_nhds hpW)).continuousAt.tendsto.mono_left inf_le_left
  have hcomp := hu.tendsto.comp hb
  rw [O.uMinus_off_image χ hout] at hcomp
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  change O.uMinus χ (O.germ.branchMap q) = O.deficiencyDensity χ q
  exact O.uMinus_on_image χ hq

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

/-- The Jacobian-weighted squared deficiency density is integrable on the full
standard parameter space. -/
theorem ForwardBranchOpen.integrable_weighted_deficiencyDensity
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun v : Fin 3 → ℝ =>
      |v 2| * ‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2) volume := by
  have hχ2 : Integrable (fun x : ℝ × ℝ => ‖χ x‖ ^ 2)
      (volume : Measure (ℝ × ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hχ.aestronglyMeasurable).mp
      (hχ.memLp_of_hasCompactSupport hχc)
  have hτ : Integrable
      (fun τ : ℝ => |τ| * ‖Complex.exp (-(τ : ℂ) ^ 2)‖ ^ 2) := by
    convert (integrable_mul_exp_neg_mul_sq (b := 2) (by norm_num)).norm using 1
    ext τ
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_exp, pow_two, ← Real.exp_add]
    congr 2
    have hre : ((τ : ℂ) ^ 2).re = τ ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    rw [Complex.neg_re, hre]
    ring
  have hp : Integrable (fun p : (ℝ × ℝ) × ℝ =>
      ‖χ p.1‖ ^ 2 * (|p.2| * ‖Complex.exp (-(p.2 : ℂ) ^ 2)‖ ^ 2)) := by
    rw [Measure.volume_eq_prod]
    exact hχ2.mul_prod hτ
  have hi := (measurePreserving_paramToFin3_symm.integrable_comp_emb
    paramToFin3.symm.toHomeomorph.measurableEmbedding
    (g := fun p : (ℝ × ℝ) × ℝ =>
      ‖χ p.1‖ ^ 2 * (|p.2| * ‖Complex.exp (-(p.2 : ℂ) ^ 2)‖ ^ 2))).mpr hp
  convert hi using 1
  ext v
  simp [paramToFin3, Function.comp_apply, ForwardBranchOpen.deficiencyDensity,
    mul_pow, mul_left_comm, mul_comm]

/-- The Jacobian-weighted squared deficiency density is integrable on the
positive standard-coordinate branch domain. -/
theorem ForwardBranchOpen.integrableOn_weighted_deficiencyDensity
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    IntegrableOn (fun v : Fin 3 → ℝ =>
      |v 2| * ‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2)
      O.WposFin3 volume :=
  (O.integrable_weighted_deficiencyDensity χ hχ hχc).integrableOn

/-- The weighted `ENNReal` integral occurring in branch change of variables is finite. -/
theorem ForwardBranchOpen.lintegral_weighted_lt_top
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ∫⁻ v in O.WposFin3, ENNReal.ofReal |v 2| *
        ENNReal.ofReal (‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2) ∂volume < ∞ := by
  simp_rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  apply (hasFiniteIntegral_iff_ofReal ?_).mp
    (O.integrableOn_weighted_deficiencyDensity χ hχ hχc).hasFiniteIntegral
  filter_upwards
  exact fun v => mul_nonneg (abs_nonneg _) (sq_nonneg _)

/-- A cutoff which is nonzero at one positive branch parameter gives a strictly
positive Jacobian-weighted square integral. -/
theorem ForwardBranchOpen.lintegral_weighted_pos
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.Wpos) (hχp : χ p.1 ≠ 0) :
    0 < ∫⁻ v in O.WposFin3, ENNReal.ofReal |v 2| *
        ENNReal.ofReal (‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2) ∂volume := by
  let g : (Fin 3 → ℝ) → ℝ := fun v =>
    |v 2| * ‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2
  let f : (Fin 3 → ℝ) → ℝ≥0∞ := fun v => ENNReal.ofReal |v 2| *
    ENNReal.ofReal (‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2)
  let v0 := paramToFin3 p
  have hv0 : v0 ∈ O.WposFin3 := by
    simpa [v0, ForwardBranchOpen.WposFin3]
  have hτ : 0 < p.2 := hp.2
  have hdens : O.deficiencyDensity χ p ≠ 0 := by
    simp only [ForwardBranchOpen.deficiencyDensity, mul_ne_zero_iff]
    exact ⟨hχp, Complex.exp_ne_zero _⟩
  have hg0 : 0 < g v0 := by
    apply mul_pos
    · simpa [v0, paramToFin3] using abs_pos.mpr (ne_of_gt hτ)
    · exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa [v0] using hdens))
  have hg : Continuous g := by
    unfold g ForwardBranchOpen.deficiencyDensity
    fun_prop
  let N : Set (Fin 3 → ℝ) := O.WposFin3 ∩ {v | 0 < g v}
  have hNopen : IsOpen N := O.isOpen_WposFin3.inter (isOpen_lt continuous_const hg)
  have hvN : v0 ∈ N := ⟨hv0, hg0⟩
  have hNpos : 0 < volume N := hNopen.measure_pos volume ⟨v0, hvN⟩
  have hf : Measurable f := by
    unfold f ForwardBranchOpen.deficiencyDensity
    fun_prop
  have hsub : N ⊆ Function.support f ∩ O.WposFin3 := by
    intro v hv
    refine ⟨?_, hv.1⟩
    have hgv : 0 < g v := hv.2
    have hvτ : 0 < |v 2| := by
      by_contra h
      have hz : |v 2| = 0 := le_antisymm (not_lt.mp h) (abs_nonneg _)
      simp [g, hz] at hgv
    have hd : 0 < ‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2 := by
      by_contra h
      have hz := le_antisymm (not_lt.mp h) (sq_nonneg _)
      simp [g, hz] at hgv
    simp only [Function.mem_support, f, ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero]
    exact not_or_intro (not_le.mpr hvτ) (not_le.mpr hd)
  apply (setLIntegral_pos_iff hf).mpr
  exact lt_of_lt_of_le hNpos (measure_mono hsub)

/-- The standard-coordinate positive branch restriction is a measurable embedding. -/
theorem ForwardBranchOpen.measurableEmbedding_asFin3Map_branchMap_WposFin3
    (O : ForwardBranchOpen) :
    MeasurableEmbedding (O.WposFin3.restrict (asFin3Map O.germ.branchMap)) :=
  measurableEmbedding_of_fderivWithin O.measurableSet_WposFin3
    (fun _ hv => O.hasFDerivWithinAt_asFin3Map_WposFin3 hv)
    O.asFin3Map_injOn_WposFin3

/-- The branch-supported zero extension is measurable. -/
theorem ForwardBranchOpen.measurable_uMinus (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) : Measurable (O.uMinus χ) := by
  classical
  by_cases hW : O.Wpos.Nonempty
  · obtain ⟨p0, hp0⟩ := hW
    letI : Nonempty O.WposFin3 := ⟨⟨paramToFin3 p0, by
      simpa [ForwardBranchOpen.WposFin3] using hp0⟩⟩
    let e := O.measurableEmbedding_asFin3Map_branchMap_WposFin3
    let g : (Fin 3 → ℝ) → ℂ := fun q =>
      O.deficiencyDensity χ (paramToFin3.symm (e.invFun q).1)
    have hg : Measurable g := by
      have hinv : Measurable (fun q => paramToFin3.symm (e.invFun q).1) :=
        paramToFin3.symm.continuous.measurable.comp
          (measurable_subtype_coe.comp e.measurable_invFun)
      apply Measurable.mul
      · exact hχ.measurable.comp (measurable_fst.comp hinv)
      · apply Complex.measurable_exp.comp
        exact ((Complex.measurable_ofReal.comp
          (measurable_snd.comp hinv)).pow_const 2).neg
    have heq : O.uMinus χ = Set.piecewise (O.germ.branchMap '' O.Wpos) g 0 := by
      funext q
      by_cases hq : q ∈ O.germ.branchMap '' O.Wpos
      · rcases hq with ⟨p, hp, rfl⟩
        rw [O.uMinus_on_image χ hp]
        have himg : O.germ.branchMap p ∈ O.germ.branchMap '' O.Wpos := ⟨p, hp, rfl⟩
        rw [Set.piecewise_eq_of_mem _ _ _ himg]
        have hv : paramToFin3 p ∈ O.WposFin3 := by
          simpa [ForwardBranchOpen.WposFin3]
        have heval : asFin3Map O.germ.branchMap (paramToFin3 p) =
            O.germ.branchMap p := by simp [asFin3Map]
        change O.deficiencyDensity χ p =
          O.deficiencyDensity χ (paramToFin3.symm (e.invFun (O.germ.branchMap p)).1)
        rw [← heval, show e.invFun (asFin3Map O.germ.branchMap (paramToFin3 p)) =
          ⟨paramToFin3 p, hv⟩ from e.leftInverse_invFun ⟨paramToFin3 p, hv⟩]
        simp
      · rw [O.uMinus_off_image χ hq]
        simp [Set.piecewise, hq]
    rw [heq]
    exact hg.piecewise O.measurableSet_image_branchMap_Wpos measurable_const
  · have hEmpty : O.Wpos = ∅ := not_nonempty_iff_eq_empty.mp hW
    rw [show O.uMinus χ = 0 by
      funext q
      simp [ForwardBranchOpen.uMinus, hEmpty]]
    exact measurable_const

/-- The branch-supported zero extension is strongly measurable almost everywhere. -/
theorem ForwardBranchOpen.aestronglyMeasurable_uMinus (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) :
    AEStronglyMeasurable (O.uMinus χ) volume :=
  (O.measurable_uMinus χ hχ).aestronglyMeasurable

/-- The ambient squared-norm integral of the branch-supported candidate is finite. -/
theorem ForwardBranchOpen.lintegral_sq_norm_uMinus_lt_top
    (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ∫⁻ q : Fin 3 → ℝ, ENNReal.ofReal (‖O.uMinus χ q‖ ^ 2) ∂volume < ∞ := by
  let S := O.germ.branchMap '' O.Wpos
  let f : (Fin 3 → ℝ) → ℝ≥0∞ := fun q => ENNReal.ofReal (‖O.uMinus χ q‖ ^ 2)
  have hind : S.indicator f = f := by
    funext q
    by_cases hq : q ∈ S
    · simp [hq]
    · simp [Set.indicator, hq, f, S, O.uMinus_off_image χ hq]
  calc
    ∫⁻ q, ENNReal.ofReal (‖O.uMinus χ q‖ ^ 2) ∂volume = ∫⁻ q, f q ∂volume := rfl
    _ = ∫⁻ q, S.indicator f q ∂volume := by rw [hind]
    _ = ∫⁻ q in S, f q ∂volume :=
      lintegral_indicator O.measurableSet_image_branchMap_Wpos f
    _ = ∫⁻ v in O.WposFin3, ENNReal.ofReal |v 2| *
        ENNReal.ofReal (‖O.deficiencyDensity χ (paramToFin3.symm v)‖ ^ 2) ∂volume :=
      O.lintegral_sq_norm_uMinus_image_eq χ
    _ < ∞ := O.lintegral_weighted_lt_top χ hχ hχc

/-- The branch-supported candidate belongs to ambient `L²(ℝ³)`. -/
theorem ForwardBranchOpen.memLp_uMinus (O : ForwardBranchOpen)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (O.uMinus χ) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (O.aestronglyMeasurable_uMinus χ hχ)).mpr
  refine ⟨((O.measurable_uMinus χ hχ).norm.pow_const 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal ?_).mpr
    (O.lintegral_sq_norm_uMinus_lt_top χ hχ hχc)
  filter_upwards
  exact fun q => sq_nonneg ‖O.uMinus χ q‖

/-- Every forward branch carries a compactly supported cutoff whose zero
extension determines a nonzero vector of ambient `L²(ℝ³)`. -/
theorem ForwardBranchOpen.exists_nonzero_L2_uMinus (O : ForwardBranchOpen) :
    ∃ (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ),
      (O.memLp_uMinus χ hχ hχc).toLp (O.uMinus χ) ≠ 0 := by
  obtain ⟨p, hp⟩ := O.nonempty_Wpos
  obtain ⟨χ, hχ, hχc, hχp⟩ := exists_continuous_hasCompactSupport_baseCutoff_at p.1
  refine ⟨χ, hχ, hχc, ?_⟩
  let hu := O.memLp_uMinus χ hχ hχc
  have hweighted := O.lintegral_weighted_pos χ hχ hp (by simpa [hχp])
  have himage : 0 < ∫⁻ q in O.germ.branchMap '' O.Wpos,
      ENNReal.ofReal (‖O.uMinus χ q‖ ^ 2) ∂volume := by
    rw [O.lintegral_sq_norm_uMinus_image_eq]
    exact hweighted
  intro hzero
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero] at hzero
  have huae : O.uMinus χ =ᵐ[volume] 0 := hu.coeFn_toLp.symm.trans hzero
  have hamb : ∫⁻ q : Fin 3 → ℝ,
      ENNReal.ofReal (‖O.uMinus χ q‖ ^ 2) ∂volume = 0 := by
    rw [← lintegral_zero]
    apply lintegral_congr_ae
    filter_upwards [huae] with q hq
    simp [hq]
  have hz : ∫⁻ q in O.germ.branchMap '' O.Wpos,
      ENNReal.ofReal (‖O.uMinus χ q‖ ^ 2) ∂volume = 0 := by
    apply le_zero_iff.mp
    exact (setLIntegral_le_lintegral _ _).trans_eq hamb
  exact (ne_of_gt himage) hz

/-- Existence form of the nonzero ambient `L²` branch candidate. -/
theorem exists_forwardBranchOpen_nonzero_L2_uMinus :
    ∃ (O : ForwardBranchOpen) (χ : ℝ × ℝ → ℂ)
        (hχ : Continuous χ) (hχc : HasCompactSupport χ),
      (O.memLp_uMinus χ hχ hχc).toLp (O.uMinus χ) ≠ 0 := by
  obtain ⟨O⟩ := exists_forwardBranchOpen
  obtain ⟨χ, hχ, hχc, hu⟩ := O.exists_nonzero_L2_uMinus
  exact ⟨O, χ, hχ, hχc, hu⟩

end ExoticCCR
