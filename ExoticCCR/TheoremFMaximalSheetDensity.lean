/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFMaximalSheet
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variables on the maximal forward sheet

This module puts the variable-domain maximal sheet in standard `Fin 3`
coordinates.  The exact anchor identity makes the sheet a local inverse of
`F`; the inverse-function theorem therefore supplies the missing transverse
differentiability and the constant absolute Jacobian `1 / 2`.
-/

noncomputable section

open Filter Function MeasureTheory MvPolynomial Set
open scoped ENNReal Topology

namespace ExoticCCR

/-- Polynomial evaluation is smooth as a function of the evaluation point. -/
theorem contDiff_eval_mvPolynomial (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ⊤ (fun q => MvPolynomial.eval q p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const (c := a)
  | add p r hp hr => simpa using hp.add hr
  | mul_X p i hp =>
      simpa using hp.mul
        (ContinuousLinearMap.contDiff (ContinuousLinearMap.proj i :
          (Fin 3 → ℝ) →L[ℝ] ℝ))

/-- The real anchor evaluation map is smooth. -/
theorem contDiff_evalMap_F : ContDiff ℝ ⊤ (evalMap (F ℝ)) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_eval_mvPolynomial (F ℝ i)

/-- Maximal-sheet parameters in anchor order: `((a,c),s) ↦ (a,s,c)`. -/
def flowParamToFin3 : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => ![p.1.1, p.2, p.1.2]
      invFun := fun v => ((v 0, v 2), v 1)
      left_inv := by
        rintro ⟨⟨a, c⟩, s⟩
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

/-- The maximal-sheet domain in standard coordinates. -/
def ForwardMaximalSheet.Dfin3 (M : ForwardMaximalSheet) : Set (Fin 3 → ℝ) :=
  flowParamToFin3.symm ⁻¹' M.D

/-- The maximal sheet in standard coordinates. -/
def ForwardMaximalSheet.PsiFin3 (M : ForwardMaximalSheet) :
    (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  M.Psi ∘ flowParamToFin3.symm

namespace ForwardMaximalSheet

theorem isOpen_Dfin3 (M : ForwardMaximalSheet) : IsOpen M.Dfin3 :=
  M.isOpen_D.preimage flowParamToFin3.symm.continuous

theorem measurableSet_Dfin3 (M : ForwardMaximalSheet) : MeasurableSet M.Dfin3 :=
  M.isOpen_Dfin3.measurableSet

theorem continuousOn_PsiFin3 (M : ForwardMaximalSheet) :
    ContinuousOn M.PsiFin3 M.Dfin3 :=
  M.continuousOn_Psi.comp flowParamToFin3.symm.continuous.continuousOn
    (fun _ hv => hv)

theorem injOn_PsiFin3 (M : ForwardMaximalSheet) : Set.InjOn M.PsiFin3 M.Dfin3 := by
  intro v hv w hw h
  apply flowParamToFin3.symm.injective
  exact M.injOn_Psi hv hw h

/-- In standard anchor coordinates the maximal sheet is a right inverse of
the polynomial anchor map. -/
theorem evalMap_PsiFin3 (M : ForwardMaximalSheet) {v : Fin 3 → ℝ}
    (hv : v ∈ M.Dfin3) :
    evalMap (F ℝ) (M.PsiFin3 v) = v := by
  change ((v 0, v 2), v 1) ∈ M.D at hv
  have h := M.evalMap_Psi hv.1
    ((mem_integralCurveDomain_iff _ _).1 hv.2)
  change evalMap (F ℝ) (M.Psi ((v 0, v 2), v 1)) = v
  rw [h]
  funext i
  fin_cases i <;> rfl

/-- The derivative of the anchor map is a continuous linear equivalence at
every point. -/
def anchorFDerivEquiv (q : Fin 3 → ℝ) :
    (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) := by
  let L := fderiv ℝ (evalMap (F ℝ)) q
  have hdet : L.det ≠ 0 := by
    rw [det_fderiv_evalMap_F]
    norm_num
  have hunitDet : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet
  have hunitLinear : IsUnit (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr hunitDet
  have hbij : Function.Bijective L :=
    ContinuousLinearMap.isUnit_iff_bijective.mp
      (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr hunitLinear)
  exact ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot_of_injective hbij.1) (LinearMap.range_eq_top.mpr hbij.2)

@[simp] theorem anchorFDerivEquiv_coe (q : Fin 3 → ℝ) :
    (anchorFDerivEquiv q : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) =
      fderiv ℝ (evalMap (F ℝ)) q := rfl

/-- The maximal sheet has a strict derivative at every point of its open
standard-coordinate domain.  This follows from continuity and the local
right-inverse identity, without differentiating the maximal-flow construction
itself. -/
theorem hasStrictFDerivAt_PsiFin3 (M : ForwardMaximalSheet) {v : Fin 3 → ℝ}
    (hv : v ∈ M.Dfin3) :
    HasStrictFDerivAt M.PsiFin3
      ((anchorFDerivEquiv (M.PsiFin3 v)).symm :
        (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) v := by
  let q := M.PsiFin3 v
  let e := anchorFDerivEquiv q
  have hcont : ContinuousAt M.PsiFin3 v :=
    M.continuousOn_PsiFin3 v hv |>.continuousAt (M.isOpen_Dfin3.mem_nhds hv)
  have hFstrict : HasStrictFDerivAt (evalMap (F ℝ))
      (e : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) q := by
    have hcd : ContDiffAt ℝ 1 (evalMap (F ℝ)) q :=
      contDiff_evalMap_F.contDiffAt.of_le (by norm_num)
    simpa [e, q] using hcd.hasStrictFDerivAt (by norm_num)
  have hright : ∀ᶠ w in 𝓝 v, evalMap (F ℝ) (M.PsiFin3 w) = w := by
    filter_upwards [M.isOpen_Dfin3.mem_nhds hv] with w hw
    exact M.evalMap_PsiFin3 hw
  simpa [q, e] using hFstrict.of_local_left_inverse hcont hright

/-- The maximal sheet is differentiable at every point of its open standard
coordinate domain. -/
theorem differentiableAt_PsiFin3 (M : ForwardMaximalSheet) {v : Fin 3 → ℝ}
    (hv : v ∈ M.Dfin3) : DifferentiableAt ℝ M.PsiFin3 v :=
  (M.hasStrictFDerivAt_PsiFin3 hv).differentiableAt

/-- Chain rule for the exact anchor identity on the maximal sheet. -/
theorem fderiv_evalMap_comp_PsiFin3 (M : ForwardMaximalSheet)
    {v : Fin 3 → ℝ} (hv : v ∈ M.Dfin3) :
    (fderiv ℝ (evalMap (F ℝ)) (M.PsiFin3 v)).comp
        (fderiv ℝ M.PsiFin3 v) = ContinuousLinearMap.id ℝ (Fin 3 → ℝ) := by
  have hcomp := (hasFDerivAt_evalMap_F (M.PsiFin3 v)).comp v
    (M.differentiableAt_PsiFin3 hv).hasFDerivAt
  have hid : HasFDerivAt (fun w : Fin 3 → ℝ => w)
      (ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) v := hasFDerivAt_id v
  have heq : (evalMap (F ℝ) ∘ M.PsiFin3) =ᶠ[𝓝 v]
      (fun w : Fin 3 → ℝ => w) := by
    filter_upwards [M.isOpen_Dfin3.mem_nhds hv] with (w : Fin 3 → ℝ) hw
    exact M.evalMap_PsiFin3 hw
  have hcomp' : HasFDerivAt (fun w : Fin 3 → ℝ => w)
      ((fderiv ℝ (evalMap (F ℝ)) (M.PsiFin3 v)).comp
        (fderiv ℝ M.PsiFin3 v)) v := by
    rw [fderiv_evalMap_F]
    exact hcomp.congr_of_eventuallyEq heq.symm
  exact hcomp'.unique hid

/-- The maximal sheet has constant absolute Jacobian `1 / 2`. -/
theorem abs_det_fderiv_PsiFin3 (M : ForwardMaximalSheet)
    {v : Fin 3 → ℝ} (hv : v ∈ M.Dfin3) :
    |(fderiv ℝ M.PsiFin3 v).det| = 1 / 2 := by
  have hchain := congrArg ContinuousLinearMap.det (M.fderiv_evalMap_comp_PsiFin3 hv)
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ← ContinuousLinearMap.det, det_fderiv_evalMap_F] at hchain
  have hid : (ContinuousLinearMap.id ℝ (Fin 3 → ℝ)).det = 1 := LinearMap.det_id
  rw [hid] at hchain
  have hdet : (fderiv ℝ M.PsiFin3 v).det = -(1 / 2 : ℝ) := by
    linarith
  rw [hdet]
  norm_num

/-- The standard-coordinate maximal-sheet derivative is available as a
within-derivative on its domain. -/
theorem hasFDerivWithinAt_PsiFin3 (M : ForwardMaximalSheet)
    {v : Fin 3 → ℝ} (hv : v ∈ M.Dfin3) :
    HasFDerivWithinAt M.PsiFin3 (fderiv ℝ M.PsiFin3 v) M.Dfin3 v :=
  (M.differentiableAt_PsiFin3 hv).hasFDerivAt.hasFDerivWithinAt

/-- Mathlib's Jacobian change-of-variables formula on the full variable-domain
maximal sheet.  The weight is the constant reciprocal anchor Jacobian `1/2`. -/
theorem lintegral_image_PsiFin3_eq (M : ForwardMaximalSheet)
    (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ q in M.PsiFin3 '' M.Dfin3, g q ∂volume =
      ∫⁻ v in M.Dfin3, ENNReal.ofReal (1 / 2 : ℝ) * g (M.PsiFin3 v) ∂volume := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (f' := fun v => fderiv ℝ M.PsiFin3 v) volume M.measurableSet_Dfin3
    (fun v hv => M.hasFDerivWithinAt_PsiFin3 hv) M.injOn_PsiFin3 g]
  apply setLIntegral_congr_fun M.measurableSet_Dfin3
  intro v hv
  dsimp only
  rw [M.abs_det_fderiv_PsiFin3 hv]

/-- The standard-coordinate maximal-sheet restriction is a measurable embedding. -/
theorem measurableEmbedding_PsiFin3 (M : ForwardMaximalSheet) :
    MeasurableEmbedding (M.Dfin3.restrict M.PsiFin3) :=
  measurableEmbedding_of_fderivWithin M.measurableSet_Dfin3
    (fun _ hv => M.hasFDerivWithinAt_PsiFin3 hv) M.injOn_PsiFin3

/-- The maximal-sheet image is measurable. -/
theorem measurableSet_image_Psi (M : ForwardMaximalSheet) :
    MeasurableSet (M.Psi '' M.D) := by
  have himage : M.PsiFin3 '' M.Dfin3 = M.Psi '' M.D := by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨flowParamToFin3.symm v, hv, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨flowParamToFin3 p, by simpa [Dfin3], by simp [PsiFin3]⟩
  rw [← himage]
  exact measurable_image_of_fderivWithin M.measurableSet_Dfin3
    (fun v hv => M.hasFDerivWithinAt_PsiFin3 hv) M.injOn_PsiFin3

/-- The flow-time deficiency density in standard anchor coordinates. -/
def deficiencyDensityFin3 (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (v : Fin 3 → ℝ) : ℂ :=
  χ (v 0, v 2) * Complex.exp (v 1 - M.S.O.germ.β (v 0, v 2))

/-- The maximal-sheet deficiency candidate, extended by zero off the sheet
image. -/
def uMinus (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) :
    (Fin 3 → ℝ) → ℂ := by
  classical
  exact fun q =>
    if q ∈ M.PsiFin3 '' M.Dfin3 then
      M.deficiencyDensityFin3 χ
        (Function.invFunOn M.PsiFin3 M.Dfin3 q)
    else 0

theorem uMinus_on_image (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    {v : Fin 3 → ℝ} (hv : v ∈ M.Dfin3) :
    M.uMinus χ (M.PsiFin3 v) = M.deficiencyDensityFin3 χ v := by
  rw [uMinus, if_pos ⟨v, hv, rfl⟩]
  rw [M.injOn_PsiFin3.leftInvOn_invFunOn hv]

theorem uMinus_off_image (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    {q : Fin 3 → ℝ} (hq : q ∉ M.PsiFin3 '' M.Dfin3) :
    M.uMinus χ q = 0 := by
  simp [uMinus, hq]

/-- The maximal-sheet image is open. -/
theorem isOpen_image_Psi (M : ForwardMaximalSheet) : IsOpen (M.Psi '' M.D) := by
  rw [← show M.PsiFin3 '' M.Dfin3 = M.Psi '' M.D by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨flowParamToFin3.symm v, hv, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨flowParamToFin3 p, by simpa [Dfin3], by simp [PsiFin3]⟩]
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨v, hv, rfl⟩
  let e := anchorFDerivEquiv (M.PsiFin3 v)
  have hstrict : HasStrictFDerivAt M.PsiFin3
      (e.symm : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) v := by
    simpa [e] using M.hasStrictFDerivAt_PsiFin3 hv
  rw [← hstrict.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (M.isOpen_Dfin3.mem_nhds hv)

end ForwardMaximalSheet

end ExoticCCR
