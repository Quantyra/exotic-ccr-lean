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

/-- The anchor-ordered parameter identification preserves Lebesgue volume. -/
theorem measurePreserving_flowParamToFin3_symm :
    MeasurePreserving flowParamToFin3.symm
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure ((ℝ × ℝ) × ℝ)) := by
  let hsplit : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (1 : Fin 3))
      (volume : Measure (Fin 3 → ℝ))
      (volume : Measure (ℝ × (Fin 2 → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (1 : Fin 3)
  let hswap : MeasurePreserving (Prod.swap : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  let hpair := (volume_preserving_finTwoArrow ℝ).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have h := hpair.comp (hswap.comp hsplit)
  refine h.congr flowParamToFin3.symm.continuous.measurable ?_
  filter_upwards with v
  ext <;> simp [flowParamToFin3, Fin.removeNth_apply, Fin.succAbove]

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

/-- Every maximal-sheet parameter lies strictly below its forward wall. -/
theorem time_lt_beta_of_mem_Dfin3 (M : ForwardMaximalSheet) {v : Fin 3 → ℝ}
    (hv : v ∈ M.Dfin3) : v 1 < M.S.O.germ.β (v 0, v 2) := by
  change (v 0, v 2) ∈ M.W ∧
    v 1 - M.s0 (v 0, v 2) ∈ integralCurveDomain (M.S.qSigma (v 0, v 2)) at hv
  have ht := ((mem_integralCurveDomain_iff _ _).1 hv.2).2
  rw [M.tMax_eq (v 0, v 2) hv.1] at ht
  have ht' : v 1 - M.s0 (v 0, v 2) < M.S.ε₀ := by exact_mod_cast ht
  dsimp [ForwardMaximalSheet.s0] at ht'
  linarith

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

/-- The parameter density is continuous on the (variable) maximal-sheet
domain.  No regularity of the extended-real lower endpoint is needed here. -/
theorem continuousOn_deficiencyDensityFin3 (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) :
    ContinuousOn (M.deficiencyDensityFin3 χ) M.Dfin3 := by
  intro v hv
  have hx : (v 0, v 2) ∈ M.W := hv.1
  have hβ : ContinuousAt M.S.O.germ.β (v 0, v 2) := by
    have hs0 := M.continuousAt_s0 hx
    have heq : M.S.O.germ.β = fun x => M.s0 x + M.S.ε₀ := by
      funext x
      simp [ForwardMaximalSheet.s0]
    rw [heq]
    exact hs0.add continuousAt_const
  apply ContinuousAt.continuousWithinAt
  unfold deficiencyDensityFin3
  have h0 : ContinuousAt (fun w : Fin 3 → ℝ => w 0) v := continuousAt_apply 0 v
  have h1 : ContinuousAt (fun w : Fin 3 → ℝ => w 1) v := continuousAt_apply 1 v
  have h2 : ContinuousAt (fun w : Fin 3 → ℝ => w 2) v := continuousAt_apply 2 v
  have h02 : ContinuousAt (fun w : Fin 3 → ℝ => (w 0, w 2)) v := h0.prodMk h2
  have hχ' : ContinuousAt (fun w : Fin 3 → ℝ => χ (w 0, w 2)) v :=
    hχ.continuousAt.comp h02
  have hs : ContinuousAt (fun w : Fin 3 → ℝ => (w 1 : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp h1
  have hβ' : ContinuousAt (fun w : Fin 3 → ℝ => (M.S.O.germ.β (w 0, w 2) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp
      (hβ.comp_of_eq h02 rfl)
  exact hχ'.mul (Complex.continuous_exp.continuousAt.comp (hs.sub hβ'))

/-- The maximal-sheet zero extension is measurable. -/
theorem measurable_uMinus (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) : Measurable (M.uMinus χ) := by
  classical
  by_cases hD : M.Dfin3.Nonempty
  · obtain ⟨v0, hv0⟩ := hD
    letI : Nonempty M.Dfin3 := ⟨⟨v0, hv0⟩⟩
    let e := M.measurableEmbedding_PsiFin3
    let g : (Fin 3 → ℝ) → ℂ := fun q =>
      M.deficiencyDensityFin3 χ (e.invFun q).1
    have hg : Measurable g := by
      exact (M.continuousOn_deficiencyDensityFin3 χ hχ).restrict.measurable.comp
        e.measurable_invFun
    have heq : M.uMinus χ = Set.piecewise (M.PsiFin3 '' M.Dfin3) g 0 := by
      funext q
      by_cases hq : q ∈ M.PsiFin3 '' M.Dfin3
      · rcases hq with ⟨v, hv, rfl⟩
        rw [M.uMinus_on_image χ hv]
        have himem : M.PsiFin3 v ∈ M.PsiFin3 '' M.Dfin3 := ⟨v, hv, rfl⟩
        rw [Set.piecewise_eq_of_mem _ _ _ himem]
        change M.deficiencyDensityFin3 χ v =
          M.deficiencyDensityFin3 χ (e.invFun (M.PsiFin3 v)).1
        rw [show e.invFun (M.PsiFin3 v) = ⟨v, hv⟩ from
          e.leftInverse_invFun ⟨v, hv⟩]
      · rw [M.uMinus_off_image χ hq]
        simp [Set.piecewise, hq]
    rw [heq]
    exact hg.piecewise
      (measurable_image_of_fderivWithin M.measurableSet_Dfin3
        (fun v hv => M.hasFDerivWithinAt_PsiFin3 hv) M.injOn_PsiFin3) measurable_const
  · have hEmpty : M.Dfin3 = ∅ := not_nonempty_iff_eq_empty.mp hD
    rw [show M.uMinus χ = 0 by
      funext q
      simp [ForwardMaximalSheet.uMinus, hEmpty]]
    exact measurable_const

theorem aestronglyMeasurable_uMinus (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) :
    AEStronglyMeasurable (M.uMinus χ) volume :=
  (M.measurable_uMinus χ hχ).aestronglyMeasurable

/-- A fixed upper and lower bound for the wall height on the nonzero part of
the cutoff gives the required parameter-space square-integrability.  This is
the useful exhaustion-free form of the fiber estimate. -/
theorem integrableOn_sq_norm_deficiencyDensityFin3_of_beta_bounds
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (A B : ℝ)
    (hA : ∀ x ∈ M.W, χ x ≠ 0 → M.S.O.germ.β x ≤ A)
    (hB : ∀ x ∈ M.W, χ x ≠ 0 → B ≤ M.S.O.germ.β x) :
    IntegrableOn (fun v : Fin 3 → ℝ => ‖M.deficiencyDensityFin3 χ v‖ ^ 2)
      M.Dfin3 volume := by
  classical
  let base : (ℝ × ℝ) → ℝ := fun x => ‖χ x‖ ^ 2
  let tail : ℝ → ℝ := fun s => (Set.Iic A).indicator (fun t => Real.exp (2 * (t - B))) s
  have hbase : Integrable base (volume : Measure (ℝ × ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hχ.aestronglyMeasurable).mp
      (hχ.memLp_of_hasCompactSupport hχc)
  have htail : Integrable tail (volume : Measure ℝ) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    have h := (integrableOn_exp_mul_Iic (show (0 : ℝ) < 2 by norm_num) A).const_mul
      (Real.exp (-2 * B))
    change Integrable (fun t => Real.exp (2 * (t - B)))
      (volume.restrict (Iic A))
    convert h using 1
    funext t
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hprod : Integrable (fun p : (ℝ × ℝ) × ℝ => base p.1 * tail p.2)
      (volume : Measure ((ℝ × ℝ) × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact hbase.mul_prod htail
  have hmajor : Integrable (fun v : Fin 3 → ℝ =>
      base (v 0, v 2) * tail (v 1)) volume := by
    have h := (measurePreserving_flowParamToFin3_symm.integrable_comp_emb
      flowParamToFin3.symm.toHomeomorph.measurableEmbedding
      (g := fun p : (ℝ × ℝ) × ℝ => base p.1 * tail p.2)).mpr hprod
    convert h using 1
    funext v
    rfl
  let f : (Fin 3 → ℝ) → ℝ := M.Dfin3.indicator
    (fun v => ‖M.deficiencyDensityFin3 χ v‖ ^ 2)
  have hfmeas : AEStronglyMeasurable f volume := by
    apply Measurable.aestronglyMeasurable
    apply ContinuousOn.measurable_piecewise _ continuous_zero.continuousOn
      M.measurableSet_Dfin3
    intro v hv
    exact ((M.continuousOn_deficiencyDensityFin3 χ hχ v hv).norm.pow 2)
  have hf : Integrable f volume := by
    apply Integrable.mono hmajor hfmeas
    filter_upwards with v
    by_cases hv : v ∈ M.Dfin3
    · change ‖M.Dfin3.indicator
          (fun w => ‖M.deficiencyDensityFin3 χ w‖ ^ 2) v‖ ≤ _
      rw [Set.indicator_of_mem hv]
      have ht := M.time_lt_beta_of_mem_Dfin3 hv
      by_cases hχv : χ (v 0, v 2) = 0
      · simp [f, deficiencyDensityFin3, base, hχv]
      · have hAv := hA (v 0, v 2) hv.1 hχv
        have hBv := hB (v 0, v 2) hv.1 hχv
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
          (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _))]
        simp only [base, tail, deficiencyDensityFin3, norm_mul, mul_pow,
          Complex.norm_exp, Complex.sub_re, Complex.ofReal_re]
        rw [Set.indicator_of_mem (show v 1 ∈ Iic A from ht.le.trans hAv)]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [pow_two, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
    · simp [f, hv]
      positivity
  exact (integrable_indicator_iff M.measurableSet_Dfin3).mp hf

/-- Compact support strictly inside the transverse open set supplies the
uniform wall-height bounds used by the preceding estimate. -/
theorem integrableOn_sq_norm_deficiencyDensityFin3
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) :
    IntegrableOn (fun v : Fin 3 → ℝ => ‖M.deficiencyDensityFin3 χ v‖ ^ 2)
      M.Dfin3 volume := by
  have hβcont : ContinuousOn M.S.O.germ.β (tsupport χ) := by
    intro x hx
    have hs0 := M.continuousAt_s0 (hχW hx)
    have heq : M.S.O.germ.β = fun y => M.s0 y + M.S.ε₀ := by
      funext y
      simp [ForwardMaximalSheet.s0]
    rw [heq]
    exact (hs0.add continuousAt_const).continuousWithinAt
  obtain ⟨A, hA⟩ := hχc.bddAbove_image hβcont
  obtain ⟨B, hB⟩ := hχc.bddBelow_image hβcont
  apply M.integrableOn_sq_norm_deficiencyDensityFin3_of_beta_bounds
    χ hχ hχc A B
  · intro x hx hne
    exact hA ⟨x, subset_tsupport _ (Function.mem_support.mpr hne), rfl⟩
  · intro x hx hne
    exact hB ⟨x, subset_tsupport _ (Function.mem_support.mpr hne), rfl⟩

theorem integrableOn_sq_norm_uMinus_image (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) :
    IntegrableOn (fun q : Fin 3 → ℝ => ‖M.uMinus χ q‖ ^ 2)
      (M.PsiFin3 '' M.Dfin3) volume := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume M.measurableSet_Dfin3 (fun v hv => M.hasFDerivWithinAt_PsiFin3 hv)
    M.injOn_PsiFin3]
  have hd := M.integrableOn_sq_norm_deficiencyDensityFin3 χ hχ hχc hχW
  apply IntegrableOn.congr_fun (hd.const_mul (1 / 2 : ℝ)) _ M.measurableSet_Dfin3
  intro v hv
  dsimp only
  rw [M.abs_det_fderiv_PsiFin3 hv, M.uMinus_on_image χ hv]
  norm_num [smul_eq_mul]

theorem integrable_sq_norm_uMinus (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) :
    Integrable (fun q : Fin 3 → ℝ => ‖M.uMinus χ q‖ ^ 2) volume := by
  let S := M.PsiFin3 '' M.Dfin3
  have hi := M.integrableOn_sq_norm_uMinus_image χ hχ hχc hχW
  rw [← integrable_indicator_iff
    (measurable_image_of_fderivWithin M.measurableSet_Dfin3
      (fun v hv => M.hasFDerivWithinAt_PsiFin3 hv) M.injOn_PsiFin3)] at hi
  have hind : S.indicator (fun q : Fin 3 → ℝ => ‖M.uMinus χ q‖ ^ 2) =
      fun q => ‖M.uMinus χ q‖ ^ 2 := by
    funext q
    by_cases hq : q ∈ S
    · simp [hq]
    · simp [S, hq, M.uMinus_off_image χ hq]
  rwa [hind] at hi

/-- The maximal-sheet zero extension belongs to ambient `L²(ℝ³)`. -/
theorem memLp_uMinus (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) : MemLp (M.uMinus χ) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (M.aestronglyMeasurable_uMinus χ hχ)).mpr
  exact M.integrable_sq_norm_uMinus χ hχ hχc hχW

/-- A nonzero continuous compactly supported cutoff can be chosen with
topological support contained in the transverse open set. -/
theorem exists_baseCutoff_tsupport_subset (M : ForwardMaximalSheet) (x : ℝ × ℝ)
    (hx : x ∈ M.W) :
    ∃ χ : ℝ × ℝ → ℂ, Continuous χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ M.W ∧ χ x = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp M.isOpen_W x hx
  let b : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let χ : ℝ × ℝ → ℂ := fun y => (b y : ℂ)
  refine ⟨χ, Complex.continuous_ofReal.comp b.continuous,
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero,
    ?_, ?_⟩
  · have hsupp : Function.support χ = Function.support b := by
      ext y
      simp [χ]
    have hts : tsupport χ = tsupport b := congrArg closure hsupp
    rw [hts, b.tsupport_eq]
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    have hyr : dist y x ≤ ε / 2 := by simpa [Metric.mem_closedBall] using hy
    linarith
  · change (b x : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    norm_num

/-- A cutoff which is nonzero at one transverse point gives a strictly positive
squared-norm integral on the maximal-sheet image. -/
theorem lintegral_sq_norm_uMinus_image_pos (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) {x : ℝ × ℝ}
    (hx : x ∈ M.W) (hχx : χ x ≠ 0) :
    0 < ∫⁻ q in M.PsiFin3 '' M.Dfin3,
      ENNReal.ofReal (‖M.uMinus χ q‖ ^ 2) ∂volume := by
  classical
  let v0 : Fin 3 → ℝ := ![x.1, M.s0 x, x.2]
  have hzero : 0 ∈ integralCurveDomain (M.S.qSigma x) := by
    obtain ⟨α, I, hα⟩ := exists_isIntegralCurveFrom (M.S.qSigma x)
    exact ⟨α, I, hα, hα.1⟩
  have hv0 : v0 ∈ M.Dfin3 := by
    change x ∈ M.W ∧ M.s0 x - M.s0 x ∈ integralCurveDomain (M.S.qSigma x)
    simpa using And.intro hx hzero
  let g : (Fin 3 → ℝ) → ℝ := fun v => ‖M.deficiencyDensityFin3 χ v‖ ^ 2
  let r : (Fin 3 → ℝ) → ℝ := M.Dfin3.indicator g
  let f : (Fin 3 → ℝ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (r v)
  have hdens : M.deficiencyDensityFin3 χ v0 ≠ 0 := by
    simp only [deficiencyDensityFin3, mul_ne_zero_iff]
    exact ⟨by simpa [v0] using hχx, Complex.exp_ne_zero _⟩
  have hg0 : 0 < g v0 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hdens)
  have hg : ContinuousOn g M.Dfin3 := by
    intro v hv
    exact ((M.continuousOn_deficiencyDensityFin3 χ hχ v hv).norm.pow 2)
  let N : Set (Fin 3 → ℝ) := M.Dfin3 ∩ {v | 0 < g v}
  have hNopen : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    intro v hv
    exact inter_mem (M.isOpen_Dfin3.mem_nhds hv.1)
      ((hg v hv.1).continuousAt (M.isOpen_Dfin3.mem_nhds hv.1)
        (Ioi_mem_nhds hv.2))
  have hvN : v0 ∈ N := ⟨hv0, hg0⟩
  have hNpos : 0 < volume N := hNopen.measure_pos volume ⟨v0, hvN⟩
  have hr : Measurable r := by
    apply ContinuousOn.measurable_piecewise _ continuous_zero.continuousOn
      M.measurableSet_Dfin3
    intro v hv
    exact hg v hv
  have hf : Measurable f := by
    apply Measurable.const_mul
    apply ENNReal.measurable_ofReal.comp
    exact hr
  have hsub : N ⊆ Function.support f ∩ M.Dfin3 := by
    intro v hv
    refine ⟨?_, hv.1⟩
    have hgv : 0 < g v := hv.2
    simp only [Function.mem_support, f, ne_eq, mul_eq_zero,
      ENNReal.ofReal_eq_zero]
    exact not_or_intro (by norm_num) (not_le.mpr (by simpa [r, hv.1] using hgv))
  rw [M.lintegral_image_PsiFin3_eq]
  have hpos : 0 < ∫⁻ v in M.Dfin3, f v ∂volume := by
    apply (setLIntegral_pos_iff hf).mpr
    exact lt_of_lt_of_le hNpos (measure_mono hsub)
  convert hpos using 1
  apply setLIntegral_congr_fun M.measurableSet_Dfin3
  intro v hv
  simp [f, r, g, hv, M.uMinus_on_image χ hv]

/-- Every maximal forward sheet carries a compactly supported cutoff whose
zero extension determines a nonzero vector of ambient `L²(ℝ³)`. -/
theorem exists_nonzero_L2_uMinus (M : ForwardMaximalSheet) :
    ∃ (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
        (hχW : tsupport χ ⊆ M.W),
      (M.memLp_uMinus χ hχ hχc hχW).toLp (M.uMinus χ) ≠ 0 := by
  obtain ⟨x, hx⟩ := M.nonempty_W
  obtain ⟨χ, hχ, hχc, hχW, hχx⟩ := M.exists_baseCutoff_tsupport_subset x hx
  refine ⟨χ, hχ, hχc, hχW, ?_⟩
  let hu := M.memLp_uMinus χ hχ hχc hχW
  have himage := M.lintegral_sq_norm_uMinus_image_pos χ hχ hx (by simpa [hχx])
  intro hzero
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero] at hzero
  have huae : M.uMinus χ =ᵐ[volume] 0 := hu.coeFn_toLp.symm.trans hzero
  have hamb : ∫⁻ q : Fin 3 → ℝ,
      ENNReal.ofReal (‖M.uMinus χ q‖ ^ 2) ∂volume = 0 := by
    rw [← lintegral_zero]
    apply lintegral_congr_ae
    filter_upwards [huae] with q hq
    simp [hq]
  have hz : ∫⁻ q in M.PsiFin3 '' M.Dfin3,
      ENNReal.ofReal (‖M.uMinus χ q‖ ^ 2) ∂volume = 0 := by
    apply le_zero_iff.mp
    exact (setLIntegral_le_lintegral _ _).trans_eq hamb
  exact (ne_of_gt himage) hz

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
