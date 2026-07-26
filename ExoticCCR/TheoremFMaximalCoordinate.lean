/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFSaturatedSheet
import ExoticCCR.TheoremFBranchDensity

/-!
# The anchor coordinate along maximal `X1` trajectories

This module proves the chain-rule input for locating a maximal trajectory in
the target `s` coordinate.  It does not identify either maximal endpoint with
the forward wall; that requires an additional global component/range argument.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped Topology

namespace ExoticCCR

/-- The positive-time reparameterization of a branch cross-section by `X1`
flow time.  Its useful domain is the interval before `ε₀`. -/
def ForwardBranchCrossSection.branchTimeCurve (S : ForwardBranchCrossSection)
    (x : ℝ × ℝ) (t : ℝ) :=
  S.O.germ.branchMap (x, Real.sqrt (S.ε₀ - t))

/-- A fixed transverse parameter has the whole positive vertical branch segment
below the chosen cross-section.  This is deliberately a hypothesis: it does not
follow from the current `ForwardBranchOpen` API. -/
def ForwardBranchCrossSection.HasVerticalBranchSegment
    (S : ForwardBranchCrossSection) (x : ℝ × ℝ) : Prop :=
  ∀ τ ∈ Ioc (0 : ℝ) S.τ₀, (x, τ) ∈ S.O.W

/-- The square-root reparameterization of a vertical branch segment has
velocity exactly `X1`. -/
theorem ForwardBranchCrossSection.hasDerivAt_branchTimeCurve_of_mem
    (S : ForwardBranchCrossSection) (x : ℝ × ℝ) {t : ℝ}
    (ht : t < S.ε₀)
    (hmem : (x, Real.sqrt (S.ε₀ - t)) ∈ S.O.W) :
    HasDerivAt (S.branchTimeCurve x)
      (X1 (S.branchTimeCurve x t)) t := by
  let τ := Real.sqrt (S.ε₀ - t)
  have harg : 0 < S.ε₀ - t := sub_pos.mpr ht
  have hτ : 0 < τ := Real.sqrt_pos.2 harg
  have hp : (x, τ) ∈ S.O.Wpos := ⟨hmem, hτ⟩
  have hinner : HasDerivAt (fun u : ℝ => S.ε₀ - u) (-1) t :=
    (hasDerivAt_id t).const_sub S.ε₀
  have hsqrtOuter : HasDerivAt Real.sqrt (1 / (2 * τ)) (S.ε₀ - t) := by
    simpa [τ, Real.sq_sqrt harg.le] using Real.hasDerivAt_sqrt (ne_of_gt harg)
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (S.ε₀ - u))
      ((1 / (2 * τ)) * (-1)) t :=
    hsqrtOuter.comp t hinner
  have hbranch := S.O.hasDerivAt_branchMap_tau hp
  have hcomp := hbranch.scomp t hsqrt
  have hscalar : ((1 / (2 * τ)) * (-1)) •
      ((-2 * τ) • X1 (S.O.germ.branchMap (x, τ))) =
      X1 (S.O.germ.branchMap (x, τ)) := by
    rw [smul_smul]
    have hτ0 : τ ≠ 0 := ne_of_gt hτ
    field_simp
    simp
  rw [hasDerivAt_pi]
  intro i
  simpa only [branchTimeCurve, τ, Function.comp_apply] using
    hasDerivAt_pi.mp (hcomp.congr_deriv hscalar) i

/-- On a full vertical segment, every strictly positive time before the wall is
an `X1`-time for the reparameterized branch. -/
theorem ForwardBranchCrossSection.hasDerivAt_branchTimeCurve
    (S : ForwardBranchCrossSection) {x : ℝ × ℝ}
    (hvert : S.HasVerticalBranchSegment x) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) S.ε₀) :
    HasDerivAt (S.branchTimeCurve x)
      (X1 (S.branchTimeCurve x t)) t := by
  have harg : 0 < S.ε₀ - t := sub_pos.mpr ht.2
  have hτpos : 0 < Real.sqrt (S.ε₀ - t) := Real.sqrt_pos.2 harg
  have hτle : Real.sqrt (S.ε₀ - t) ≤ S.τ₀ := by
    rw [← S.sqrt_ε₀]
    exact Real.sqrt_le_sqrt (by linarith [ht.1])
  exact S.hasDerivAt_branchTimeCurve_of_mem x ht.2
    (hvert _ ⟨hτpos, hτle⟩)

/-- A vertical branch segment extends slightly backward from the cross-section
by openness, so the branch reparameterization itself is a connected open
integral curve through `qSigma`. -/
theorem ForwardBranchCrossSection.exists_branch_isIntegralCurveFrom
    (S : ForwardBranchCrossSection) {x : ℝ × ℝ} (hx : x ∈ S.W)
    (hvert : S.HasVerticalBranchSegment x) :
    ∃ η > 0, isIntegralCurveFrom (S.qSigma x) (S.branchTimeCurve x)
      (Ioo (-η) S.ε₀) := by
  have hxW : (x, S.τ₀) ∈ S.O.W := by simpa [S.W_eq] using hx
  let p : ℝ → (ℝ × ℝ) × ℝ := fun t => (x, Real.sqrt (S.ε₀ - t))
  have hp0 : p 0 = (x, S.τ₀) := by simp [p, S.sqrt_ε₀]
  have hpcont : ContinuousAt p 0 := by
    apply ContinuousAt.prodMk continuousAt_const
    exact Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hpre : p ⁻¹' S.O.W ∈ 𝓝 0 := by
    apply hpcont
    rw [hp0]
    exact S.O.isOpen_W.mem_nhds hxW
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let η := min (r / 2) (S.ε₀ / 2)
  have hη : 0 < η := lt_min (half_pos hr) (half_pos S.ε₀_pos)
  refine ⟨η, hη, ?_⟩
  have hzero : S.branchTimeCurve x 0 = S.qSigma x := by
    simp [branchTimeCurve, qSigma, S.sqrt_ε₀]
  refine ⟨by constructor <;> linarith [hη, S.ε₀_pos], isOpen_Ioo,
    isConnected_Ioo (by linarith [hη, S.ε₀_pos]), hzero, ?_⟩
  intro t ht
  apply S.hasDerivAt_branchTimeCurve_of_mem x ht.2
  by_cases htnonneg : 0 ≤ t
  · have harg : 0 < S.ε₀ - t := sub_pos.mpr ht.2
    have hτpos : 0 < Real.sqrt (S.ε₀ - t) := Real.sqrt_pos.2 harg
    have hτle : Real.sqrt (S.ε₀ - t) ≤ S.τ₀ := by
      rw [← S.sqrt_ε₀]
      exact Real.sqrt_le_sqrt (by linarith)
    exact hvert _ ⟨hτpos, hτle⟩
  · apply hball
    rw [Metric.mem_ball, dist_zero_right]
    have htneg : t < 0 := lt_of_not_ge htnonneg
    have hteta : |t| < η := by rw [abs_of_neg htneg]; linarith [ht.1]
    exact lt_of_lt_of_le hteta (min_le_left _ _ |>.trans (by linarith))

/-- The full anchor map has constant velocity `(0,1,0)` along an `X1`
integral curve. -/
theorem hasDerivAt_evalMap_F_of_hasDerivAt_X1 {α : ℝ → R3} {t : ℝ}
    (hα : HasDerivAt α (X1 (α t)) t) :
    HasDerivAt (fun u => evalMap (F ℝ) (α u)) (![0, 1, 0] : R3) t := by
  have h := (hasFDerivAt_evalMap_F (α t)).comp_hasDerivAt t hα
  exact h.congr_deriv (evalJacobianF_apply_X1 (α t))

/-- In particular, the middle anchor coordinate has derivative one. -/
theorem hasDerivAt_evalMap_F_coord1_of_hasDerivAt_X1 {α : ℝ → R3} {t : ℝ}
    (hα : HasDerivAt α (X1 (α t)) t) :
    HasDerivAt (fun u => evalMap (F ℝ) (α u) 1) 1 t := by
  simpa using hasDerivAt_pi.mp (hasDerivAt_evalMap_F_of_hasDerivAt_X1 hα) 1

/-- The middle anchor coordinate is affine with slope one on every connected
open partial trajectory. -/
theorem isIntegralCurveFrom.evalMap_F_coord1
    {x₀ : R3} {α : ℝ → R3} {I : Set ℝ}
    (hα : isIntegralCurveFrom x₀ α I) {t : ℝ} (ht : t ∈ I) :
    evalMap (F ℝ) (α t) 1 = evalMap (F ℝ) x₀ 1 + t := by
  let f : ℝ → ℝ := fun u => evalMap (F ℝ) (α u) 1
  let g : ℝ → ℝ := fun u => evalMap (F ℝ) x₀ 1 + u
  have hf : DifferentiableOn ℝ f I := by
    intro u hu
    exact (hasDerivAt_evalMap_F_coord1_of_hasDerivAt_X1
      (hα.2.2.2.2 u hu)).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ g I := by
    intro u hu
    exact ((hasDerivAt_const u (evalMap (F ℝ) x₀ 1)).add
      (hasDerivAt_id u)).differentiableAt.differentiableWithinAt
  have hd : I.EqOn (deriv f) (deriv g) := by
    intro u hu
    rw [(hasDerivAt_evalMap_F_coord1_of_hasDerivAt_X1
      (hα.2.2.2.2 u hu)).deriv]
    simpa [g] using (((hasDerivAt_const u (evalMap (F ℝ) x₀ 1)).add
      (hasDerivAt_id u)).deriv).symm
  have hfg : I.EqOn f g := hα.2.1.eqOn_of_deriv_eq hα.2.2.1.2 hf hg hd hα.1 (by
    simp [f, g, hα.2.2.2.1])
  exact hfg ht

/-- The chosen maximal representative has the same affine target coordinate
throughout its maximal domain. -/
theorem evalMap_maximalIntegralCurve_coord1
    {x₀ : R3} {t : ℝ} (ht : t ∈ integralCurveDomain x₀) :
    evalMap (F ℝ) (maximalIntegralCurve x₀ t) 1 = evalMap (F ℝ) x₀ 1 + t := by
  obtain ⟨α, I, hα, htI⟩ := ht
  rw [maximalIntegralCurve_eq_of_mem hα htI]
  exact hα.evalMap_F_coord1 htI

/-- For a cross-section initial point, flow time and target `s` differ by the
fixed initial offset `β(x)-ε₀`. -/
theorem ForwardBranchCrossSection.evalMap_maximalIntegralCurve_coord1
    (S : ForwardBranchCrossSection) {x : ℝ × ℝ} (hx : x ∈ S.W)
    {t : ℝ} (ht : t ∈ integralCurveDomain (S.qSigma x)) :
    evalMap (F ℝ) (maximalIntegralCurve (S.qSigma x) t) 1 =
      S.O.germ.β x - S.ε₀ + t := by
  rw [ExoticCCR.evalMap_maximalIntegralCurve_coord1 ht]
  have hq := S.evalMap_qSigma hx
  have hq1 := congrFun hq (1 : Fin 3)
  simpa using hq1

/-- A full vertical segment identifies the forward maximal time with `ε₀` as
soon as the corresponding fixed-parameter branch is known to escape at that
endpoint.  The escape hypothesis is explicit because the current branch API
only proves escape while the whole parameter tends to the distinguished base,
not along every fixed transverse vertical line. -/
theorem ForwardBranchCrossSection.tMax_qSigma_eq_ε₀_of_escape
    (S : ForwardBranchCrossSection) {x : ℝ × ℝ} (hx : x ∈ S.W)
    (hvert : S.HasVerticalBranchSegment x)
    (hescape : Tendsto (fun t : ℝ => ‖S.branchTimeCurve x t‖)
      (𝓝[<] S.ε₀) atTop) :
    tMax (S.qSigma x) = (S.ε₀ : EReal) := by
  obtain ⟨η, hη, hcurve⟩ := S.exists_branch_isIntegralCurveFrom hx hvert
  have hzeroDom : 0 ∈ integralCurveDomain (S.qSigma x) :=
    ⟨S.branchTimeCurve x, Ioo (-η) S.ε₀, hcurve, hcurve.1⟩
  have hends := (mem_integralCurveDomain_iff (S.qSigma x) 0).1 hzeroDom
  have hεnot : S.ε₀ ∉ integralCurveDomain (S.qSigma x) := by
    intro hεDom
    have hmaxDeriv := hasDerivAt_maximalIntegralCurve
      ((mem_integralCurveDomain_iff (S.qSigma x) S.ε₀).1 hεDom)
    have hfinite : Tendsto
        (fun t : ℝ => ‖maximalIntegralCurve (S.qSigma x) t‖)
        (𝓝[<] S.ε₀) (𝓝 ‖maximalIntegralCurve (S.qSigma x) S.ε₀‖) :=
      hmaxDeriv.continuousAt.norm.tendsto.mono_left inf_le_left
    have heq : (fun t : ℝ => ‖maximalIntegralCurve (S.qSigma x) t‖) =ᶠ[𝓝[<] S.ε₀]
        (fun t : ℝ => ‖S.branchTimeCurve x t‖) := by
      filter_upwards [Ioo_mem_nhdsLT (show -η < S.ε₀ by linarith [hη, S.ε₀_pos])]
        with t ht
      rw [maximalIntegralCurve_eq_of_mem hcurve ht]
    have hlarge : ∀ᶠ t in 𝓝[<] S.ε₀,
        ‖maximalIntegralCurve (S.qSigma x) S.ε₀‖ + 1 ≤
          ‖S.branchTimeCurve x t‖ :=
      hescape.eventually_ge_atTop (‖maximalIntegralCurve (S.qSigma x) S.ε₀‖ + 1)
    have hsmall : ∀ᶠ t in 𝓝[<] S.ε₀,
        ‖maximalIntegralCurve (S.qSigma x) t‖ <
          ‖maximalIntegralCurve (S.qSigma x) S.ε₀‖ + 1 :=
      hfinite (Iio_mem_nhds (by linarith))
    obtain ⟨t, htlarge, htsmall, hteq⟩ :=
      (hlarge.and (hsmall.and heq)).exists
    change ‖maximalIntegralCurve (S.qSigma x) t‖ =
      ‖S.branchTimeCurve x t‖ at hteq
    rw [← hteq] at htlarge
    linarith
  have hupper : tMax (S.qSigma x) ≤ (S.ε₀ : EReal) := by
    have hnot := mt (mem_integralCurveDomain_iff (S.qSigma x) S.ε₀).2 hεnot
    have hlower : tMin (S.qSigma x) < (S.ε₀ : EReal) :=
      hends.1.trans (EReal.coe_lt_coe_iff.mpr S.ε₀_pos)
    exact le_of_not_gt fun hgt => hnot ⟨hlower, hgt⟩
  apply le_antisymm hupper
  have hmaxPos : (0 : EReal) < tMax (S.qSigma x) := hends.2
  have hneTop : tMax (S.qSigma x) ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    exact EReal.coe_ne_top S.ε₀ (top_le_iff.mp hupper)
  have hneBot : tMax (S.qSigma x) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < tMax (S.qSigma x) from bot_lt_of_lt hmaxPos)
  have hcoe : ((tMax (S.qSigma x)).toReal : EReal) = tMax (S.qSigma x) :=
    EReal.coe_toReal hneTop hneBot
  by_contra hnot
  have hmaxLt : tMax (S.qSigma x) < (S.ε₀ : EReal) := lt_of_not_ge hnot
  have hTlt : (tMax (S.qSigma x)).toReal < S.ε₀ := by
    rw [← EReal.coe_lt_coe_iff, hcoe]
    exact hmaxLt
  have hTpos : 0 < (tMax (S.qSigma x)).toReal := by
    rw [← EReal.coe_lt_coe_iff, hcoe]
    exact hmaxPos
  let t := ((tMax (S.qSigma x)).toReal + S.ε₀) / 2
  have htI : t ∈ Ioo (-η) S.ε₀ := by
    dsimp [t]
    constructor <;> linarith [hη, hTpos, hTlt]
  have htDom : t ∈ integralCurveDomain (S.qSigma x) :=
    ⟨S.branchTimeCurve x, Ioo (-η) S.ε₀, hcurve, htI⟩
  have htUpper := ((mem_integralCurveDomain_iff (S.qSigma x) t).1 htDom).2
  rw [← hcoe] at htUpper
  have htReal : t < (tMax (S.qSigma x)).toReal := EReal.coe_lt_coe_iff.mp htUpper
  dsimp [t] at htReal
  linarith

end ExoticCCR
