/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFSaturatedSheet
import ExoticCCR.TheoremFBranchDensity

/-!
# The anchor coordinate along maximal `X1` trajectories

This module constructs a nonempty vertical collar at the distinguished wall,
proves fixed-parameter escape there, and identifies the resulting maximal
forward trajectory time with the wall offset.  It makes no sheet-smoothness or
weak-adjoint claim.
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
below the chosen cross-section. -/
def ForwardBranchCrossSection.HasVerticalBranchSegment
    (S : ForwardBranchCrossSection) (x : ℝ × ℝ) : Prop :=
  ∀ τ ∈ Ioc (0 : ℝ) S.τ₀, (x, τ) ∈ S.O.W

/-- Shrinking the positive half-ball in a forward branch gives a vertical
collar on which the numerator of the divided branch root stays uniformly
positive. -/
theorem ForwardBranchOpen.exists_crossSection_with_verticalCollar_and_rPlus
    (O : ForwardBranchOpen) :
    ∃ S : ForwardBranchCrossSection, S.O = O ∧
      ∃ W' : Set (ℝ × ℝ), IsOpen W' ∧ W'.Nonempty ∧ W' ⊆ S.W ∧
        ∀ x ∈ W', S.HasVerticalBranchSegment x ∧
          ∀ τ ∈ Ioc (0 : ℝ) S.τ₀, 1 ≤ O.germ.rPlus (x, τ) := by
  obtain ⟨ε, hε, hball⟩ := O.exists_positive_ball_subset
  have hrcont : ContinuousAt O.germ.rPlus (((0, 2), 0) : (ℝ × ℝ) × ℝ) :=
    (O.germ.contDiff_rPlus.contDiffAt
      (O.germ.isOpen_V.mem_nhds O.germ.base_tau_mem)).continuousAt
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hrnh : {p | 1 < O.germ.rPlus p} ∈
      𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ) := by
    change O.germ.rPlus ⁻¹' Ioi 1 ∈ 𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ)
    apply hrcont
    simpa [O.germ.rPlus_base] using Ioi_mem_nhds hsqrt
  obtain ⟨δ, hδ, hballr⟩ := Metric.mem_nhds_iff.mp hrnh
  let r := min ε δ
  let τ₀ := r / 2
  let W : Set (ℝ × ℝ) := {x | (x, τ₀) ∈ O.W}
  let W' : Set (ℝ × ℝ) := Metric.ball (0, 2) (r / 2)
  have hr : 0 < r := lt_min hε hδ
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; linarith
  have hcollar : ∀ x ∈ W', ∀ τ ∈ Ioc (0 : ℝ) τ₀, (x, τ) ∈ O.W := by
    intro x hx τ hτ
    apply hball
    constructor
    · rw [Metric.mem_ball, Prod.dist_eq]
      have hx' : dist x (0, 2) < r / 2 := by simpa [W'] using hx
      have hτdist : dist τ 0 < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hτ.1]
        dsimp [τ₀] at hτ
        exact hτ.2.trans_lt ((half_lt_self hr).trans_le (min_le_left ε δ))
      exact max_lt (hx'.trans (half_lt_self hr) |>.trans_le (min_le_left ε δ)) hτdist
    · exact hτ.1
  have hrplus : ∀ x ∈ W', ∀ τ ∈ Ioc (0 : ℝ) τ₀,
      1 ≤ O.germ.rPlus (x, τ) := by
    intro x hx τ hτ
    apply le_of_lt
    apply hballr
    rw [Metric.mem_ball, Prod.dist_eq]
    have hx' : dist x (0, 2) < r / 2 := by simpa [W'] using hx
    have hτdist : dist τ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hτ.1]
      dsimp [τ₀] at hτ
      exact hτ.2.trans_lt ((half_lt_self hr).trans_le (min_le_right ε δ))
    exact max_lt (hx'.trans (half_lt_self hr) |>.trans_le (min_le_right ε δ)) hτdist
  have hWopen : IsOpen W := by
    exact O.isOpen_W.preimage (by fun_prop : Continuous fun x : ℝ × ℝ => (x, τ₀))
  have hW'open : IsOpen W' := Metric.isOpen_ball
  have hbaseW' : (0, 2) ∈ W' := by simp [W', hr]
  have hW'sub : W' ⊆ W := by
    intro x hx
    exact hcollar x hx τ₀ ⟨hτ₀, le_rfl⟩
  let S : ForwardBranchCrossSection :=
    ⟨O, τ₀, hτ₀, W, rfl, hWopen, ⟨(0, 2), hW'sub hbaseW'⟩⟩
  refine ⟨S, rfl, W', hW'open, ⟨(0, 2), hbaseW'⟩, ?_, ?_⟩
  · simpa [S] using hW'sub
  · intro x hx
    exact ⟨fun τ hτ => hcollar x hx τ hτ,
      by simpa [S] using hrplus x hx⟩

/-- Every forward branch therefore has a nonempty open cross-section carrying
full vertical branch segments down to the wall. -/
theorem ForwardBranchOpen.exists_crossSection_with_verticalCollar
    (O : ForwardBranchOpen) :
    ∃ S : ForwardBranchCrossSection, S.O = O ∧
      ∃ W' : Set (ℝ × ℝ), IsOpen W' ∧ W'.Nonempty ∧ W' ⊆ S.W ∧
        ∀ x ∈ W', S.HasVerticalBranchSegment x := by
  obtain ⟨S, hSO, W', hWopen, hWne, hWsub, h⟩ :=
    O.exists_crossSection_with_verticalCollar_and_rPlus
  exact ⟨S, hSO, W', hWopen, hWne, hWsub, fun x hx => (h x hx).1⟩

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

/-- A uniform positive lower bound for the divided branch root numerator makes
the fixed-parameter branch escape when its vertical parameter tends to zero. -/
theorem ForwardBranchCrossSection.tendsto_norm_branchTimeCurve_of_one_le_rPlus
    (S : ForwardBranchCrossSection) (x : ℝ × ℝ)
    (hr : ∀ τ ∈ Ioc (0 : ℝ) S.τ₀, 1 ≤ S.O.germ.rPlus (x, τ)) :
    Tendsto (fun t : ℝ => ‖S.branchTimeCurve x t‖)
      (𝓝[<] S.ε₀) atTop := by
  let τ : ℝ → ℝ := fun t => Real.sqrt (S.ε₀ - t)
  have hτzero : Tendsto τ (𝓝[<] S.ε₀) (𝓝 0) := by
    have hcont : ContinuousAt τ S.ε₀ := by
      dsimp [τ]
      fun_prop
    change Tendsto (fun t => Real.sqrt (S.ε₀ - t))
      (𝓝 S.ε₀ ⊓ 𝓟 (Iio S.ε₀)) (𝓝 0)
    simpa only [τ, sub_self, Real.sqrt_zero] using
      hcont.tendsto.mono_left inf_le_left
  have hτpos : ∀ᶠ t in 𝓝[<] S.ε₀, 0 < τ t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.sqrt_pos.2 (sub_pos.mpr ht)
  have hτGT : Tendsto τ (𝓝[<] S.ε₀) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hτzero, hτpos⟩
  have hinv : Tendsto (fun t => (τ t)⁻¹) (𝓝[<] S.ε₀) atTop :=
    hτGT.inv_tendsto_nhdsGT_zero
  have hnear : ∀ᶠ t in 𝓝[<] S.ε₀, t ∈ Ioo 0 S.ε₀ :=
    Ioo_mem_nhdsLT S.ε₀_pos
  have hτle : ∀ᶠ t in 𝓝[<] S.ε₀, τ t ≤ S.τ₀ := by
    filter_upwards [hnear] with t ht
    dsimp [τ]
    rw [← S.sqrt_ε₀]
    exact Real.sqrt_le_sqrt (by linarith [ht.1])
  have hq0 : Tendsto (fun t => S.O.germ.q0 (x, τ t))
      (𝓝[<] S.ε₀) atTop := by
    apply tendsto_atTop_mono' _ _ hinv
    filter_upwards [hτpos, hτle] with t htpos htle
    rw [ForwardBranchGerm.q0, div_eq_mul_inv]
    have hinvnonneg : 0 ≤ (τ t)⁻¹ := le_of_lt (inv_pos.2 htpos)
    simpa using mul_le_mul_of_nonneg_right (hr (τ t) ⟨htpos, htle⟩) hinvnonneg
  apply tendsto_atTop_mono' _ _ hq0
  filter_upwards with t
  calc
    S.O.germ.q0 (x, τ t) ≤ |S.O.germ.q0 (x, τ t)| := le_abs_self _
    _ ≤ ‖S.branchTimeCurve x t‖ := by
      rw [← S.O.branchMap_coord0_eq_q0 (x, τ t), Pi.norm_def]
      exact_mod_cast Finset.le_sup
        (f := fun b ↦ ‖S.O.germ.branchMap (x, τ t) b‖₊)
        (Finset.mem_univ (0 : Fin 3))

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

/-- On a nonempty open transverse set, the vertical branch reaches its wall at
exactly the maximal forward `X1` time.  No endpoint hypothesis remains in this
existence statement. -/
theorem ForwardBranchOpen.exists_crossSection_tMax_qSigma_eq_ε₀
    (O : ForwardBranchOpen) :
    ∃ S : ForwardBranchCrossSection, S.O = O ∧
      ∃ W' : Set (ℝ × ℝ), IsOpen W' ∧ W'.Nonempty ∧ W' ⊆ S.W ∧
        ∀ x ∈ W', tMax (S.qSigma x) = (S.ε₀ : EReal) := by
  obtain ⟨S, hSO, W', hWopen, hWne, hWsub, h⟩ :=
    O.exists_crossSection_with_verticalCollar_and_rPlus
  refine ⟨S, hSO, W', hWopen, hWne, hWsub, ?_⟩
  intro x hx
  have hvert := (h x hx).1
  have hr : ∀ τ ∈ Ioc (0 : ℝ) S.τ₀, 1 ≤ S.O.germ.rPlus (x, τ) := by
    simpa [hSO] using (h x hx).2
  exact S.tMax_qSigma_eq_ε₀_of_escape (hWsub hx) hvert
    (S.tendsto_norm_branchTimeCurve_of_one_le_rPlus x hr)

/-- The explicit vertical branch collar, reparameterized by the anchor `s`
coordinate, is a forward saturated sheet.  Its lower face is the regular
cross-section and is recorded by the regular-limit alternative of `lower_ok`;
it is not claimed to escape. -/
theorem ForwardBranchOpen.exists_forwardSaturatedSheet (O : ForwardBranchOpen) :
    Nonempty ForwardSaturatedSheet := by
  obtain ⟨S, hSO, W', hWopen, hWne, hWsub, hcollar⟩ :=
    O.exists_crossSection_with_verticalCollar_and_rPlus
  let β : ℝ × ℝ → ℝ := S.O.germ.β
  let ℓ : ℝ × ℝ → EReal := fun x => ((β x - S.ε₀ : ℝ) : EReal)
  let D : Set ((ℝ × ℝ) × ℝ) :=
    {p | p.1 ∈ W' ∧ β p.1 - S.ε₀ < p.2 ∧ p.2 < β p.1}
  let Psi : ((ℝ × ℝ) × ℝ) → R3 := fun p =>
    S.O.germ.branchMap (p.1, Real.sqrt (β p.1 - p.2))
  have hU : W' ⊆ S.O.germ.U := by
    intro x hx
    have hxW : (x, S.τ₀) ∈ S.O.W := by simpa [S.W_eq] using hWsub hx
    exact S.O.germ.proj_mem (x, S.τ₀) (S.O.subset_V hxW)
  have hβdiff : ContDiffOn ℝ ⊤ β W' :=
    S.O.germ.contDiff_β.mono hU
  have hlower : ∀ x ∈ W', ℓ x < (β x : EReal) := by
    intro x hx
    simp only [ℓ, EReal.coe_lt_coe_iff]
    linarith [S.ε₀_pos]
  have hDeq : D = {p | p.1 ∈ W' ∧ ℓ p.1 < (p.2 : EReal) ∧ p.2 < β p.1} := by
    ext p
    simp only [D, ℓ, Set.mem_setOf_eq, EReal.coe_lt_coe_iff]
  have hDopen : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hp' : p.1 ∈ W' ∧ β p.1 - S.ε₀ < p.2 ∧ p.2 < β p.1 := hp
    have hβat : ContinuousAt β p.1 :=
      (hβdiff p.1 hp'.1).contDiffAt (hWopen.mem_nhds hp'.1) |>.continuousAt
    have hbase : {q : (ℝ × ℝ) × ℝ | q.1 ∈ W'} ∈ 𝓝 p :=
      (hWopen.preimage continuous_fst).mem_nhds hp'.1
    have hloCont : ContinuousAt (fun q : (ℝ × ℝ) × ℝ => β q.1 - S.ε₀ - q.2) p :=
      ((hβat.comp continuousAt_fst).sub continuousAt_const).sub continuousAt_snd
    have hlo : {q : (ℝ × ℝ) × ℝ | β q.1 - S.ε₀ < q.2} ∈ 𝓝 p := by
      have heq : {q : (ℝ × ℝ) × ℝ | β q.1 - S.ε₀ < q.2} =
          (fun q => β q.1 - S.ε₀ - q.2) ⁻¹' Iio 0 := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
        constructor <;> intro h <;> linarith
      rw [heq]
      exact hloCont (Iio_mem_nhds (sub_neg.mpr hp'.2.1))
    have hhiCont : ContinuousAt (fun q : (ℝ × ℝ) × ℝ => q.2 - β q.1) p :=
      continuousAt_snd.sub (hβat.comp continuousAt_fst)
    have hhi : {q : (ℝ × ℝ) × ℝ | q.2 < β q.1} ∈ 𝓝 p := by
      have heq : {q : (ℝ × ℝ) × ℝ | q.2 < β q.1} =
          (fun q => q.2 - β q.1) ⁻¹' Iio 0 := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
        constructor <;> intro h <;> linarith
      rw [heq]
      exact hhiCont (Iio_mem_nhds (sub_neg.mpr hp'.2.2))
    apply mem_of_superset (inter_mem hbase (inter_mem hlo hhi))
    rintro q ⟨hqW, hqlo, hqhi⟩
    exact ⟨hqW, hqlo, hqhi⟩
  have hPsiDiff : ContDiffOn ℝ ⊤ Psi D := by
    intro p hp
    have hp' : p.1 ∈ W' ∧ β p.1 - S.ε₀ < p.2 ∧ p.2 < β p.1 := hp
    have harg : 0 < β p.1 - p.2 := sub_pos.mpr hp'.2.2
    have hτpos : 0 < Real.sqrt (β p.1 - p.2) := Real.sqrt_pos.2 harg
    have hτle : Real.sqrt (β p.1 - p.2) ≤ S.τ₀ := by
      rw [← S.sqrt_ε₀]
      exact Real.sqrt_le_sqrt (by linarith [hp'.2.1])
    have hmem : (p.1, Real.sqrt (β p.1 - p.2)) ∈ S.O.W :=
      (hcollar p.1 hp'.1).1 _ ⟨hτpos, hτle⟩
    have hβat : ContDiffAt ℝ ⊤ β p.1 :=
      (hβdiff p.1 hp'.1).contDiffAt (hWopen.mem_nhds hp'.1)
    have hinner : ContDiffAt ℝ ⊤
        (fun q : (ℝ × ℝ) × ℝ => (q.1, Real.sqrt (β q.1 - q.2))) p := by
      apply ContDiffAt.prodMk contDiffAt_fst
      apply ContDiffAt.sqrt
      · exact (hβat.comp p contDiffAt_fst).sub contDiffAt_snd
      · exact ne_of_gt harg
    have houter : ContDiffAt ℝ ⊤ S.O.germ.branchMap
        (p.1, Real.sqrt (β p.1 - p.2)) :=
      (S.O.contDiff_branchMap _ hmem).contDiffAt (S.O.isOpen_W.mem_nhds hmem)
    exact (houter.comp p hinner).contDiffWithinAt
  have hEval : ∀ p ∈ D,
      evalMap (F ℝ) (Psi p) = ![p.1.1, p.2, p.1.2] := by
    intro p hp
    have hp' : p.1 ∈ W' ∧ β p.1 - S.ε₀ < p.2 ∧ p.2 < β p.1 := hp
    have harg : 0 < β p.1 - p.2 := sub_pos.mpr hp'.2.2
    have hτpos : 0 < Real.sqrt (β p.1 - p.2) := Real.sqrt_pos.2 harg
    have hτle : Real.sqrt (β p.1 - p.2) ≤ S.τ₀ := by
      rw [← S.sqrt_ε₀]
      exact Real.sqrt_le_sqrt (by linarith [hp'.2.1])
    have hmem : (p.1, Real.sqrt (β p.1 - p.2)) ∈ S.O.W :=
      (hcollar p.1 hp'.1).1 _ ⟨hτpos, hτle⟩
    simpa [Psi, β, ForwardBranchGerm.sCoord, Real.sq_sqrt harg.le] using
      S.O.evalMap_branch hmem
  have hInj : Set.InjOn Psi D := by
    intro p hp q hq heq
    have heval : (![p.1.1, p.2, p.1.2] : Fin 3 → ℝ) =
        ![q.1.1, q.2, q.1.2] := by
      rw [← hEval p hp, ← hEval q hq, heq]
    have ha : p.1.1 = q.1.1 := by simpa using congrFun heval (0 : Fin 3)
    have hs : p.2 = q.2 := by simpa using congrFun heval (1 : Fin 3)
    have hc : p.1.2 = q.1.2 := by simpa using congrFun heval (2 : Fin 3)
    exact Prod.ext (Prod.ext ha hc) hs
  refine ⟨⟨W', hWopen, hWne, β, hβdiff, ℓ, hlower, D, hDeq, hDopen,
    Psi, hPsiDiff, hInj, hEval, ?_, ?_, ?_⟩⟩
  · intro x s hs
    have hs' : x ∈ W' ∧ β x - S.ε₀ < s ∧ s < β x := hs
    let t := s - (β x - S.ε₀)
    have ht : t ∈ Ioo (0 : ℝ) S.ε₀ := by
      dsimp [t]
      constructor <;> linarith [hs'.2.1, hs'.2.2]
    have hder := S.hasDerivAt_branchTimeCurve (hcollar x hs'.1).1 ht
    have hshift := hder.comp_add_const s (-(β x - S.ε₀))
    have hfun : (fun u : ℝ => S.branchTimeCurve x (u + -(β x - S.ε₀))) =
        (fun u : ℝ => Psi (x, u)) := by
      funext u
      simp only [ForwardBranchCrossSection.branchTimeCurve, Psi, β]
      apply congrArg (fun z => S.O.germ.branchMap (x, Real.sqrt z))
      ring
    rw [hfun] at hshift
    have hval : S.branchTimeCurve x t = Psi (x, s) := by
      simpa only [t, sub_eq_add_neg] using congrFun hfun s
    exact hshift.congr_deriv (congrArg X1 hval)
  · intro x hx
    have hesc := S.tendsto_norm_branchTimeCurve_of_one_le_rPlus x
      (by simpa [hSO] using (hcollar x hx).2)
    have hshift : Tendsto (fun s : ℝ => s - (β x - S.ε₀))
        (𝓝[<] β x) (𝓝[<] S.ε₀) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hc : ContinuousAt (fun s : ℝ => s - (β x - S.ε₀)) (β x) :=
          continuousAt_id.sub continuousAt_const
        have hct := hc.tendsto.mono_left
          (show 𝓝[<] β x ≤ 𝓝 (β x) from inf_le_left)
        convert hct using 1
        rw [sub_sub_cancel]
      · filter_upwards [self_mem_nhdsWithin] with s hs
        change s - (β x - S.ε₀) < S.ε₀
        calc
          s - (β x - S.ε₀) < β x - (β x - S.ε₀) := sub_lt_sub_right hs _
          _ = S.ε₀ := by ring
    change Tendsto (fun s : ℝ =>
      ‖S.O.germ.branchMap (x, Real.sqrt (β x - s))‖) (𝓝[<] β x) atTop
    have hcomp := hesc.comp hshift
    have hfun : (fun s : ℝ => ‖S.O.germ.branchMap (x, Real.sqrt (β x - s))‖) =
        (fun t => ‖S.branchTimeCurve x t‖) ∘
          (fun s : ℝ => s - (β x - S.ε₀)) := by
      funext s
      simp only [Function.comp_apply, ForwardBranchCrossSection.branchTimeCurve]
      apply congrArg norm
      apply congrArg (fun z => S.O.germ.branchMap (x, Real.sqrt z))
      ring
    rw [hfun]
    exact hcomp
  · intro x hx
    right; right
    refine ⟨β x - S.ε₀, rfl, S.qSigma x, ?_⟩
    have hxW : (x, S.τ₀) ∈ S.O.W := by simpa [S.W_eq] using hWsub hx
    have hbranch : ContinuousAt S.O.germ.branchMap (x, S.τ₀) :=
      (S.O.contDiff_branchMap _ hxW).contDiffAt (S.O.isOpen_W.mem_nhds hxW) |>.continuousAt
    have hinner : Tendsto (fun s : ℝ => (x, Real.sqrt (β x - s)))
        (𝓝[>] (β x - S.ε₀)) (𝓝 (x, S.τ₀)) := by
      have hc : ContinuousAt (fun s : ℝ => (x, Real.sqrt (β x - s)))
          (β x - S.ε₀) := by fun_prop
      have ht := hc.tendsto.mono_left
        (show 𝓝[>] (β x - S.ε₀) ≤ 𝓝 (β x - S.ε₀) from inf_le_left)
      convert ht using 1
      rw [sub_sub_cancel, S.sqrt_ε₀]
    change Tendsto (S.O.germ.branchMap ∘ fun s : ℝ =>
      (x, Real.sqrt (β x - s))) (𝓝[>] (β x - S.ε₀))
        (𝓝 (S.O.germ.branchMap (x, S.τ₀)))
    exact hbranch.tendsto.comp hinner

end ExoticCCR
