/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFSaturatedSheet
import ExoticCCR.TheoremFBranchDensity
import ExoticCCR.TheoremFMaximalSheetDensity
import ExoticCCR.TheoremEDeficiency
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite-interval integration by parts on a forward sheet

This module records the one-dimensional analytic identity needed on each
characteristic of a `ForwardSaturatedSheet`.  Both finite endpoint residuals
are displayed explicitly.  In particular, the lower residual is not discarded:
the currently inhabited sheet has a regular lower face.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped EReal Interval Topology

namespace ExoticCCR

namespace ForwardSaturatedSheet

/-- The `-i` deficiency density in flow time.  Its exponential is normalized
to equal the transverse cutoff at the upper wall time. -/
def deficiencyDensity (S : ForwardSaturatedSheet) (χ : ℝ × ℝ → ℂ)
    (p : (ℝ × ℝ) × ℝ) : ℂ :=
  χ p.1 * Complex.exp (p.2 - S.β p.1)

/-- Along every flow-time line, the deficiency density solves `dρ/ds = ρ`. -/
theorem hasDerivAt_deficiencyDensity_s (S : ForwardSaturatedSheet)
    (χ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => S.deficiencyDensity χ (x, t))
      (S.deficiencyDensity χ (x, s)) s := by
  unfold deficiencyDensity
  have hinner : HasDerivAt (fun t : ℝ => ((t - S.β x : ℝ) : ℂ)) 1 s := by
    simpa using ((hasDerivAt_id s).sub_const (S.β x)).ofReal_comp
  simpa using (Complex.hasDerivAt_exp _).comp s hinner |>.const_mul (χ x)

/-- Derivative of a test function restricted to a sheet characteristic. -/
theorem hasDerivAt_test_comp_Psi_s (S : ForwardSaturatedSheet)
    (φ : CcinftyR3) {x : ℝ × ℝ} {s : ℝ} (hs : (x, s) ∈ S.D) :
    HasDerivAt (fun t : ℝ => φ (S.Psi (x, t)))
      (fderiv ℝ (φ : R3 → ℂ) (S.Psi (x, s)) (X1 (S.Psi (x, s)))) s := by
  exact (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt s (S.hasDerivAt_Psi_s x s hs)

/-- Product-rule identity for the density--test-function pairing along a sheet
characteristic. -/
theorem hasDerivAt_density_pairing_s (S : ForwardSaturatedSheet)
    (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) {x : ℝ × ℝ} {s : ℝ}
    (hs : (x, s) ∈ S.D) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (S.deficiencyDensity χ (x, t)) (φ (S.Psi (x, t))))
      (inner ℂ (S.deficiencyDensity χ (x, s))
        (φ (S.Psi (x, s)) +
          fderiv ℝ (φ : R3 → ℂ) (S.Psi (x, s)) (X1 (S.Psi (x, s))))) s := by
  simpa only [inner_add_right, add_comm] using
    (S.hasDerivAt_deficiencyDensity_s χ x s).inner ℂ
      (S.hasDerivAt_test_comp_Psi_s φ hs)

/-- Finite-interval FTC for the sheet pairing.  The right side is the upper
trace minus the lower trace, with neither endpoint suppressed. -/
theorem integral_density_pairing_deriv_eq_endpoint_residuals
    (S : ForwardSaturatedSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    (x : ℝ × ℝ) (a b : ℝ)
    (hab : ∀ s ∈ uIcc a b, (x, s) ∈ S.D)
    (hint : IntervalIntegrable (fun s : ℝ =>
      inner ℂ (S.deficiencyDensity χ (x, s))
        (φ (S.Psi (x, s)) +
          fderiv ℝ (φ : R3 → ℂ) (S.Psi (x, s)) (X1 (S.Psi (x, s))))) volume a b) :
    ∫ s in a..b, inner ℂ (S.deficiencyDensity χ (x, s))
        (φ (S.Psi (x, s)) +
          fderiv ℝ (φ : R3 → ℂ) (S.Psi (x, s)) (X1 (S.Psi (x, s)))) =
      inner ℂ (S.deficiencyDensity χ (x, b)) (φ (S.Psi (x, b))) -
        inner ℂ (S.deficiencyDensity χ (x, a)) (φ (S.Psi (x, a))) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => S.hasDerivAt_density_pairing_s χ φ (hab s hs))
    hint

/-- Integration by parts with both endpoint traces explicit.  This is the
form used when the transport derivative is moved onto the deficiency density. -/
theorem integral_density_mul_transport_eq_residuals
    (S : ForwardSaturatedSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    (x : ℝ × ℝ) (a b : ℝ)
    (hab : ∀ s ∈ uIcc a b, (x, s) ∈ S.D)
    (hφ : IntervalIntegrable (fun s : ℝ =>
      inner ℂ (S.deficiencyDensity χ (x, s)) (φ (S.Psi (x, s)))) volume a b)
    (hXφ : IntervalIntegrable (fun s : ℝ =>
      inner ℂ (S.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (S.Psi (x, s)) (X1 (S.Psi (x, s))))) volume a b) :
    ∫ s in a..b, inner ℂ (S.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (S.Psi (x, s)) (X1 (S.Psi (x, s)))) =
      inner ℂ (S.deficiencyDensity χ (x, b)) (φ (S.Psi (x, b))) -
        inner ℂ (S.deficiencyDensity χ (x, a)) (φ (S.Psi (x, a))) -
      ∫ s in a..b, inner ℂ (S.deficiencyDensity χ (x, s)) (φ (S.Psi (x, s))) := by
  have hftc := S.integral_density_pairing_deriv_eq_endpoint_residuals χ φ x a b hab
    (by simpa only [inner_add_right] using hφ.add hXφ)
  simp_rw [inner_add_right] at hftc
  rw [intervalIntegral.integral_add] at hftc
  · apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hftc
  · exact hφ
  · exact hXφ

end ForwardSaturatedSheet

namespace ForwardMaximalSheet

/-- The ambient pairing of the maximal-sheet representative with a compactly
supported smooth test function is integrable. -/
theorem integrable_inner_uMinus_test (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) (φ : CcinftyR3) :
    Integrable (fun q : R3 => inner ℂ (M.uMinus χ q) (φ q)) volume :=
  M.integrable_inner_uMinus χ hχ hχc hχW (testFunctionMemLp φ)

/-- The ambient pairing with the minimal `X1` transport expression is
integrable by the same `L² × L² → L¹` estimate. -/
theorem integrable_inner_uMinus_minimalTransportExpression
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) (φ : CcinftyR3) :
    Integrable (fun q : R3 =>
      inner ℂ (M.uMinus χ q) (minimalTransportExpression X1 φ q)) volume :=
  M.integrable_inner_uMinus χ hχ hχc hχW
    (transportExpressionMemLp X1 contDiff_X1.continuous φ)

/-- Change of variables for the exact ambient test-function pairing used in
the representative weak identity. -/
theorem integral_inner_uMinus_test_eq_half_smul_integral_D
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) :
    (∫ q : R3, inner ℂ (M.uMinus χ q) (φ q) ∂volume) =
      (1 / 2 : ℝ) • ∫ p in M.D,
        inner ℂ (M.deficiencyDensity χ p) (φ (M.Psi p)) ∂volume :=
  M.integral_inner_uMinus_eq_half_smul_integral_D χ (φ : R3 → ℂ)

/-- Change of variables for the exact ambient minimal-transport pairing used
in the representative weak identity. -/
theorem integral_inner_uMinus_minimalTransportExpression_eq_half_smul_integral_D
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) :
    (∫ q : R3,
      inner ℂ (M.uMinus χ q) (minimalTransportExpression X1 φ q) ∂volume) =
      (1 / 2 : ℝ) • ∫ p in M.D,
        inner ℂ (M.deficiencyDensity χ p)
          (minimalTransportExpression X1 φ (M.Psi p)) ∂volume :=
  M.integral_inner_uMinus_eq_half_smul_integral_D χ
    (minimalTransportExpression X1 φ)

/-- The maximal-sheet density solves `dρ/ds = ρ` on every fiber. -/
theorem hasDerivAt_deficiencyDensity_s (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => M.deficiencyDensity χ (x, t))
      (M.deficiencyDensity χ (x, s)) s := by
  unfold deficiencyDensity
  have hinner : HasDerivAt
      (fun t : ℝ => ((t - M.S.O.germ.β x : ℝ) : ℂ)) 1 s := by
    simpa using ((hasDerivAt_id s).sub_const (M.S.O.germ.β x)).ofReal_comp
  simpa using (Complex.hasDerivAt_exp _).comp s hinner |>.const_mul (χ x)

/-- Derivative of a test function restricted to a maximal-sheet characteristic. -/
theorem hasDerivAt_test_comp_Psi_s (M : ForwardMaximalSheet)
    (φ : CcinftyR3) {x : ℝ × ℝ} {s : ℝ} (hs : (x, s) ∈ M.D) :
    HasDerivAt (fun t : ℝ => φ (M.Psi (x, t)))
      (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s)))) s := by
  exact (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt s
      (M.hasDerivAt_Psi_s ((mem_integralCurveDomain_iff _ _).1 hs.2))

/-- Product rule for the maximal-sheet density--test pairing. -/
theorem hasDerivAt_density_pairing_s (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) {x : ℝ × ℝ} {s : ℝ}
    (hs : (x, s) ∈ M.D) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (M.deficiencyDensity χ (x, t)) (φ (M.Psi (x, t))))
      (inner ℂ (M.deficiencyDensity χ (x, s))
        (φ (M.Psi (x, s)) +
          fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s))))) s := by
  simpa only [inner_add_right, add_comm] using
    (M.hasDerivAt_deficiencyDensity_s χ x s).inner ℂ
      (M.hasDerivAt_test_comp_Psi_s φ hs)

/-- Finite-interval integration by parts on a maximal characteristic, with
both endpoint residuals retained explicitly. -/
theorem integral_density_mul_transport_eq_residuals
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    (x : ℝ × ℝ) (a b : ℝ)
    (hab : ∀ s ∈ uIcc a b, (x, s) ∈ M.D)
    (hφ : IntervalIntegrable (fun s : ℝ =>
      inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s)))) volume a b)
    (hXφ : IntervalIntegrable (fun s : ℝ =>
      inner ℂ (M.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s))))) volume a b) :
    ∫ s in a..b, inner ℂ (M.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s)))) =
      inner ℂ (M.deficiencyDensity χ (x, b)) (φ (M.Psi (x, b))) -
        inner ℂ (M.deficiencyDensity χ (x, a)) (φ (M.Psi (x, a))) -
      ∫ s in a..b, inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))) := by
  have hftc :
      ∫ s in a..b, inner ℂ (M.deficiencyDensity χ (x, s))
          (φ (M.Psi (x, s)) +
            fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s)))) =
        inner ℂ (M.deficiencyDensity χ (x, b)) (φ (M.Psi (x, b))) -
          inner ℂ (M.deficiencyDensity χ (x, a)) (φ (M.Psi (x, a))) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => M.hasDerivAt_density_pairing_s χ φ (hab s hs))
      (by simpa only [inner_add_right] using hφ.add hXφ)
  simp_rw [inner_add_right] at hftc
  rw [intervalIntegral.integral_add] at hftc
  · apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hftc
  · exact hφ
  · exact hXφ

/-- Transverse integration of the finite-fiber FTC identity.  The product
integrand is continuous on the compact box, hence integrable; the proof uses
Fubini to identify its integral with the iterated fiber integral before
applying the one-dimensional identity on every transverse characteristic. -/
theorem integral_compactBox_density_pairing_deriv_eq_endpoint_residuals
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (φ : CcinftyR3) (a b : ℝ) (hab : a ≤ b)
    (hbox : tsupport χ ×ˢ Icc a b ⊆ M.D) :
    ∫ p in tsupport χ ×ˢ Icc a b,
        inner ℂ (M.deficiencyDensity χ p)
          (φ (M.Psi p) + fderiv ℝ (φ : R3 → ℂ) (M.Psi p) (X1 (M.Psi p))) =
      ∫ x in tsupport χ,
        (inner ℂ (M.deficiencyDensity χ (x, b)) (φ (M.Psi (x, b))) -
          inner ℂ (M.deficiencyDensity χ (x, a)) (φ (M.Psi (x, a)))) := by
  let G : ((ℝ × ℝ) × ℝ) → ℂ := fun p =>
    inner ℂ (M.deficiencyDensity χ p)
      (φ (M.Psi p) + fderiv ℝ (φ : R3 → ℂ) (M.Psi p) (X1 (M.Psi p)))
  have hGcont : ContinuousOn G (tsupport χ ×ˢ Icc a b) := by
    intro p hp
    have hβ : ContinuousAt M.S.O.germ.β p.1 := by
      have hs0 := M.continuousAt_s0 (hbox hp).1
      have heq : M.S.O.germ.β = fun x => M.s0 x + M.S.ε₀ := by
        funext x
        simp [ForwardMaximalSheet.s0]
      rw [heq]
      exact hs0.add continuousAt_const
    have hdens : ContinuousWithinAt (M.deficiencyDensity χ)
        (tsupport χ ×ˢ Icc a b) p := by
      unfold deficiencyDensity
      exact ((hχ.continuousAt.comp continuousAt_fst).mul
        (Complex.continuous_exp.continuousAt.comp
          ((Complex.continuous_ofReal.continuousAt.comp continuousAt_snd).sub
            (Complex.continuous_ofReal.continuousAt.comp
              (hβ.comp_of_eq continuousAt_fst rfl))))).continuousWithinAt
    have hPsi : ContinuousWithinAt M.Psi (tsupport χ ×ˢ Icc a b) p :=
      (M.continuousOn_Psi p (hbox hp)).mono hbox
    have hφPsi : ContinuousWithinAt (fun q => φ (M.Psi q))
        (tsupport χ ×ˢ Icc a b) p :=
      φ.contDiff.continuous.continuousAt.continuousWithinAt.comp hPsi
        (fun _ _ => mem_univ _)
    have htransport : Continuous (fun q : R3 =>
        fderiv ℝ (φ : R3 → ℂ) q (X1 q)) :=
      (φ.contDiff.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk contDiff_X1.continuous)
    exact hdens.inner (hφPsi.add
      (htransport.continuousAt.continuousWithinAt.comp hPsi
        (fun _ _ => mem_univ _)))
  have hGint : IntegrableOn G (tsupport χ ×ˢ Icc a b) volume :=
    hGcont.integrableOn_compact (hχc.isCompact.prod isCompact_Icc)
  rw [show (volume : Measure ((ℝ × ℝ) × ℝ)) =
      (volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ) by
        exact Measure.volume_eq_prod (ℝ × ℝ) ℝ]
  rw [MeasureTheory.setIntegral_prod G hGint]
  apply setIntegral_congr_fun hχc.isCompact.measurableSet
  intro x hx
  change (∫ s in Icc a b, G (x, s)) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    simpa [G] using M.hasDerivAt_density_pairing_s χ φ
      (hbox ⟨hx, by simpa [uIcc_of_le hab] using hs⟩)
  · apply ContinuousOn.intervalIntegrable
    exact hGcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hx, by simpa [uIcc_of_le hab] using hs⟩)

/-- On every fiber over `W`, the norm of `Psi` tends to infinity as `s` approaches
the upper wall time `β(x)` from below.  This is a translation of `escape_upper_branch`
from branch-time to anchor-`s` time. -/
theorem tendsto_norm_Psi_atTop_nhdsWithin_Iio_beta (M : ForwardMaximalSheet)
    {x : ℝ × ℝ} (hx : x ∈ M.W) :
    Tendsto (fun s : ℝ => ‖M.Psi (x, s)‖) (𝓝[<] M.S.O.germ.β x) atTop := by
  have hβ : M.S.O.germ.β x = M.s0 x + M.S.ε₀ := by simp [ForwardMaximalSheet.s0]
  have hesc := M.escape_upper_branch x hx
  -- Eventually s > s0 x as s → β(x)⁻ (since s0 x < β x)
  have hs0_lt_β : M.s0 x < M.S.O.germ.β x := by
    rw [hβ]
    linarith [M.S.ε₀_pos]
  -- On the Ioo (s0 x) (β x) overlap, Psi agrees with branchTimeCurve
  have hevEq : ∀ᶠ s in 𝓝[<] M.S.O.germ.β x, s > M.s0 x →
      ‖M.Psi (x, s)‖ = ‖M.S.branchTimeCurve x (s - M.s0 x)‖ := by
    filter_upwards [self_mem_nhdsWithin] with s hs hgt
    rw [M.Psi_eq_branchTimeCurve hx ⟨hgt, hs⟩]
  have hevGt : ∀ᶠ s in 𝓝[<] M.S.O.germ.β x, s > M.s0 x := by
    have hmem : Ioo (M.s0 x) (M.S.O.germ.β x) ∈ 𝓝[<] M.S.O.germ.β x :=
      Ioo_mem_nhdsLT hs0_lt_β
    filter_upwards [hmem] with s hs
    exact hs.1
  -- The composed function: ‖branchTimeCurve x (s - s0 x)‖ → ∞
  -- We prove this using the characterization of atTop
  rw [Filter.tendsto_atTop]
  intro B
  -- From hesc, ∀ᶠ t in 𝓝[<] ε₀, B ≤ ‖branchTimeCurve x t‖
  rw [Filter.tendsto_atTop] at hesc
  have hB := hesc B
  -- Pull back hB through (s ↦ s - s0 x) : 𝓝[<] (s0 x + ε₀) → 𝓝[<] ε₀
  have hpre : ∀ᶠ s in 𝓝[<] M.S.O.germ.β x, B ≤ ‖M.S.branchTimeCurve x (s - M.s0 x)‖ := by
    rw [hβ]
    -- Get the set from hB
    rw [Filter.Eventually, mem_nhdsWithin_iff_exists_mem_nhds_inter] at hB ⊢
    obtain ⟨U, hU, hUB⟩ := hB
    refine ⟨(fun s => s - M.s0 x) ⁻¹' U, ?_, ?_⟩
    · apply (continuous_sub_right (M.s0 x)).continuousAt.preimage_mem_nhds
      simp only [add_sub_cancel_left]
      exact hU
    · intro s hs
      simp only [mem_inter_iff, mem_preimage, mem_Iio] at hs
      apply hUB
      refine ⟨hs.1, ?_⟩
      simp only [mem_Iio]
      linarith [hs.2]
  filter_upwards [hpre, hevEq, hevGt] with s hpre' heq hgt
  rw [heq hgt]
  exact hpre'

/-- A compactly supported test function is eventually zero along any fiber whose
norm tends to infinity. -/
theorem eventually_eq_zero_of_tendsto_norm_atTop (φ : CcinftyR3) {f : ℝ → R3}
    {l : Filter ℝ} (hf : Tendsto (fun s => ‖f s‖) l atTop) :
    ∀ᶠ s in l, φ (f s) = 0 := by
  -- The tsupport of φ is compact, hence bounded
  have hK : IsCompact (tsupport (φ : R3 → ℂ)) := φ.hasCompactSupport
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hsupp : ∀ q : R3, R < ‖q‖ → φ q = 0 := by
    intro q hq
    by_contra hmem
    have hmem' : q ∈ Function.support (φ : R3 → ℂ) := Function.mem_support.mpr hmem
    have hq_in : q ∈ tsupport (φ : R3 → ℂ) := subset_tsupport _ hmem'
    have h := hR q hq_in
    linarith
  have hev : ∀ᶠ s in l, R < ‖f s‖ := hf (Ioi_mem_atTop R)
  filter_upwards [hev] with s hs
  exact hsupp (f s) hs

/-- **Upper wall residual vanishing (pointwise).**  For a compactly supported test
function φ and a compactly supported transverse cutoff χ, the upper endpoint pairing
`inner (χ x) (φ (M.Psi (x, s)))` tends pointwise to zero as `s → β(x)⁻`.

This is the key estimate that makes the upper residual vanish in integration by parts
on forward maximal sheets: the sheet escapes all compact sets at the upper wall,
so any compactly supported test function eventually evaluates to zero there. -/
theorem tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Iio_beta
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    {x : ℝ × ℝ} (hx : x ∈ M.W) :
    Tendsto (fun s : ℝ => inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))))
      (𝓝[<] M.S.O.germ.β x) (𝓝 0) := by
  have hnorm := M.tendsto_norm_Psi_atTop_nhdsWithin_Iio_beta hx
  have hφzero := eventually_eq_zero_of_tendsto_norm_atTop φ hnorm
  apply tendsto_const_nhds.congr'
  filter_upwards [hφzero] with s hs
  simp [hs]

/-- Variant of upper wall residual vanishing for the raw test function (without
the deficiency density prefactor).  This is useful when the density cancellation
is handled separately. -/
theorem tendsto_test_comp_Psi_zero_nhdsWithin_Iio_beta
    (M : ForwardMaximalSheet) (φ : CcinftyR3)
    {x : ℝ × ℝ} (hx : x ∈ M.W) :
    Tendsto (fun s : ℝ => φ (M.Psi (x, s))) (𝓝[<] M.S.O.germ.β x) (𝓝 0) := by
  have hnorm := M.tendsto_norm_Psi_atTop_nhdsWithin_Iio_beta hx
  have hφzero := eventually_eq_zero_of_tendsto_norm_atTop φ hnorm
  apply tendsto_const_nhds.congr'
  filter_upwards [hφzero] with s hs
  exact hs.symm

/-- The upper residual term in integration by parts can be made arbitrarily small
by taking the upper integration limit sufficiently close to β(x).  This is the
ε-δ form of upper wall residual vanishing. -/
theorem forall_pos_exists_near_beta_norm_inner_lt
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    {x : ℝ × ℝ} (hx : x ∈ M.W) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : ℝ, M.S.O.germ.β x - δ < s → s < M.S.O.germ.β x →
      ‖inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s)))‖ < ε := by
  have htends := M.tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Iio_beta χ φ hx
  rw [Metric.tendsto_nhdsWithin_nhds] at htends
  obtain ⟨δ, hδ, hball⟩ := htends ε hε
  refine ⟨δ, hδ, fun s hs1 hs2 => ?_⟩
  have hdist : dist s (M.S.O.germ.β x) < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr hs2)]
    linarith
  have hres := hball hs2 hdist
  simp only [dist_zero_right] at hres
  exact hres

/-!
## Lower residual vanishing

The lower endpoint has two honest alternatives per `lower_eq_bot_or_exists_escape`:

1. **`tMin = ⊥`** (lower endpoint is `-∞`): The density factor `exp(s - β(x)) → 0`
   as `s → -∞`, while the test function remains bounded (compact support on a
   continuous function).  The pairing vanishes.

2. **Finite `tMin` with norm escape**: As `s` approaches the finite lower endpoint
   from the right, `‖Psi‖ → ∞`, so any compactly supported test function eventually
   evaluates to zero.  The pairing vanishes.
-/

/-- When the lower endpoint is `-∞`, the density factor `exp(s - β(x))` tends to 0
as `s → -∞`. -/
theorem tendsto_exp_sub_beta_atBot (M : ForwardMaximalSheet) (x : ℝ × ℝ) :
    Tendsto (fun s : ℝ => Complex.exp (s - M.S.O.germ.β x)) atBot (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => (s - M.S.O.germ.β x : ℂ)) atBot (comap Complex.re atBot) := by
    rw [tendsto_comap_iff]
    simp only [Function.comp_def, Complex.sub_re, Complex.ofReal_re]
    exact tendsto_atBot_add_const_right _ _ tendsto_id
  exact Complex.tendsto_exp_comap_re_atBot.comp h

/-- **Lower residual vanishing (case: lower endpoint is `-∞`).**  When `tMin = ⊥`,
the deficiency density `χ(x) * exp(s - β(x))` tends to 0 as `s → -∞`, and hence
the pairing with any bounded test function vanishes.  This covers the first
honest alternative for lower residual treatment. -/
theorem tendsto_inner_deficiencyDensity_test_zero_atBot
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) (x : ℝ × ℝ) :
    Tendsto (fun s : ℝ => inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))))
      atBot (𝓝 0) := by
  -- The density is χ(x) * exp(s - β(x)); as s → -∞, exp(s - β) → 0
  -- The test function φ(Psi(x, s)) is bounded (continuous, compactly supported)
  have hexp := M.tendsto_exp_sub_beta_atBot x
  -- χ(x) is a constant wrt s
  have hdens : Tendsto (fun s : ℝ => M.deficiencyDensity χ (x, s)) atBot (𝓝 0) := by
    unfold deficiencyDensity
    simpa using hexp.const_mul (χ x)
  -- φ is bounded: continuous function with compact support
  have hbdd : ∃ C : ℝ, ∀ q : R3, ‖(φ : R3 → ℂ) q‖ ≤ C := by
    have hK := φ.hasCompactSupport
    have hcont := φ.contDiff.continuous
    -- The image of the compact support is bounded
    have himg := hK.image hcont
    obtain ⟨R, hR⟩ := himg.isBounded.exists_norm_le
    -- Outside tsupport, φ = 0, so norm ≤ max(R, 0) = R (since R ≥ 0 from norm bound)
    refine ⟨max R 0, fun q => ?_⟩
    by_cases hmem : q ∈ tsupport (φ : R3 → ℂ)
    · exact (hR _ (Set.mem_image_of_mem (φ : R3 → ℂ) hmem)).trans (le_max_left R 0)
    · have hzero : (φ : R3 → ℂ) q = 0 := by
        by_contra h
        exact hmem (subset_tsupport (φ : R3 → ℂ) (Function.mem_support.mpr h))
      simp only [hzero, norm_zero]
      exact le_max_right R 0
  obtain ⟨C, hbnd⟩ := hbdd
  have hpair : ∀ s : ℝ, ‖inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s)))‖ ≤
      ‖M.deficiencyDensity χ (x, s)‖ * C := fun s =>
    calc ‖inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s)))‖
        ≤ ‖M.deficiencyDensity χ (x, s)‖ * ‖φ (M.Psi (x, s))‖ := norm_inner_le_norm _ _
      _ ≤ ‖M.deficiencyDensity χ (x, s)‖ * C :=
          mul_le_mul_of_nonneg_left (hbnd _) (norm_nonneg _)
  have htends : Tendsto (fun s => ‖M.deficiencyDensity χ (x, s)‖ * C) atBot (𝓝 0) := by
    have h0 : (0 : ℝ) = ‖(0 : ℂ)‖ * C := by simp
    rw [h0]
    exact hdens.norm.mul_const C
  exact squeeze_zero_norm hpair htends

/-- On every fiber over `W`, the norm of `Psi` tends to infinity as `s` approaches
a finite lower endpoint from the right.  This mirrors `tendsto_norm_Psi_atTop_nhdsWithin_Iio_beta`
for the upper wall. -/
theorem tendsto_norm_Psi_atTop_nhdsWithin_Ioi_finite_lower (M : ForwardMaximalSheet)
    {x : ℝ × ℝ} (_hx : x ∈ M.W) {T : ℝ} (hT : tMin (M.S.qSigma x) = (T : EReal)) :
    Tendsto (fun s : ℝ => ‖M.Psi (x, s)‖) (𝓝[>] (M.s0 x + T)) atTop := by
  -- The finite-endpoint escape lemma gives norm escape at the maximal-curve level
  have hesc := tendsto_norm_maximalIntegralCurve_at_tMin hT
  -- Psi(x, s) = maximalIntegralCurve (qSigma x) (s - s0 x)
  -- As s → (s0 x + T)⁺, we have (s - s0 x) → T⁺
  rw [Filter.tendsto_atTop] at hesc ⊢
  intro B
  obtain ⟨U, hU, hUB⟩ := Filter.eventually_iff_exists_mem.mp (hesc B)
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨(fun s => s - M.s0 x) ⁻¹' V ∩ Ioi (M.s0 x + T), ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨(fun s => s - M.s0 x) ⁻¹' V, ?_, rfl.subset⟩
    apply (continuous_sub_right (M.s0 x)).continuousAt.preimage_mem_nhds
    simp only [add_sub_cancel_left]
    exact hV
  · intro s hs
    simp only [mem_inter_iff, mem_preimage, mem_Ioi] at hs
    have hs' : s - M.s0 x ∈ V ∩ Ioi T := by
      refine ⟨hs.1, ?_⟩
      simp only [mem_Ioi]
      linarith [hs.2]
    have hmem : s - M.s0 x ∈ U := hVU hs'
    have hB := hUB (s - M.s0 x) hmem
    simp only [Psi]
    exact hB

/-- **Lower residual vanishing (case: finite lower with norm escape).**  When the
lower endpoint is finite and the norm escapes to infinity, the compactly supported
test function eventually vanishes, and hence the pairing vanishes.  This covers
the second honest alternative for lower residual treatment. -/
theorem tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Ioi_finite_lower
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    {x : ℝ × ℝ} (hx : x ∈ M.W) {T : ℝ} (hT : tMin (M.S.qSigma x) = (T : EReal)) :
    Tendsto (fun s : ℝ => inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))))
      (𝓝[>] (M.s0 x + T)) (𝓝 0) := by
  have hnorm := M.tendsto_norm_Psi_atTop_nhdsWithin_Ioi_finite_lower hx hT
  have hφzero := eventually_eq_zero_of_tendsto_norm_atTop φ hnorm
  apply tendsto_const_nhds.congr'
  filter_upwards [hφzero] with s hs
  simp [hs]

/-- Variant of lower residual vanishing (finite case) for the raw test function. -/
theorem tendsto_test_comp_Psi_zero_nhdsWithin_Ioi_finite_lower
    (M : ForwardMaximalSheet) (φ : CcinftyR3)
    {x : ℝ × ℝ} (hx : x ∈ M.W) {T : ℝ} (hT : tMin (M.S.qSigma x) = (T : EReal)) :
    Tendsto (fun s : ℝ => φ (M.Psi (x, s))) (𝓝[>] (M.s0 x + T)) (𝓝 0) := by
  have hnorm := M.tendsto_norm_Psi_atTop_nhdsWithin_Ioi_finite_lower hx hT
  have hφzero := eventually_eq_zero_of_tendsto_norm_atTop φ hnorm
  apply tendsto_const_nhds.congr'
  filter_upwards [hφzero] with s hs
  exact hs.symm

/-- **Pointwise lower residual vanishing (combined).**  For both honest lower
alternatives, the density--test pairing vanishes at the lower endpoint:

- If `tMin = ⊥`, the exponential factor in the density goes to zero as `s → -∞`.
- If `tMin` is finite with norm escape, the test function vanishes.

This is the key estimate ensuring the lower residual can be taken to zero in
integration by parts on forward maximal sheets. -/
theorem lower_residual_vanishing_alternatives (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) {x : ℝ × ℝ} (hx : x ∈ M.W) :
    (tMin (M.S.qSigma x) = ⊥ ∧
      Tendsto (fun s : ℝ => inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))))
        atBot (𝓝 0)) ∨
    (∃ T : ℝ, tMin (M.S.qSigma x) = (T : EReal) ∧
      Tendsto (fun s : ℝ => inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))))
        (𝓝[>] (M.s0 x + T)) (𝓝 0)) := by
  rcases M.lower_eq_bot_or_exists_escape x with hbot | ⟨T, hT, _⟩
  · left
    exact ⟨hbot, M.tendsto_inner_deficiencyDensity_test_zero_atBot χ φ x⟩
  · right
    exact ⟨T, hT, M.tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Ioi_finite_lower χ φ hx hT⟩

/-!
## Fiber geometry

The following identities expose the translated maximal-curve domain as an
ordinary interval.  They are deliberately pointwise in the transverse
variable; in particular, the finite lower endpoint is not selected globally.
-/

/-- If the maximal curve has lower endpoint `-∞`, its translated fiber is the
open ray below the upper wall. -/
theorem fiber_eq_Iio_of_tMin_eq_bot (M : ForwardMaximalSheet)
    {x : ℝ × ℝ} (hx : x ∈ M.W) (hbot : tMin (M.S.qSigma x) = ⊥) :
    {s : ℝ | (x, s) ∈ M.D} = Iio (M.S.O.germ.β x) := by
  ext s
  simp only [mem_setOf_eq, D, hx, true_and, mem_Iio]
  rw [mem_integralCurveDomain_iff, hbot, M.tMax_eq x hx]
  simp only [EReal.bot_lt_coe, true_and, EReal.coe_lt_coe_iff]
  simp only [ForwardMaximalSheet.s0]
  constructor <;> intro h <;> linarith

/-- A finite lower endpoint is strictly negative, since every maximal curve
domain contains time zero as an interior point. -/
theorem tMin_lt_zero_of_eq_coe (M : ForwardMaximalSheet) (x : ℝ × ℝ)
    {T : ℝ} (hT : tMin (M.S.qSigma x) = (T : EReal)) : T < 0 := by
  obtain ⟨α, I, hα⟩ := exists_isIntegralCurveFrom (M.S.qSigma x)
  have hzero : 0 ∈ integralCurveDomain (M.S.qSigma x) := ⟨α, I, hα, hα.1⟩
  have hlo := ((mem_integralCurveDomain_iff (M.S.qSigma x) 0).1 hzero).1
  rw [hT] at hlo
  exact EReal.coe_lt_coe_iff.mp (by simpa using hlo)

/-- If the maximal curve has finite lower endpoint `T`, its translated fiber
is the open interval from `s0 + T` to the upper wall. -/
theorem fiber_eq_Ioo_of_tMin_eq_coe (M : ForwardMaximalSheet)
    {x : ℝ × ℝ} (hx : x ∈ M.W) {T : ℝ}
    (hT : tMin (M.S.qSigma x) = (T : EReal)) :
    {s : ℝ | (x, s) ∈ M.D} = Ioo (M.s0 x + T) (M.S.O.germ.β x) := by
  ext s
  simp only [mem_setOf_eq, D, hx, true_and, mem_Ioo]
  rw [mem_integralCurveDomain_iff, hT, M.tMax_eq x hx]
  simp only [EReal.coe_lt_coe_iff]
  simp only [ForwardMaximalSheet.s0]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith

/-!
## Transverse integration of upper residual vanishing

For a compactly supported transverse cutoff χ, the upper endpoint residual
`∫ x in K, inner ρ(x,b) φ(Psi(x,b))` can be shown to vanish as `b(x) → β(x)⁻`
uniformly.  The key is that:

1. **Uniform bound**: On the compact support `K = tsupport χ`, the residual
   magnitude is bounded by `‖χ x‖ · ‖φ‖∞`, which is integrable over `K`.

2. **Pointwise convergence**: For each `x ∈ K ⊆ W`, the pointwise lemma
   `tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Iio_beta` gives
   convergence to 0 as `s → β(x)⁻`.

3. **DCT application**: Dominated convergence on the compact set `K` then
   yields convergence of the integral.

We work with the approximating sequence `b_n(x) = β(x) - 1/n` which stays
uniformly below the wall while approaching it.
-/

/-- Uniform bound on the norm of a compactly supported test function. -/
theorem exists_bound_CcinftyR3 (φ : CcinftyR3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : R3, ‖(φ : R3 → ℂ) q‖ ≤ C := by
  have hK : IsCompact (tsupport (φ : R3 → ℂ)) := φ.hasCompactSupport
  have hcont : Continuous (φ : R3 → ℂ) := φ.contDiff.continuous
  obtain ⟨R, hR⟩ := (hK.image hcont.norm).isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right R 0, fun q => ?_⟩
  by_cases hmem : q ∈ tsupport (φ : R3 → ℂ)
  · have := hR ‖(φ : R3 → ℂ) q‖ (Set.mem_image_of_mem _ hmem)
    rw [Real.norm_of_nonneg (norm_nonneg _)] at this
    exact this.trans (le_max_left R 0)
  · have hzero : (φ : R3 → ℂ) q = 0 := by
      by_contra h
      exact hmem (subset_tsupport _ (Function.mem_support.mpr h))
    simp only [hzero, norm_zero]
    exact le_max_right R 0

/-- The integrand for the upper residual at a fixed offset below the wall.
This is the function `x ↦ inner ρ(x, β(x) - δ) φ(Psi(x, β(x) - δ))`. -/
def upperResidualAtOffset (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (φ : CcinftyR3) (δ : ℝ) (x : ℝ × ℝ) : ℂ :=
  inner ℂ (M.deficiencyDensity χ (x, M.S.O.germ.β x - δ))
    (φ (M.Psi (x, M.S.O.germ.β x - δ)))

/-- Uniform bound on the upper residual at any offset δ > 0: the residual magnitude
is bounded by `‖χ x‖ · C` where C bounds the test function. -/
theorem norm_upperResidualAtOffset_le (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) {C : ℝ} (hC_pos : 0 ≤ C) (hC : ∀ q, ‖(φ : R3 → ℂ) q‖ ≤ C)
    (δ : ℝ) (hδ : 0 < δ) (x : ℝ × ℝ) :
    ‖M.upperResidualAtOffset χ φ δ x‖ ≤ ‖χ x‖ * C := by
  unfold upperResidualAtOffset
  -- The deficiency density at (x, β(x) - δ) is χ(x) * exp((β(x) - δ) - β(x)) = χ(x) * exp(-δ)
  have hdens : M.deficiencyDensity χ (x, M.S.O.germ.β x - δ) =
      χ x * Complex.exp (-δ) := by
    unfold deficiencyDensity
    congr 1
    simp only [Complex.ofReal_sub]
    ring
  rw [hdens]
  calc ‖inner ℂ (χ x * Complex.exp (-δ)) (φ (M.Psi (x, M.S.O.germ.β x - δ)))‖
      ≤ ‖χ x * Complex.exp (-δ)‖ * ‖φ (M.Psi (x, M.S.O.germ.β x - δ))‖ := norm_inner_le_norm _ _
    _ ≤ ‖χ x * Complex.exp (-δ)‖ * C := by
        apply mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = ‖χ x‖ * ‖Complex.exp (-δ)‖ * C := by rw [norm_mul]
    _ = ‖χ x‖ * Real.exp (-δ) * C := by
        rw [Complex.norm_exp]
        simp only [Complex.neg_re, Complex.ofReal_re]
    _ ≤ ‖χ x‖ * 1 * C := by
        apply mul_le_mul_of_nonneg_right _ hC_pos
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hδ.le)
    _ = ‖χ x‖ * C := by ring

/-- Pointwise upper residual convergence: for each x in the transverse support,
the upper residual at offset 1/(n+1) tends to 0 as n → ∞. This follows from
the escape lemma and the fact that β(x) - 1/(n+1) → β(x)⁻. -/
theorem tendsto_upperResidualAtOffset_zero_of_mem_W (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3) {x : ℝ × ℝ} (hx : x ∈ M.W) :
    Tendsto (fun n : ℕ => M.upperResidualAtOffset χ φ (1 / (n + 1 : ℝ)) x) atTop (𝓝 0) := by
  have htends := M.tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Iio_beta χ φ hx
  -- The sequence β(x) - 1/(n+1) → β(x)⁻
  have h1n : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      have h : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      exact h.atTop_add tendsto_const_nhds
    simpa [one_div] using this
  have hseq : Tendsto (fun n : ℕ => M.S.O.germ.β x - 1 / (n + 1 : ℝ)) atTop
      (𝓝[<] M.S.O.germ.β x) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using tendsto_const_nhds.sub h1n
    · filter_upwards with n
      simp only [mem_Iio, sub_lt_self_iff]
      positivity
  unfold upperResidualAtOffset
  exact htends.comp hseq

/-!
## DCT integration of upper residual vanishing

The transverse integral of the upper residual converges to 0 via Dominated
Convergence.  The dominating function is `‖χ x‖ * C` which is integrable
on the compact transverse support of `χ`.
-/

/-- The dominating function `x ↦ ‖χ x‖ * C` is integrable on the compact
transverse support of a compactly supported cutoff. -/
theorem integrable_norm_mul_const_on_tsupport (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (C : ℝ) :
    IntegrableOn (fun x : ℝ × ℝ => ‖χ x‖ * C) (tsupport χ) volume :=
  (hχ.norm.continuousOn.integrableOn_compact hχc).mul_const C

/-!
## Fixed-fiber improper integration by parts
-/

/-- An abstract exhaustion form of fixed-fiber integration by parts.  Both
endpoint residuals are retained at every finite stage and are required to
converge to zero. -/
theorem integral_fiber_density_mul_transport_eq_neg_of_exhaustion
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    (x : ℝ × ℝ) (fiber : Set ℝ) (a b : ℕ → ℝ)
    (hmono : Monotone (fun n => Icc (a n) (b n)))
    (hunion : (⋃ n, Icc (a n) (b n)) = fiber)
    (hab : ∀ n, a n ≤ b n)
    (hmem : ∀ n s, s ∈ Icc (a n) (b n) → (x, s) ∈ M.D)
    (hpair : IntegrableOn (fun s : ℝ =>
      inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s)))) fiber volume)
    (htransport : IntegrableOn (fun s : ℝ =>
      inner ℂ (M.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s))))) fiber volume)
    (ha0 : Tendsto (fun n =>
      inner ℂ (M.deficiencyDensity χ (x, a n)) (φ (M.Psi (x, a n)))) atTop (𝓝 0))
    (hb0 : Tendsto (fun n =>
      inner ℂ (M.deficiencyDensity χ (x, b n)) (φ (M.Psi (x, b n)))) atTop (𝓝 0)) :
    (∫ s in fiber, inner ℂ (M.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s)))) ∂volume) =
      -(∫ s in fiber,
        inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))) ∂volume) := by
  let A : ℝ → ℂ := fun s =>
    inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s)))
  let B : ℝ → ℂ := fun s =>
    inner ℂ (M.deficiencyDensity χ (x, s))
      (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s))))
  have hAI : Tendsto (fun n => ∫ s in Icc (a n) (b n), A s ∂volume) atTop
      (𝓝 (∫ s in fiber, A s ∂volume)) := by
    rw [← hunion]
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) hmono
      (by simpa [A, hunion] using hpair)
  have hBI : Tendsto (fun n => ∫ s in Icc (a n) (b n), B s ∂volume) atTop
      (𝓝 (∫ s in fiber, B s ∂volume)) := by
    rw [← hunion]
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) hmono
      (by simpa [B, hunion] using htransport)
  have hfinite : ∀ n,
      (∫ s in Icc (a n) (b n), B s ∂volume) =
        inner ℂ (M.deficiencyDensity χ (x, b n)) (φ (M.Psi (x, b n))) -
          inner ℂ (M.deficiencyDensity χ (x, a n)) (φ (M.Psi (x, a n))) -
            ∫ s in Icc (a n) (b n), A s ∂volume := by
    intro n
    have hsub : Icc (a n) (b n) ⊆ fiber := by
      rw [← hunion]
      exact Set.subset_iUnion (fun k : ℕ => Icc (a k) (b k)) n
    have hAint : IntervalIntegrable A volume (a n) (b n) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (hab n)).2
        (by simpa [A] using hpair.mono_set hsub)
    have hBint : IntervalIntegrable B volume (a n) (b n) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (hab n)).2
        (by simpa [B] using htransport.mono_set hsub)
    have h := M.integral_density_mul_transport_eq_residuals χ φ x (a n) (b n)
      (fun s hs => hmem n s (by simpa [uIcc_of_le (hab n)] using hs))
      (by simpa [A] using hAint) (by simpa [B] using hBint)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab n),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab n)]
    exact h
  have hrhs : Tendsto (fun n =>
      inner ℂ (M.deficiencyDensity χ (x, b n)) (φ (M.Psi (x, b n))) -
        inner ℂ (M.deficiencyDensity χ (x, a n)) (φ (M.Psi (x, a n))) -
          ∫ s in Icc (a n) (b n), A s ∂volume) atTop
      (𝓝 (-(∫ s in fiber, A s ∂volume))) := by
    convert (hb0.sub ha0).sub hAI using 1 <;> simp
  have hBI' := hrhs.congr' (Filter.Eventually.of_forall fun n => (hfinite n).symm)
  simpa [A, B] using tendsto_nhds_unique hBI hBI'

/-- Closed intervals whose lower endpoints tend to `-∞` and whose upper
endpoints tend to a finite wall from below exhaust the corresponding open ray. -/
theorem iUnion_Icc_eq_Iio_of_tendsto
    {a b : ℕ → ℝ} {u : ℝ} (ha : Tendsto a atTop atBot)
    (hb : Tendsto b atTop (𝓝 u)) (hbu : ∀ n, b n < u) :
    (⋃ n, Icc (a n) (b n)) = Iio u := by
  ext s
  constructor
  · intro hs
    rw [Set.mem_iUnion] at hs
    obtain ⟨n, hn⟩ := hs
    exact hn.2.trans_lt (hbu n)
  · intro hs
    have hea : ∀ᶠ n in atTop, a n ≤ s := ha (Iic_mem_atBot s)
    have heb : ∀ᶠ n in atTop, s ≤ b n := hb (Ici_mem_nhds hs)
    have hev : ∀ᶠ n in atTop, a n ≤ s ∧ s ≤ b n := hea.and heb
    obtain ⟨n, hn⟩ := Filter.Eventually.exists hev
    exact Set.mem_iUnion.2 ⟨n, hn⟩

/-- Closed intervals whose endpoints approach two finite walls from the
interior exhaust the corresponding open interval. -/
theorem iUnion_Icc_eq_Ioo_of_tendsto
    {a b : ℕ → ℝ} {l u : ℝ} (ha : Tendsto a atTop (𝓝 l))
    (hb : Tendsto b atTop (𝓝 u)) (hla : ∀ n, l < a n)
    (hbu : ∀ n, b n < u) :
    (⋃ n, Icc (a n) (b n)) = Ioo l u := by
  ext s
  constructor
  · intro hs
    rw [Set.mem_iUnion] at hs
    obtain ⟨n, hn⟩ := hs
    exact ⟨(hla n).trans_le hn.1, hn.2.trans_lt (hbu n)⟩
  · intro hs
    have hea : ∀ᶠ n in atTop, a n ≤ s := ha (Iic_mem_nhds hs.1)
    have heb : ∀ᶠ n in atTop, s ≤ b n := hb (Ici_mem_nhds hs.2)
    have hev : ∀ᶠ n in atTop, a n ≤ s ∧ s ≤ b n := hea.and heb
    obtain ⟨n, hn⟩ := Filter.Eventually.exists hev
    exact Set.mem_iUnion.2 ⟨n, hn⟩

/-- Improper integration by parts on one fixed maximal-sheet fiber.  The lower
endpoint alternative is chosen only after fixing `x`; no measurable selection
of finite lower endpoints is used. -/
theorem integral_fiber_density_mul_transport_eq_neg
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ) (φ : CcinftyR3)
    (x : ℝ × ℝ) (hx : x ∈ M.W)
    (hpair : IntegrableOn (fun s : ℝ =>
      inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))))
      {s | (x, s) ∈ M.D} volume)
    (htransport : IntegrableOn (fun s : ℝ =>
      inner ℂ (M.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s)))))
      {s | (x, s) ∈ M.D} volume) :
    (∫ s in {s | (x, s) ∈ M.D}, inner ℂ (M.deficiencyDensity χ (x, s))
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi (x, s)) (X1 (M.Psi (x, s)))) ∂volume) =
      -(∫ s in {s | (x, s) ∈ M.D},
        inner ℂ (M.deficiencyDensity χ (x, s)) (φ (M.Psi (x, s))) ∂volume) := by
  let b : ℕ → ℝ := fun n =>
    M.S.O.germ.β x - M.S.ε₀ / ((n : ℝ) + 2)
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hoff : Tendsto (fun n : ℕ => M.S.ε₀ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hb : Tendsto b atTop (𝓝 (M.S.O.germ.β x)) := by
    simpa [b] using tendsto_const_nhds.sub hoff
  have hbu : ∀ n, b n < M.S.O.germ.β x := by
    intro n
    simp only [b, sub_lt_self_iff]
    exact div_pos M.S.ε₀_pos (by positivity)
  have hbwithin : Tendsto b atTop (𝓝[<] M.S.O.germ.β x) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within b hb
      (Filter.Eventually.of_forall hbu)
  have hb0 : Tendsto (fun n =>
      inner ℂ (M.deficiencyDensity χ (x, b n)) (φ (M.Psi (x, b n))))
      atTop (𝓝 0) :=
    (M.tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Iio_beta χ φ hx).comp hbwithin
  have hbmono : Monotone b := by
    intro m n hmn
    apply sub_le_sub_left
    apply mul_le_mul_of_nonneg_left _ M.S.ε₀_pos.le
    simpa [one_div, div_eq_mul_inv] using
      one_div_le_one_div_of_le (show 0 < (m : ℝ) + 2 by positivity)
        (by exact_mod_cast (Nat.add_le_add_right hmn 2))
  have hb_s0 : ∀ n, M.s0 x < b n := by
    intro n
    simp only [b, ForwardMaximalSheet.s0]
    have hfrac : M.S.ε₀ / ((n : ℝ) + 2) ≤ M.S.ε₀ / 2 := by
      apply mul_le_mul_of_nonneg_left _ M.S.ε₀_pos.le
      simpa [one_div, div_eq_mul_inv] using
        one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num)
          (show (2 : ℝ) ≤ (n : ℝ) + 2 by norm_cast; omega)
    linarith [M.S.ε₀_pos]
  rcases M.lower_eq_bot_or_exists_escape x with hbot | ⟨T, hT, _⟩
  · let a : ℕ → ℝ := fun n => M.s0 x - n
    have ha : Tendsto a atTop atBot := by
      have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
      simpa [a, sub_eq_add_neg, add_comm] using
        tendsto_atBot_add_const_right atTop (M.s0 x) hneg
    have hamono : Antitone a := by
      intro m n hmn
      dsimp [a]
      exact sub_le_sub_left (by exact_mod_cast hmn) _
    have hmono : Monotone (fun n => Icc (a n) (b n)) := by
      intro m n hmn s hs
      exact ⟨(hamono hmn).trans hs.1, hs.2.trans (hbmono hmn)⟩
    have hunion : (⋃ n, Icc (a n) (b n)) = {s | (x, s) ∈ M.D} := by
      rw [M.fiber_eq_Iio_of_tMin_eq_bot hx hbot]
      exact iUnion_Icc_eq_Iio_of_tendsto ha hb hbu
    have hab : ∀ n, a n ≤ b n := by
      intro n
      exact (show a n ≤ M.s0 x by simp [a]).trans (hb_s0 n).le
    have hmem : ∀ n s, s ∈ Icc (a n) (b n) → (x, s) ∈ M.D := by
      intro n s hs
      show s ∈ {t : ℝ | (x, t) ∈ M.D}
      rw [M.fiber_eq_Iio_of_tMin_eq_bot hx hbot]
      exact hs.2.trans_lt (hbu n)
    have ha0 : Tendsto (fun n =>
        inner ℂ (M.deficiencyDensity χ (x, a n)) (φ (M.Psi (x, a n))))
        atTop (𝓝 0) :=
      (M.tendsto_inner_deficiencyDensity_test_zero_atBot χ φ x).comp ha
    exact M.integral_fiber_density_mul_transport_eq_neg_of_exhaustion χ φ x
      {s | (x, s) ∈ M.D} a b hmono hunion hab hmem hpair htransport ha0 hb0
  · have hTneg : T < 0 := M.tMin_lt_zero_of_eq_coe x hT
    let l : ℝ := M.s0 x + T
    let a : ℕ → ℝ := fun n => l + (-T) / ((n : ℝ) + 2)
    have ha : Tendsto a atTop (𝓝 l) := by
      have htend : Tendsto (fun n : ℕ => (-T) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => -T) atTop (𝓝 (-T)) := tendsto_const_nhds
        simpa [div_eq_mul_inv] using hc.mul hinv
      simpa [a] using tendsto_const_nhds.add htend
    have hla : ∀ n, l < a n := by
      intro n
      simp only [a, lt_add_iff_pos_right]
      exact div_pos (neg_pos.mpr hTneg) (by positivity)
    have hamono : Antitone a := by
      intro m n hmn
      dsimp [a]
      have hrecip : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
        one_div_le_one_div_of_le (show 0 < (m : ℝ) + 2 by positivity)
          (by exact_mod_cast (Nat.add_le_add_right hmn 2))
      have hfrac := mul_le_mul_of_nonneg_left hrecip (neg_nonneg.mpr hTneg.le)
      calc
        l + (-T) / ((n : ℝ) + 2) = (-T) * (1 / ((n : ℝ) + 2)) + l := by ring
        _ ≤ (-T) * (1 / ((m : ℝ) + 2)) + l := add_le_add_left hfrac l
        _ = l + (-T) / ((m : ℝ) + 2) := by ring
    have ha_s0 : ∀ n, a n < M.s0 x := by
      intro n
      have hfrac : (-T) / ((n : ℝ) + 2) ≤ (-T) / 2 := by
        apply mul_le_mul_of_nonneg_left _ (neg_nonneg.mpr hTneg.le)
        simpa [one_div, div_eq_mul_inv] using
          one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num)
            (show (2 : ℝ) ≤ (n : ℝ) + 2 by norm_cast; omega)
      dsimp [a, l]
      linarith
    have hmono : Monotone (fun n => Icc (a n) (b n)) := by
      intro m n hmn s hs
      exact ⟨(hamono hmn).trans hs.1, hs.2.trans (hbmono hmn)⟩
    have hunion : (⋃ n, Icc (a n) (b n)) = {s | (x, s) ∈ M.D} := by
      rw [M.fiber_eq_Ioo_of_tMin_eq_coe hx hT]
      exact iUnion_Icc_eq_Ioo_of_tendsto ha hb hla hbu
    have hab : ∀ n, a n ≤ b n := by
      intro n
      exact (ha_s0 n).le.trans (hb_s0 n).le
    have hmem : ∀ n s, s ∈ Icc (a n) (b n) → (x, s) ∈ M.D := by
      intro n s hs
      show s ∈ {t : ℝ | (x, t) ∈ M.D}
      rw [M.fiber_eq_Ioo_of_tMin_eq_coe hx hT]
      exact ⟨(show M.s0 x + T = l by rfl) ▸ (hla n).trans_le hs.1,
        hs.2.trans_lt (hbu n)⟩
    have hawithin : Tendsto a atTop (𝓝[>] l) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a ha
        (Filter.Eventually.of_forall hla)
    have ha0 : Tendsto (fun n =>
        inner ℂ (M.deficiencyDensity χ (x, a n)) (φ (M.Psi (x, a n))))
        atTop (𝓝 0) := by
      have hlower : l = M.s0 x + T := rfl
      rw [hlower] at hawithin
      exact (M.tendsto_inner_deficiencyDensity_test_zero_nhdsWithin_Ioi_finite_lower
        χ φ hx hT).comp hawithin
    exact M.integral_fiber_density_mul_transport_eq_neg_of_exhaustion χ φ x
      {s | (x, s) ∈ M.D} a b hmono hunion hab hmem hpair htransport ha0 hb0

/-!
## Full-domain Fubini
-/

/-- The unscaled directional derivative appearing after fiberwise integration
by parts is an ambient `L²` function. -/
theorem memLp_test_fderiv_X1 (φ : CcinftyR3) :
    MemLp (fun q : R3 => fderiv ℝ (φ : R3 → ℂ) q (X1 q)) 2 volume := by
  have hcont : Continuous (fun q : R3 => fderiv ℝ (φ : R3 → ℂ) q (X1 q)) :=
    (φ.contDiff.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk contDiff_X1.continuous)
  have hsupp : HasCompactSupport
      (fun q : R3 => fderiv ℝ (φ : R3 → ℂ) q (X1 q)) := by
    apply (φ.hasCompactSupport.fderiv ℝ).mono'
    intro q hq
    apply subset_tsupport
    change fderiv ℝ (φ : R3 → ℂ) q ≠ 0
    intro hz
    apply hq
    simp [hz]
  exact hcont.memLp_of_hasCompactSupport hsupp

/-- The density--test pairing is integrable on the full variable parameter
domain, obtained by reversing the nonzero-Jacobian Bochner change of variables. -/
theorem integrableOn_D_density_test (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) (φ : CcinftyR3) :
    IntegrableOn (fun p : (ℝ × ℝ) × ℝ =>
      inner ℂ (M.deficiencyDensity χ p) (φ (M.Psi p))) M.D volume :=
  M.integrableOn_inner_deficiencyDensity_comp_Psi χ hχ hχc hχW
    (testFunctionMemLp φ)

/-- The density--directional-derivative pairing is integrable on the full
variable parameter domain. -/
theorem integrableOn_D_density_transport (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) (φ : CcinftyR3) :
    IntegrableOn (fun p : (ℝ × ℝ) × ℝ =>
      inner ℂ (M.deficiencyDensity χ p)
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi p) (X1 (M.Psi p)))) M.D volume :=
  M.integrableOn_inner_deficiencyDensity_comp_Psi χ hχ hχc hχW
    (memLp_test_fderiv_X1 φ)

/-- Full-domain integration by parts.  Fubini supplies section integrability
almost everywhere, and the lower endpoint alternative is resolved only inside
the already-fixed fiber theorem. -/
theorem integral_D_density_mul_transport_eq_neg
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) (φ : CcinftyR3) :
    (∫ p in M.D, inner ℂ (M.deficiencyDensity χ p)
        (fderiv ℝ (φ : R3 → ℂ) (M.Psi p) (X1 (M.Psi p))) ∂volume) =
      -(∫ p in M.D,
        inner ℂ (M.deficiencyDensity χ p) (φ (M.Psi p)) ∂volume) := by
  let A : ((ℝ × ℝ) × ℝ) → ℂ := fun p =>
    inner ℂ (M.deficiencyDensity χ p) (φ (M.Psi p))
  let B : ((ℝ × ℝ) × ℝ) → ℂ := fun p =>
    inner ℂ (M.deficiencyDensity χ p)
      (fderiv ℝ (φ : R3 → ℂ) (M.Psi p) (X1 (M.Psi p)))
  let AI := M.D.indicator A
  let BI := M.D.indicator B
  have hDm : MeasurableSet M.D := M.isOpen_D.measurableSet
  have hAI : Integrable AI volume := by
    rw [integrable_indicator_iff hDm]
    simpa [A, AI] using M.integrableOn_D_density_test χ hχ hχc hχW φ
  have hBI : Integrable BI volume := by
    rw [integrable_indicator_iff hDm]
    simpa [B, BI] using M.integrableOn_D_density_transport χ hχ hχc hχW φ
  have hvol : (volume : Measure ((ℝ × ℝ) × ℝ)) =
      (volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ) :=
    Measure.volume_eq_prod (ℝ × ℝ) ℝ
  rw [hvol] at hAI hBI
  have hsection : ∀ᵐ x : ℝ × ℝ,
      (∫ s : ℝ, BI (x, s) ∂volume) = -(∫ s : ℝ, AI (x, s) ∂volume) := by
    filter_upwards [hAI.prod_right_ae, hBI.prod_right_ae] with x hAx hBx
    by_cases hx : x ∈ M.W
    · have hfiber : MeasurableSet {s : ℝ | (x, s) ∈ M.D} :=
        M.isOpen_D.preimage (continuous_const.prodMk continuous_id) |>.measurableSet
      have hAind : Integrable ({s : ℝ | (x, s) ∈ M.D}.indicator
          (fun s => A (x, s))) volume := by
        apply hAx.congr
        filter_upwards with s
        simp only [AI, Set.indicator, A]
        rfl
      have hBind : Integrable ({s : ℝ | (x, s) ∈ M.D}.indicator
          (fun s => B (x, s))) volume := by
        apply hBx.congr
        filter_upwards with s
        simp only [BI, Set.indicator, B]
        rfl
      have hAon : IntegrableOn (fun s => A (x, s)) {s | (x, s) ∈ M.D} volume :=
        (integrable_indicator_iff hfiber).1 hAind
      have hBon : IntegrableOn (fun s => B (x, s)) {s | (x, s) ∈ M.D} volume :=
        (integrable_indicator_iff hfiber).1 hBind
      rw [show (∫ s, BI (x, s) ∂volume) = ∫ s in {s | (x, s) ∈ M.D}, B (x, s) ∂volume by
          rw [← integral_indicator hfiber]
          apply integral_congr_ae
          filter_upwards with s
          simp only [BI, Set.indicator, B]
          rfl]
      rw [show (∫ s, AI (x, s) ∂volume) = ∫ s in {s | (x, s) ∈ M.D}, A (x, s) ∂volume by
          rw [← integral_indicator hfiber]
          apply integral_congr_ae
          filter_upwards with s
          simp only [AI, Set.indicator, A]
          rfl]
      simpa [A, B] using
        M.integral_fiber_density_mul_transport_eq_neg χ φ x hx
          (by simpa [A] using hAon) (by simpa [B] using hBon)
    · have hempty : {s : ℝ | (x, s) ∈ M.D} = ∅ := by
        ext s
        simp [ForwardMaximalSheet.D, hx]
      simp [AI, BI, A, B, ForwardMaximalSheet.D, hx]
  rw [← integral_indicator hDm, ← integral_indicator hDm]
  change (∫ p, BI p ∂volume) = -(∫ p, AI p ∂volume)
  rw [hvol, integral_prod BI hBI, integral_prod AI hAI]
  calc
    (∫ x : ℝ × ℝ, ∫ s : ℝ, BI (x, s) ∂volume ∂volume) =
        ∫ x : ℝ × ℝ, -(∫ s : ℝ, AI (x, s) ∂volume) ∂volume :=
      integral_congr_ae hsection
    _ = -(∫ x : ℝ × ℝ, ∫ s : ℝ, AI (x, s) ∂volume ∂volume) := integral_neg _

end ForwardMaximalSheet

/-!
## Forward weak deficiency witness and Theorem E
-/

/-- The representative weak `-i` identity for the maximal-sheet zero
extension. -/
theorem representative_integral_identity (M : ForwardMaximalSheet)
    (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) (φ : CcinftyR3) :
    inner ℂ ((-Complex.I) • (M.memLp_uMinus χ hχ hχc hχW).toLp (M.uMinus χ))
        (testFunctionToL2 φ) =
      ∫ q : R3, inner ℂ (M.uMinus χ q)
        (minimalTransportExpression X1 φ q) ∂volume := by
  have hmin :
      (∫ p in M.D, inner ℂ (M.deficiencyDensity χ p)
        (minimalTransportExpression X1 φ (M.Psi p)) ∂volume) =
        (-Complex.I) • ∫ p in M.D, inner ℂ (M.deficiencyDensity χ p)
          (fderiv ℝ (φ : R3 → ℂ) (M.Psi p) (X1 (M.Psi p))) ∂volume := by
    rw [← integral_smul]
    apply setIntegral_congr_fun M.isOpen_D.measurableSet
    intro p _
    change inner ℂ (M.deficiencyDensity χ p)
      ((-Complex.I) • fderiv ℝ (φ : R3 → ℂ) (M.Psi p) (X1 (M.Psi p))) = _
    rw [inner_smul_right]
    rfl
  rw [inner_smul_left]
  simp only [map_neg, Complex.conj_I, neg_neg]
  rw [inner_toLp_testFunctionToL2_eq_integral (M.memLp_uMinus χ hχ hχc hχW) φ]
  rw [M.integral_inner_uMinus_test_eq_half_smul_integral_D χ φ]
  rw [M.integral_inner_uMinus_minimalTransportExpression_eq_half_smul_integral_D χ φ]
  rw [hmin, M.integral_D_density_mul_transport_eq_neg χ hχ hχc hχW φ]
  simp [smul_eq_mul]
  ring

/-- A nonzero maximal-sheet zero extension is a weak `-i` eigenvector for the
canonical minimal transport core of `X1`. -/
theorem X1_forwardWeakDeficiency : X1ForwardWeakDeficiencyStatement := by
  obtain ⟨O⟩ := exists_forwardBranchOpen
  obtain ⟨M⟩ := O.exists_forwardMaximalSheet
  obtain ⟨χ, hχ, hχc, hχW, hu_ne⟩ := M.exists_nonzero_L2_uMinus
  let u := (M.memLp_uMinus χ hχ hχc hχW).toLp (M.uMinus χ)
  refine ⟨u, hu_ne, ?_⟩
  apply weakAdjoint_negI_of_representative_integrals
    (M.memLp_uMinus χ hχ hχc hχW)
  intro φ
  exact representative_integral_identity M χ hχ hχc hχW φ

/-- **A001 Theorem E.** The canonical minimal transport core for `X1` is not
essentially self-adjoint. -/
theorem theoremE : ¬ H_X1_min.IsEssentiallySelfAdjoint :=
  theoremE_of_forwardWeakDeficiency X1_forwardWeakDeficiency

end ExoticCCR
