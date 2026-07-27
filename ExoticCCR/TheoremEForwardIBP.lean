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

/-- The `-i` deficiency density in maximal-sheet flow time. -/
def deficiencyDensity (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (p : (ℝ × ℝ) × ℝ) : ℂ :=
  χ p.1 * Complex.exp (p.2 - M.S.O.germ.β p.1)

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

-- NOTE: Residual vanishing lemmas are blocked on detailed mathlib filter/measure API work.
-- The mathematical content is: upper residual vanishes by wall escape + compact support,
-- lower residual vanishes by either exponential decay (ℓ=⊥) or finite escape (same logic).
-- These are deferred to a future iteration.

end ForwardMaximalSheet

end ExoticCCR
