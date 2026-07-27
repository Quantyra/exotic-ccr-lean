/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFSaturatedSheet
import ExoticCCR.TheoremFBranchDensity
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

open MeasureTheory Set
open scoped Interval

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

end ExoticCCR
