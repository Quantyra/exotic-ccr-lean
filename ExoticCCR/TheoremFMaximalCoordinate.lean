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

open MvPolynomial Set

namespace ExoticCCR

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

end ExoticCCR
