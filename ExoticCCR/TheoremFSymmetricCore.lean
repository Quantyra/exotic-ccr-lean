/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFConditionalClassification
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Compact-support symmetry bridge for the Theorem F minimal core

This module isolates the analytic bridge required to prove that the canonical
compactly supported transport core of `H_X1_min = -i X1` is formally symmetric.
It contains no extension-classification assertion.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped LinearPMap ENNReal ComplexConjugate

namespace ExoticCCR

/-- The analytic divergence of a real vector field in the standard `Fin 3`
coordinates. -/
def analyticDivergence (X : R3 → R3) (q : R3) : ℝ :=
  ∑ i, fderiv ℝ X q (Pi.single i 1) i

/-- The polynomial divergence certificate for `X1` agrees with its analytic
coordinate divergence. -/
theorem analyticDivergence_X1_eq_zero (q : R3) : analyticDivergence X1 q = 0 := by
  simp [analyticDivergence, X1, dualVectorField, dualMatrixF,
    Matrix.adjugate_fin_three, jacobianMatrix, F]

/--
The operator-theoretic endpoint of a compact-support integration-by-parts
argument.  The input is a test-function pairing identity, while the conclusion
is the exact `LinearPMap.IsFormalAdjoint` statement consumed by the unbounded
operator layer.

This lemma does not assert the analytic identity: the latter must be obtained
from a divergence theorem for the concrete vector field.
-/
theorem minimalTransportCore_isFormalAdjoint_of_testFunctionPairing
    (X : R3 → R3) (hX : Continuous X)
    (hPair : ∀ φ ψ : CcinftyR3,
      inner ℂ (transportAction X hX φ) (testFunctionToL2 ψ) =
        inner ℂ (testFunctionToL2 φ) (transportAction X hX ψ)) :
    (minimalTransportCore X hX).IsFormalAdjoint (minimalTransportCore X hX) := by
  intro x y
  rw [minimalTransportCore_domain] at x y
  rcases x with ⟨φ, rfl⟩
  rcases y with ⟨ψ, rfl⟩
  rw [minimalTransportCore_apply, minimalTransportCore_apply]
  exact hPair φ ψ

/-! ### Compactly-supported coordinate integration by parts -/

/-- The coefficient used to move the `i`th coordinate derivative from one
test function to the other. -/
def transportCoefficient (X : R3 → R3) (φ : CcinftyR3) (i : Fin 3) (q : R3) : ℂ :=
  star (φ q) * (X q i)

theorem contDiff_transportCoefficient (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (φ : CcinftyR3) (i : Fin 3) :
    ContDiff ℝ ⊤ (transportCoefficient X φ i) := by
  exact (φ.contDiff.star.mul (hX.apply i))

theorem hasCompactSupport_transportCoefficient (X : R3 → R3)
    (φ : CcinftyR3) (i : Fin 3) :
    HasCompactSupport (transportCoefficient X φ i) := by
  apply φ.hasCompactSupport.mono'
  intro q hq
  apply subset_tsupport
  change star (φ q) * (X q i) ≠ 0 at hq
  intro hφ
  apply hq
  simp [hφ]

theorem integrable_transportCoefficient (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (φ : CcinftyR3) (i : Fin 3) :
    Integrable (transportCoefficient X φ i) (volume : Measure R3) :=
  (contDiff_transportCoefficient X hX φ i).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_transportCoefficient X φ i)

theorem integrable_fderiv_transportCoefficient_mul (X : R3 → R3)
    (hX : ContDiff ℝ ⊤ X) (φ ψ : CcinftyR3) (i : Fin 3) :
    Integrable
      (fun q : R3 => fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) * ψ q)
      (volume : Measure R3) := by
  apply (contDiff_transportCoefficient X hX φ i).continuous_fderiv_apply
    (by simp) |>.mul ψ.continuous |>.integrable_of_hasCompactSupport
  exact (hasCompactSupport_transportCoefficient X φ i).fderiv_apply _ |>.mul_right

theorem integrable_transportCoefficient_mul_fderiv (X : R3 → R3)
    (hX : ContDiff ℝ ⊤ X) (φ ψ : CcinftyR3) (i : Fin 3) :
    Integrable
      (fun q : R3 => transportCoefficient X φ i q *
        fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1))
      (volume : Measure R3) := by
  apply ((contDiff_transportCoefficient X hX φ i).continuous.mul
    (ψ.contDiff.continuous_fderiv_apply (by simp))) |>.integrable_of_hasCompactSupport
  exact (hasCompactSupport_transportCoefficient X φ i).mul_right

theorem integrable_transportCoefficient_mul (X : R3 → R3)
    (hX : ContDiff ℝ ⊤ X) (φ ψ : CcinftyR3) (i : Fin 3) :
    Integrable (fun q : R3 => transportCoefficient X φ i q * ψ q)
      (volume : Measure R3) := by
  apply ((contDiff_transportCoefficient X hX φ i).continuous.mul ψ.continuous)
    |>.integrable_of_hasCompactSupport
  exact (hasCompactSupport_transportCoefficient X φ i).mul_right

/-- Coordinatewise compact-support integration by parts for the variable
coefficient `conj φ · X_i`. -/
theorem integral_transportCoefficient_fderiv_eq_neg
    (X : R3 → R3) (hX : ContDiff ℝ ⊤ X) (φ ψ : CcinftyR3) (i : Fin 3) :
    (∫ q : R3, transportCoefficient X φ i q *
      fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1) ∂volume) =
      -(∫ q : R3, fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) * ψ q ∂volume) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_fderiv_transportCoefficient_mul X hX φ ψ i
  · exact integrable_transportCoefficient_mul_fderiv X hX φ ψ i
  · exact integrable_transportCoefficient_mul X hX φ ψ i
  · intro q _
    exact (contDiff_transportCoefficient X hX φ i).differentiable (by simp)
  · intro q _
    exact ψ.contDiff.differentiable (by simp)

/-- Product-rule expansion of the transported coefficient in one coordinate. -/
theorem fderiv_transportCoefficient_apply (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (φ : CcinftyR3) (i : Fin 3) (q : R3) :
    fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) =
      star (fderiv ℝ (φ : R3 → ℂ) q (Pi.single i 1)) * (X q i) +
        star (φ q) * fderiv ℝ X q (Pi.single i 1) i := by
  rw [transportCoefficient, fderiv_mul]
  · simp only [fderiv_star, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_apply]
    rfl
  · exact (φ.contDiff.differentiable (by simp)).differentiableAt
  · exact (hX.apply i).differentiable (by simp) |>.differentiableAt

private theorem pi_expand_in_coordinate_basis (v : R3) :
    (∑ i : Fin 3, v i • Pi.single i (1 : ℝ)) = v := by
  ext j
  simp

/-- Expanding a directional derivative into the three standard coordinates. -/
theorem transport_derivative_expand (X : R3 → R3) (φ ψ : CcinftyR3) (q : R3) :
    star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X q) =
      ∑ i : Fin 3, star (φ q) * (X q i) *
        fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1) := by
  rw [← pi_expand_in_coordinate_basis (X q), map_sum]
  simp only [ContinuousLinearMap.map_smul, Finset.mul_sum]
  push_cast
  ring

/-- The sum of coefficient derivatives is the transported derivative plus the
analytic divergence contribution. -/
theorem sum_fderiv_transportCoefficient (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (φ : CcinftyR3) (q : R3) :
    ∑ i : Fin 3,
      fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) =
      star (fderiv ℝ (φ : R3 → ℂ) q (X q)) + star (φ q) * analyticDivergence X q := by
  simp_rw [fderiv_transportCoefficient_apply X hX φ]
  rw [show analyticDivergence X q =
    ∑ i : Fin 3, fderiv ℝ X q (Pi.single i 1) i by rfl]
  rw [← pi_expand_in_coordinate_basis (X q), map_sum]
  simp only [ContinuousLinearMap.map_smul, map_sum, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  push_cast
  ring

/-- Full compact-support integration by parts for a smooth divergence-free
real vector field.  This is the analytic identity needed for formal symmetry
of the `-i X` transport core. -/
theorem integral_transport_derivative_eq_neg_of_analyticDivergence_eq_zero
    (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (hDiv : ∀ q : R3, analyticDivergence X q = 0)
    (φ ψ : CcinftyR3) :
    (∫ q : R3, star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X q) ∂volume) =
      -(∫ q : R3, star (fderiv ℝ (φ : R3 → ℂ) q (X q)) * ψ q ∂volume) := by
  calc
    (∫ q : R3, star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X q) ∂volume) =
        ∫ q : R3, ∑ i : Fin 3, transportCoefficient X φ i q *
          fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with q
          simpa [transportCoefficient, mul_assoc] using transport_derivative_expand X φ ψ q
    _ = ∑ i : Fin 3, ∫ q : R3, transportCoefficient X φ i q *
          fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1) ∂volume := by
          rw [integral_finsetSum]
          intro i _
          exact integrable_transportCoefficient_mul_fderiv X hX φ ψ i
    _ = -(∑ i : Fin 3, ∫ q : R3,
          fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) * ψ q ∂volume) := by
          simp_rw [integral_transportCoefficient_fderiv_eq_neg X hX φ ψ]
          rw [Finset.sum_neg_distrib]
    _ = -(∫ q : R3, ∑ i : Fin 3,
          fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) * ψ q ∂volume) := by
          congr 1
          rw [integral_finsetSum]
          intro i _
          exact integrable_fderiv_transportCoefficient_mul X hX φ ψ i
    _ = -(∫ q : R3, star (fderiv ℝ (φ : R3 → ℂ) q (X q)) * ψ q ∂volume) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with q
          rw [← Finset.sum_mul]
          rw [sum_fderiv_transportCoefficient X hX φ q, hDiv q]
          simp

/-- The concrete compact-support pairing identity for the `X1` transport
expression.  It is obtained from coordinate integration by parts and the
verified analytic divergence identity. -/
theorem transportAction_X1_testFunction_pairing (φ ψ : CcinftyR3) :
    inner ℂ (transportAction X1 contDiff_X1.continuous φ) (testFunctionToL2 ψ) =
      inner ℂ (testFunctionToL2 φ) (transportAction X1 contDiff_X1.continuous ψ) := by
  rw [show transportAction X1 contDiff_X1.continuous φ =
      (transportExpressionMemLp X1 contDiff_X1.continuous φ).toLp
        (minimalTransportExpression X1 φ) from rfl,
    testFunctionToL2_apply,
    inner_toLp_toLp_eq_integral]
  rw [show transportAction X1 contDiff_X1.continuous ψ =
      (transportExpressionMemLp X1 contDiff_X1.continuous ψ).toLp
        (minimalTransportExpression X1 ψ) from rfl,
    testFunctionToL2_apply,
    inner_toLp_toLp_eq_integral]
  have hIBP := integral_transport_derivative_eq_neg_of_analyticDivergence_eq_zero
    X1 contDiff_X1 analyticDivergence_X1_eq_zero φ ψ
  have hleft :
      (∫ q : R3, inner ℂ (minimalTransportExpression X1 φ q) (ψ q) ∂volume) =
        Complex.I *
          (∫ q : R3, star (fderiv ℝ (φ : R3 → ℂ) q (X1 q)) * ψ q ∂volume) := by
    calc
      (∫ q : R3, inner ℂ (minimalTransportExpression X1 φ q) (ψ q) ∂volume) =
          ∫ q : R3, Complex.I *
            (star (fderiv ℝ (φ : R3 → ℂ) q (X1 q)) * ψ q) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with q
              simp [minimalTransportExpression, RCLike.inner_apply', mul_assoc]
      _ = _ := by rw [integral_const_mul]
  have hright :
      (∫ q : R3, inner ℂ (φ q) (minimalTransportExpression X1 ψ q) ∂volume) =
        -Complex.I *
          (∫ q : R3, star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X1 q) ∂volume) := by
    calc
      (∫ q : R3, inner ℂ (φ q) (minimalTransportExpression X1 ψ q) ∂volume) =
          ∫ q : R3, -Complex.I *
            (star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X1 q)) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with q
              simp [minimalTransportExpression, RCLike.inner_apply', mul_assoc]
      _ = _ := by rw [integral_const_mul]
  rw [hleft, hright, hIBP]
  ring

/-- The canonical `C_c^∞` realization of `H_X1_min = -i X1` is formally
symmetric.  This is the operator-theoretic symmetry prerequisite for the
unconditional von Neumann classification program. -/
theorem H_X1_min_isFormalAdjoint_H_X1_min :
    H_X1_min.IsFormalAdjoint H_X1_min :=
  minimalTransportCore_isFormalAdjoint_of_testFunctionPairing X1 contDiff_X1.continuous
    transportAction_X1_testFunction_pairing

end ExoticCCR
