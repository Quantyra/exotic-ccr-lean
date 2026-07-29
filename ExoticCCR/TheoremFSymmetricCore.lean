/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFConditionalClassification
import ExoticCCR.TheoremFJacobianFDeriv
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

set_option maxHeartbeats 1600000 in
-- The second-order polynomial derivative expansion of the adjugate row is
-- normalization-heavy, exactly as in `hasDerivAt_gamma`.
open Matrix MvPolynomial in
/-- The polynomial divergence certificate for the first dual row: the formal
divergence of `dualMatrixF ℝ` along its second row vanishes identically. -/
theorem sum_pderiv_dualMatrixF_row_one :
    (∑ i : Fin 3, pderiv i (dualMatrixF ℝ 1 i)) = 0 := by
  simp only [Fin.sum_univ_three]
  simp only [dualMatrixF, Matrix.smul_apply, Matrix.transpose_apply,
    Matrix.adjugate_fin_three, jacobianMatrix, of_apply, F, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, smul_eq_mul, map_add, map_sub, map_neg,
    map_zero, Derivation.map_natCast, Derivation.map_one_eq_zero, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  simp only [map_ofNat]
  ring

open MvPolynomial in
/-- The polynomial divergence certificate for `X1` agrees with its analytic
coordinate divergence. -/
theorem analyticDivergence_X1_eq_zero (q : R3) : analyticDivergence X1 q = 0 := by
  have hdiff : ∀ k : Fin 3, DifferentiableAt ℝ (fun x : R3 => X1 x k) q := fun k =>
    (hasFDerivAt_eval_mvPolynomial (dualMatrixF ℝ 1 k) q).differentiableAt
  have hcoord : ∀ i : Fin 3, fderiv ℝ X1 q (Pi.single i 1) i =
      eval q (pderiv i (dualMatrixF ℝ 1 i)) := by
    intro i
    have hpi : fderiv ℝ X1 q = ContinuousLinearMap.pi
        fun k => fderiv ℝ (fun x : R3 => X1 x k) q := fderiv_pi hdiff
    rw [hpi, ContinuousLinearMap.pi_apply]
    have heval : fderiv ℝ (fun x : R3 => X1 x i) q = evalPDeriv (dualMatrixF ℝ 1 i) q :=
      (hasFDerivAt_eval_mvPolynomial (dualMatrixF ℝ 1 i) q).fderiv
    rw [heval]
    simp [evalPDeriv, Pi.single_apply]
  rw [analyticDivergence]
  calc
    (∑ i, fderiv ℝ X1 q (Pi.single i 1) i)
        = ∑ i : Fin 3, eval q (pderiv i (dualMatrixF ℝ 1 i)) :=
      Finset.sum_congr rfl fun i _ => hcoord i
    _ = eval q (∑ i : Fin 3, pderiv i (dualMatrixF ℝ 1 i)) := by rw [map_sum]
    _ = 0 := by rw [sum_pderiv_dualMatrixF_row_one, map_zero]

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
  have hxRange : (x : L2R3) ∈ LinearMap.range testFunctionToL2 := by
    rw [← minimalTransportCore_domain X hX]
    exact x.property
  have hyRange : (y : L2R3) ∈ LinearMap.range testFunctionToL2 := by
    rw [← minimalTransportCore_domain X hX]
    exact y.property
  rcases hxRange with ⟨φ, hφ⟩
  rcases hyRange with ⟨ψ, hψ⟩
  have hx : x = ⟨testFunctionToL2 φ, by
      rw [minimalTransportCore_domain X hX]
      exact LinearMap.mem_range_self testFunctionToL2 φ⟩ :=
    Subtype.ext hφ.symm
  have hy : y = ⟨testFunctionToL2 ψ, by
      rw [minimalTransportCore_domain X hX]
      exact LinearMap.mem_range_self testFunctionToL2 ψ⟩ :=
    Subtype.ext hψ.symm
  rw [hx, hy, minimalTransportCore_apply, minimalTransportCore_apply]
  exact hPair φ ψ

/-! ### Compactly-supported coordinate integration by parts -/

/-- The coefficient used to move the `i`th coordinate derivative from one
test function to the other. -/
def transportCoefficient (X : R3 → R3) (φ : CcinftyR3) (i : Fin 3) (q : R3) : ℂ :=
  star (φ q) * (X q i)

theorem contDiff_transportCoefficient (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (φ : CcinftyR3) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (transportCoefficient X φ i) := by
  have hstar : ContDiff ℝ (⊤ : ℕ∞) fun q : R3 => star (φ q) :=
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.comp φ.contDiff
  have hXiC : ContDiff ℝ (⊤ : ℕ∞) fun q : R3 => ((X q i : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_pi.mp hX i).of_le le_top)
  exact hstar.mul hXiC

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
  have hcont : Continuous fun q : R3 =>
      fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) :=
    (contDiff_transportCoefficient X hX φ i).continuous_fderiv_apply (by simp)
      |>.comp (continuous_id.prodMk continuous_const)
  apply (hcont.mul ψ.continuous).integrable_of_hasCompactSupport
  exact ((hasCompactSupport_transportCoefficient X φ i).fderiv_apply ℝ _).mul_right

theorem integrable_transportCoefficient_mul_fderiv (X : R3 → R3)
    (hX : ContDiff ℝ ⊤ X) (φ ψ : CcinftyR3) (i : Fin 3) :
    Integrable
      (fun q : R3 => transportCoefficient X φ i q *
        fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1))
      (volume : Measure R3) := by
  have hcont : Continuous fun q : R3 => fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1) :=
    ψ.contDiff.continuous_fderiv_apply (by simp)
      |>.comp (continuous_id.prodMk continuous_const)
  apply ((contDiff_transportCoefficient X hX φ i).continuous.mul hcont)
    |>.integrable_of_hasCompactSupport
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
    exact ((contDiff_transportCoefficient X hX φ i).differentiable (by simp)).differentiableAt
  · intro q _
    exact (ψ.contDiff.differentiable (by simp)).differentiableAt

/-- Product-rule expansion of the transported coefficient in one coordinate. -/
theorem fderiv_transportCoefficient_apply (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (φ : CcinftyR3) (i : Fin 3) (q : R3) :
    fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) =
      star (fderiv ℝ (φ : R3 → ℂ) q (Pi.single i 1)) * (X q i) +
        star (φ q) * fderiv ℝ X q (Pi.single i 1) i := by
  have hφD : Differentiable ℝ (φ : R3 → ℂ) := φ.contDiff.differentiable (by simp)
  have hstarD : Differentiable ℝ fun p : R3 => star (φ p) := hφD.star
  have hXiD : Differentiable ℝ fun p : R3 => X p i :=
    (contDiff_pi.mp hX i).differentiable (by simp)
  have hXiCD : Differentiable ℝ fun p : R3 => ((X p i : ℝ) : ℂ) :=
    Complex.ofRealCLM.differentiable.comp hXiD
  have hmul : fderiv ℝ
      ((fun p : R3 => star (φ p)) * fun p : R3 => ((X p i : ℝ) : ℂ)) q =
      star (φ q) • fderiv ℝ (fun p : R3 => ((X p i : ℝ) : ℂ)) q +
        ((X q i : ℝ) : ℂ) • fderiv ℝ (fun p : R3 => star (φ p)) q :=
    fderiv_mul hstarD.differentiableAt hXiCD.differentiableAt
  have hcoeff : fderiv ℝ (transportCoefficient X φ i) q =
      star (φ q) • fderiv ℝ (fun p : R3 => ((X p i : ℝ) : ℂ)) q +
        ((X q i : ℝ) : ℂ) • fderiv ℝ (fun p : R3 => star (φ p)) q := hmul
  have hstar_eval : fderiv ℝ (fun p : R3 => star (φ p)) q (Pi.single i 1) =
      star (fderiv ℝ (φ : R3 → ℂ) q (Pi.single i 1)) := by
    rw [fderiv_star]
    rfl
  have hXiC_eval : fderiv ℝ (fun p : R3 => ((X p i : ℝ) : ℂ)) q (Pi.single i 1) =
      ((fderiv ℝ X q (Pi.single i 1) i : ℝ) : ℂ) := by
    have h1 : fderiv ℝ (fun p : R3 => ((X p i : ℝ) : ℂ)) q =
        Complex.ofRealCLM.comp (fderiv ℝ (fun p : R3 => X p i) q) :=
      (Complex.ofRealCLM.hasFDerivAt.comp q hXiD.differentiableAt.hasFDerivAt).fderiv
    have h2 : fderiv ℝ X q (Pi.single i 1) i =
        fderiv ℝ (fun p : R3 => X p i) q (Pi.single i 1) := by
      rw [fderiv_pi fun k =>
        ((contDiff_pi.mp hX k).differentiable (by simp)).differentiableAt]
      rfl
    rw [h1, h2]
    rfl
  rw [hcoeff, add_apply, smul_apply, smul_apply, hstar_eval, hXiC_eval,
    smul_eq_mul, smul_eq_mul]
  ring

private theorem pi_expand_in_coordinate_basis (v : R3) :
    (∑ i : Fin 3, v i • Pi.single i (1 : ℝ)) = v := by
  funext j
  rw [Finset.sum_apply]
  simp [Pi.single_apply]

/-- Expanding a directional derivative into the three standard coordinates. -/
theorem transport_derivative_expand (X : R3 → R3) (φ ψ : CcinftyR3) (q : R3) :
    star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X q) =
      ∑ i : Fin 3, star (φ q) * (X q i) *
        fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1) := by
  have hD : fderiv ℝ (ψ : R3 → ℂ) q (X q) =
      ∑ i : Fin 3, ((X q i : ℝ) : ℂ) * fderiv ℝ (ψ : R3 → ℂ) q (Pi.single i 1) := by
    conv_lhs => rw [← pi_expand_in_coordinate_basis (X q)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Complex.real_smul]
  rw [hD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The sum of coefficient derivatives is the transported derivative plus the
analytic divergence contribution. -/
theorem sum_fderiv_transportCoefficient (X : R3 → R3) (hX : ContDiff ℝ ⊤ X)
    (φ : CcinftyR3) (q : R3) :
    ∑ i : Fin 3,
      fderiv ℝ (transportCoefficient X φ i) q (Pi.single i 1) =
      star (fderiv ℝ (φ : R3 → ℂ) q (X q)) + star (φ q) * analyticDivergence X q := by
  have hstar : star (fderiv ℝ (φ : R3 → ℂ) q (X q)) =
      ∑ i : Fin 3, star (fderiv ℝ (φ : R3 → ℂ) q (Pi.single i 1)) * (X q i) := by
    conv_lhs => rw [← pi_expand_in_coordinate_basis (X q)]
    rw [map_sum, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, star_smul, star_trivial, Complex.real_smul]
    ring
  have hdiv : star (φ q) * (analyticDivergence X q : ℂ) =
      ∑ i : Fin 3, star (φ q) * ((fderiv ℝ X q (Pi.single i 1) i : ℝ) : ℂ) := by
    rw [analyticDivergence]
    push_cast
    rw [Finset.mul_sum]
  rw [hstar, hdiv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_transportCoefficient_apply X hX φ]

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
              rw [show minimalTransportExpression X1 φ q =
                -Complex.I * fderiv ℝ (φ : R3 → ℂ) q (X1 q) from rfl]
              rw [RCLike.inner_apply', RCLike.star_def, map_mul, map_neg, Complex.conj_I]
              ring
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
              rw [show minimalTransportExpression X1 ψ q =
                -Complex.I * fderiv ℝ (ψ : R3 → ℂ) q (X1 q) from rfl]
              rw [RCLike.inner_apply', RCLike.star_def]
              ring
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
