/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremD
import ExoticCCR.TransportOperator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The sign involution carrying the forward branch to the backward branch

This module records the exact linear involution `σ(q₀,q₁,q₂) = (-q₀,-q₁,q₂)`
of the anchor domain.  Two finite algebraic facts are proved about it:

* `σ` preserves Lebesgue measure on `ℝ³` (its matrix is diagonal with
  determinant `1`);
* `σ` reverses the first dual field: `X1 (σ q) = -σ (X1 q)`.

The second identity is an exact polynomial computation on the adjugate
entries of the anchor Jacobian.  No operator-theoretic conclusion is drawn
here; the `L²` transport consequences live in a separate module.
-/

noncomputable section

open Matrix MeasureTheory MvPolynomial

namespace ExoticCCR

/-- The sign involution `σ(q₀,q₁,q₂) = (-q₀,-q₁,q₂)` on the anchor domain. -/
def sigmaMap (q : R3) : R3 := ![-(q 0), -(q 1), q 2]

/-- The diagonal matrix of the sign involution. -/
def sigmaMatrix : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, -1, 1]

theorem sigmaMap_apply_zero (q : R3) : sigmaMap q 0 = -(q 0) := rfl

theorem sigmaMap_apply_one (q : R3) : sigmaMap q 1 = -(q 1) := rfl

theorem sigmaMap_apply_two (q : R3) : sigmaMap q 2 = q 2 := rfl

/-- `σ` is an involution. -/
theorem sigmaMap_involutive : Function.Involutive sigmaMap := by
  intro q
  funext k
  fin_cases k <;> simp [sigmaMap]

/-- `σ` agrees with multiplication by its diagonal matrix. -/
theorem toLin'_sigmaMatrix : ⇑(Matrix.toLin' sigmaMatrix) = sigmaMap := by
  funext q k
  fin_cases k <;>
    simp [sigmaMatrix, Matrix.toLin'_apply, Matrix.mulVec_diagonal, sigmaMap]

/-- The sign involution has determinant one. -/
theorem det_sigmaMatrix : sigmaMatrix.det = 1 := by
  simp [sigmaMatrix, Matrix.det_diagonal, Fin.prod_univ_three]

/-- `σ` is smooth. -/
theorem contDiff_sigmaMap : ContDiff ℝ ⊤ sigmaMap := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp [sigmaMap] <;> fun_prop

theorem continuous_sigmaMap : Continuous sigmaMap :=
  contDiff_sigmaMap.continuous

/-- The sign involution as a continuous linear map. -/
def sigmaCLM : R3 →L[ℝ] R3 :=
  { Matrix.toLin' sigmaMatrix with
    cont := by
      change Continuous ⇑(Matrix.toLin' sigmaMatrix)
      rw [toLin'_sigmaMatrix]
      exact continuous_sigmaMap }

theorem sigmaCLM_apply (q : R3) : sigmaCLM q = sigmaMap q := by
  change (Matrix.toLin' sigmaMatrix) q = sigmaMap q
  rw [toLin'_sigmaMatrix]

/-- `σ` is its own Fréchet derivative everywhere. -/
theorem hasFDerivAt_sigmaMap (q : R3) : HasFDerivAt sigmaMap sigmaCLM q := by
  have h : HasFDerivAt (⇑sigmaCLM) sigmaCLM q := sigmaCLM.hasFDerivAt
  apply h.congr_of_eventuallyEq
  filter_upwards with x
  exact (sigmaCLM_apply x).symm

/-- `σ` as a homeomorphism of the anchor domain. -/
def sigmaHomeomorph : R3 ≃ₜ R3 where
  toFun := sigmaMap
  invFun := sigmaMap
  left_inv := sigmaMap_involutive
  right_inv := sigmaMap_involutive
  continuous_toFun := continuous_sigmaMap
  continuous_invFun := continuous_sigmaMap

/-- `σ` is a measurable embedding. -/
theorem measurableEmbedding_sigmaMap :
    MeasurableEmbedding sigmaMap :=
  sigmaHomeomorph.measurableEmbedding

/-- `σ` preserves Lebesgue measure on the anchor domain. -/
theorem measurePreserving_sigmaMap :
    MeasurePreserving sigmaMap (volume : Measure R3) volume := by
  have hdet : sigmaMatrix.det ≠ 0 := by rw [det_sigmaMatrix]; norm_num
  refine ⟨continuous_sigmaMap.measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := sigmaMatrix) hdet
  rw [toLin'_sigmaMatrix] at hmap
  rw [hmap, det_sigmaMatrix]
  norm_num

set_option maxHeartbeats 1600000 in
-- The three adjugate-entry expansions with sign substitution are
-- normalization-heavy, as in the other explicit dual-field computations.
/-- The sign involution reverses the first dual field: `X1 ∘ σ = -σ ∘ X1`.
This is an exact polynomial identity on the adjugate entries of the anchor
Jacobian. -/
theorem X1_sigmaMap (q : R3) : X1 (sigmaMap q) = -sigmaMap (X1 q) := by
  funext k
  fin_cases k <;>
    simp [X1, dualVectorField, dualMatrixF, Matrix.adjugate_fin_three,
      jacobianMatrix, F, sigmaMap] <;>
    ring

/-- Rearranged form: `σ` applied to the field equals minus the field at the
reflected point. -/
theorem sigmaMap_X1 (q : R3) : sigmaMap (X1 q) = -X1 (sigmaMap q) := by
  rw [X1_sigmaMap, neg_neg]

end ExoticCCR
