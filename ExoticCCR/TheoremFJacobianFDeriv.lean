/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.AnchorF

/-!
# Fréchet derivative of the anchor polynomial map

This module identifies the analytic derivative of the real evaluation map with
the evaluated algebraic Jacobian.  It contains only finite-dimensional real
calculus and determinant identities.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

/-- The derivative candidate for evaluation of a multivariate real polynomial. -/
def evalPDeriv (p : MvPolynomial (Fin 3) ℝ) (q : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ∑ j, eval q (pderiv j p) * v j
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        change (∑ j ∈ Finset.univ, eval q (pderiv j p) * (c * x j)) =
          c * ∑ j ∈ Finset.univ, eval q (pderiv j p) * x j
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }

/-- Evaluation of a multivariate real polynomial has derivative given by its
evaluated formal partial derivatives. -/
theorem hasFDerivAt_eval_mvPolynomial (p : MvPolynomial (Fin 3) ℝ)
    (q : Fin 3 → ℝ) : HasFDerivAt (fun x => eval x p) (evalPDeriv p q) q := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hder : evalPDeriv (C a) q = 0 := by
        ext v
        simp [evalPDeriv]
      rw [hder]
      simpa using (hasFDerivAt_const (𝕜 := ℝ) a q)
  | add p r hp hr =>
      have hfun : (fun x => eval x (p + r)) =
          (fun x => eval x p + eval x r) := by
        funext x
        simp
      have hder : evalPDeriv (p + r) q = evalPDeriv p q + evalPDeriv r q := by
        ext v
        simp [evalPDeriv]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hfun, hder]
      exact hp.add hr
  | mul_X p n hp =>
      have hfun : (fun x => eval x (p * X n)) =
          (fun x => eval x p * x n) := by
        funext x
        simp
      have hder : evalPDeriv (p * X n) q =
          eval q p • ContinuousLinearMap.proj n + q n • evalPDeriv p q := by
        ext v
        fin_cases n <;> simp [evalPDeriv, Fin.sum_univ_succ] <;> ring
      rw [hfun, hder]
      exact hp.mul (hasFDerivAt_apply n q)

/-- The evaluated Jacobian, regarded as a continuous linear endomorphism. -/
def evalJacobianF (q : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin' ((jacobianMatrix (F ℝ)).map (eval q)))

/-- The Fréchet derivative of the real evaluation map of `F` is its evaluated
polynomial Jacobian. -/
theorem hasFDerivAt_evalMap_F (q : Fin 3 → ℝ) :
    HasFDerivAt (evalMap (F ℝ)) (evalJacobianF q) q := by
  rw [hasFDerivAt_pi']
  intro i
  have hfun : (fun x => evalMap (F ℝ) x i) = (fun x => eval x (F ℝ i)) := rfl
  have hder : (ContinuousLinearMap.proj i).comp (evalJacobianF q) =
      evalPDeriv (F ℝ i) q := by
    ext v
    simp [evalJacobianF, evalPDeriv, jacobianMatrix, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct]
  rw [hfun, hder]
  exact hasFDerivAt_eval_mvPolynomial (F ℝ i) q

/-- The `fderiv` of the real evaluation map of `F`. -/
theorem fderiv_evalMap_F (q : Fin 3 → ℝ) :
    fderiv ℝ (evalMap (F ℝ)) q = evalJacobianF q :=
  (hasFDerivAt_evalMap_F q).fderiv

/-- The determinant of the analytic derivative of `F` is constantly `-2`. -/
theorem det_fderiv_evalMap_F (q : Fin 3 → ℝ) :
    (fderiv ℝ (evalMap (F ℝ)) q).det = -2 := by
  rw [fderiv_evalMap_F, evalJacobianF, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin']
  change ((eval q).mapMatrix (jacobianMatrix (F ℝ))).det = -2
  rw [← (eval q).map_det, ← jacobianDet, jacobianDet_F]
  simp

end ExoticCCR
