/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.DualMatrix

/-!
# Algebraic core of A001 Theorem C

The rows of the polynomial dual matrix define directional polynomial
derivations.  This file proves their action on the anchor coordinates, the
Piola row-divergence identity, and full commutation on all multivariate
polynomials.  The associated abstract polynomial Weyl-algebra endomorphism is
constructed in `ExoticCCR.TheoremCWeyl`; analytic operators remain open.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- Directional polynomial operation defined by row `j` of the dual matrix. -/
def dualField (j : Fin 3) (p : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  ∑ k : Fin 3, dualMatrixF K j k * pderiv k p

/-- The dual field bundled as a polynomial derivation. -/
def dualFieldDerivation (j : Fin 3) :
    Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K) :=
  ∑ k : Fin 3, (dualMatrixF K j k) • pderiv k

@[simp] theorem dualFieldDerivation_apply (j : Fin 3) (p : MvPolynomial (Fin 3) K) :
    dualFieldDerivation K j p = dualField K j p := by
  rw [dualFieldDerivation, dualField]
  change (∑ k : Fin 3, ((dualMatrixF K j k) • pderiv k) p) = _
  simp [Derivation.smul_apply, smul_eq_mul]

/-- The coefficient divergence of row `j` of the dual matrix. -/
def dualFieldDivergence (j : Fin 3) : MvPolynomial (Fin 3) K :=
  ∑ k : Fin 3, pderiv k (dualMatrixF K j k)

variable {K}

/-- T0.C.1: the dual fields send anchor coordinates to Kronecker deltas. -/
theorem dualField_F (h2 : (2 : K) ≠ 0) (i j : Fin 3) :
    dualField K j (F K i) = if i = j then 1 else 0 := by
  have h := congrArg (fun M => M i j) (jacobian_mul_dualMatrixF_transpose K h2)
  simpa [dualField, jacobianMatrix, Matrix.mul_apply, Matrix.one_apply, mul_comm] using h

@[simp] theorem dualField_C (j : Fin 3) (a : K) : dualField K j (C a) = 0 := by
  simp [dualField]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Expanding the explicit three-variable adjugate requires a larger normalization budget.
/-- T0.C.2: the rows of the polynomial dual matrix are divergence-free. -/
theorem dualFieldDivergence_eq_zero (j : Fin 3) :
    dualFieldDivergence K j = 0 := by
  have pderiv_nat (i : Fin 3) (n : ℕ) :
      pderiv i (n : MvPolynomial (Fin 3) K) = 0 := by
    rw [← C_eq_coe_nat]
    exact pderiv_C
  have pderiv_two (i : Fin 3) :
      pderiv i (2 : MvPolynomial (Fin 3) K) = 0 := pderiv_nat i 2
  have pderiv_three (i : Fin 3) :
      pderiv i (3 : MvPolynomial (Fin 3) K) = 0 := pderiv_nat i 3
  fin_cases j <;>
    simp [dualFieldDivergence, dualMatrixF, Matrix.adjugate_fin_three,
      jacobianMatrix, F, Fin.sum_univ_succ, pderiv_two, pderiv_three] <;>
    ring

/-- The algebraic bracket vanishes on every anchor coordinate `F k`. -/
theorem dualField_bracket_on_F (h2 : (2 : K) ≠ 0) (i j k : Fin 3) :
    dualField K i (dualField K j (F K k)) -
      dualField K j (dualField K i (F K k)) = 0 := by
  rw [dualField_F h2, dualField_F h2]
  split_ifs
  all_goals
    simp only [dualField, Derivation.map_one_eq_zero, map_zero, mul_zero,
      Finset.sum_const_zero, sub_self]

set_option maxHeartbeats 1000000 in
-- Derivation extensionality and the polynomial matrix inverse require extra elaboration time.
/-- T0.C.3: the dual fields commute as derivations on all polynomials. -/
theorem dualField_bracket_eq_zero (h2 : (2 : K) ≠ 0) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) K) :
    dualField K i (dualField K j p) - dualField K j (dualField K i p) = 0 := by
  let D : Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K) :=
    ⁅dualFieldDerivation K i, dualFieldDerivation K j⁆
  have hD_apply (q : MvPolynomial (Fin 3) K) :
      D q = dualField K i (dualField K j q) - dualField K j (dualField K i q) := by
    simp [D, Derivation.commutator_apply]
  have hF (k : Fin 3) : D (F K k) = 0 := by
    rw [hD_apply]
    exact dualField_bracket_on_F h2 i j k
  have hcoord (q : MvPolynomial (Fin 3) K) :
      D q = ∑ k : Fin 3, pderiv k q * D (X k) := by
    let E : Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K) :=
      ∑ k : Fin 3, (D (X k)) • pderiv k
    have hDE : D = E := by
      apply MvPolynomial.derivation_ext
      intro k
      fin_cases k <;>
        simp [E, Fin.sum_univ_succ, smul_eq_mul]
    rw [hDE]
    change (∑ k : Fin 3, ((D (X k)) • pderiv k) q) = _
    simp only [Derivation.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm, ← hDE]
  let v : Fin 3 → MvPolynomial (Fin 3) K := fun k => D (X k)
  have hJv : jacobianMatrix (F K) *ᵥ v = 0 := by
    funext k
    change (∑ l : Fin 3, pderiv l (F K k) * D (X l)) = 0
    exact (hcoord (F K k)).symm.trans (hF k)
  have hleft : (dualMatrixF K).transpose * jacobianMatrix (F K) = 1 :=
    mul_eq_one_comm.mp (jacobian_mul_dualMatrixF_transpose K h2)
  have hv : v = 0 := by
    calc
      v = (1 : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K)) *ᵥ v := by simp
      _ = ((dualMatrixF K).transpose * jacobianMatrix (F K)) *ᵥ v := by rw [hleft]
      _ = (dualMatrixF K).transpose *ᵥ (jacobianMatrix (F K) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hJv]; simp
  rw [← hD_apply p]
  have hD : D = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    exact congrFun hv k
  rw [hD]
  rfl

end ExoticCCR
