/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.DualMatrix

/-!
# Algebraic core of A001 Theorem C

The rows of the polynomial dual matrix define directional polynomial
operations.  This file proves their action on the anchor coordinates and
commutation on those coordinates.  Full commutation, Piola/divergence, analytic
operators, and a Weyl-algebra endomorphism remain open here.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- Directional polynomial operation defined by row `j` of the dual matrix. -/
def dualField (j : Fin 3) (p : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  ∑ k : Fin 3, dualMatrixF K j k * pderiv k p

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

/-- T0.C.2 (partial commutation): the algebraic bracket vanishes on every `F k`. -/
theorem dualField_bracket_on_F (h2 : (2 : K) ≠ 0) (i j k : Fin 3) :
    dualField K i (dualField K j (F K k)) -
      dualField K j (dualField K i (F K k)) = 0 := by
  rw [dualField_F h2, dualField_F h2]
  split_ifs
  all_goals
    simp only [dualField, Derivation.map_one_eq_zero, map_zero, mul_zero,
      Finset.sum_const_zero, sub_self]

end ExoticCCR
