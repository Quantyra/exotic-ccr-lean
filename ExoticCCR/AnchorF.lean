/-
Copyright (c) 2026 Daniel Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fredriksen
-/
import ExoticCCR.Basic

/-!
# Anchor map F (announced form, det = -2)

Gate 0 certificates T0.1 (jacobian determinant) and T0.2 (three-point collision)
for the EXOTIC-CCR Jacobian counterexample anchor.

These are finite exact algebraic identities only. See `INTEGRITY.md`.
-/

noncomputable section

open Matrix Function MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- The three components of the announced counterexample as multivariate polynomials. -/
def F : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) * (C 4 + C 3 * (X 0 * X 1)),
    X 1 + C 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 + C 3 * X 0 * X 1 ^ 2 * (C 4 + C 3 * (X 0 * X 1)),
    C 2 * X 0 - C 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2]

/-- T0.1: Jacobian determinant of F is the constant -2. -/
theorem jacobianDet_F : jacobianDet (F K) = C (-2) := by
  simp only [jacobianDet, jacobianMatrix, det_fin_three, of_apply, F, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, map_add, map_sub, Derivation.map_one_eq_zero, pderiv_mul,
    pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  simp only [map_neg, map_ofNat]
  ring

variable {K}

/-- T0.2 collision witness: F(0, 0, -1/4) = (-1/4, 0, 0). -/
theorem evalMap_F_p0 : evalMap (F K) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] := by
  funext i
  fin_cases i <;> simp [evalMap, F]

/-- T0.2 collision witness: F(1, -3/2, 13/2) = (-1/4, 0, 0) (char ≠ 2). -/
theorem evalMap_F_p1 (h2 : (2 : K) ≠ 0) :
    evalMap (F K) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;> simp [evalMap, F] <;> field_simp [h4] <;> ring

/-- T0.2 collision witness: F(-1, 3/2, 13/2) = (-1/4, 0, 0) (char ≠ 2). -/
theorem evalMap_F_p2 (h2 : (2 : K) ≠ 0) :
    evalMap (F K) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;> simp [evalMap, F] <;> field_simp [h4] <;> ring

end ExoticCCR
