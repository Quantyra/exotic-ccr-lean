/-
Copyright (c) 2026 Daniel Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fredriksen
-/
import ExoticCCR.Basic

/-!
# Anchor map G (det-1 normalization)

Determinant-one form of the counterexample anchor, obtained by a diagonal
rescaling of F. Used for the all-characteristic packaging theorem.
-/

noncomputable section

open Matrix Function MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- Determinant-1 form: diag(1/2, 1/2, -1/2) ∘ F ∘ diag(1, 2, 2) (char ≠ 2).
In characteristic 2 it reduces to a map identifying (0,1,0) and (1,1,0). -/
def G : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(1 + C 2 * X 0 * X 1) ^ 3 * X 2
      + C 4 * X 1 ^ 2 * (1 + C 2 * X 0 * X 1) * (C 2 + C 3 * (X 0 * X 1)),
    X 1 + C 3 * X 0 * (1 + C 2 * X 0 * X 1) ^ 2 * X 2
      + C 12 * X 0 * X 1 ^ 2 * (C 2 + C 3 * (X 0 * X 1)),
    -X 0 + C 3 * X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2]

/-- Jacobian determinant of G is the constant 1. -/
theorem jacobianDet_G : jacobianDet (G K) = 1 := by
  simp only [jacobianDet, jacobianMatrix, det_fin_three, of_apply, G, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, map_add, map_neg, Derivation.map_one_eq_zero,
    pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true]
  simp only [map_ofNat]
  ring

variable {K}

theorem evalMap_G_p0 : evalMap (G K) ![0, 0, -(1 / 8)] = ![-(1 / 8), 0, 0] := by
  funext i
  fin_cases i <;> simp [evalMap, G]

theorem evalMap_G_p1 (h2 : (2 : K) ≠ 0) :
    evalMap (G K) ![1, -(3 / 4), 13 / 4] = ![-(1 / 8), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := (by norm_num : (2 : K) * 4 = 8) ▸ mul_ne_zero h2 h4
  funext i
  fin_cases i <;> simp [evalMap, G] <;> field_simp [h4, h8] <;> ring

theorem evalMap_G_p2 (h2 : (2 : K) ≠ 0) :
    evalMap (G K) ![-1, 3 / 4, 13 / 4] = ![-(1 / 8), 0, 0] := by
  have h4 : (4 : K) ≠ 0 := (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  have h8 : (8 : K) ≠ 0 := (by norm_num : (2 : K) * 4 = 8) ▸ mul_ne_zero h2 h4
  funext i
  fin_cases i <;> simp [evalMap, G] <;> field_simp [h4, h8] <;> ring

/-- In characteristic 2, G identifies (0, 1, 0) and (1, 1, 0). -/
theorem evalMap_G_char_two (h2 : (2 : K) = 0) :
    evalMap (G K) ![0, 1, 0] = evalMap (G K) ![1, 1, 0] := by
  funext i
  fin_cases i <;>
    simp only [evalMap, G, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, map_add, map_mul, map_pow, map_neg, map_one,
      eval_C, eval_X]
  · linear_combination (-26 : K) * h2
  · linear_combination (-30 : K) * h2
  · linear_combination (-1 : K) * h2

end ExoticCCR
