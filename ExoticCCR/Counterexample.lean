/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.AnchorF
import ExoticCCR.AnchorG

/-!
# Non-injectivity packaging theorems (Gate 0)

Standard packaging: a polynomial self-map of K³ with unit Jacobian determinant
that is not injective. Exact algebraic packaging only — see `INTEGRITY.md`.
-/

noncomputable section

open Function MvPolynomial ExoticCCR

/-- Over every field of characteristic not 2, there is a polynomial self-map of K³
whose Jacobian determinant is a unit but which is not injective (via anchor F). -/
theorem not_injective_unit_jacobian_char_ne_two {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) K, IsUnit (jacobianDet F) → Injective (evalMap F) := by
  intro h
  have hunit : IsUnit (jacobianDet (F K)) := by
    rw [jacobianDet_F]
    exact (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr h2)).map C
  have h12 : (![1, -(3 / 2), 13 / 2] : Fin 3 → K) = ![-1, 3 / 2, 13 / 2] :=
    h (F K) hunit ((evalMap_F_p1 h2).trans (evalMap_F_p2 h2).symm)
  have h0 : (1 : K) = -1 := congrFun h12 0
  exact h2 (by linear_combination h0)

/-- Over every field K, there is a polynomial self-map of K³ with Jacobian
determinant 1 which is not injective (via anchor G). -/
theorem not_injective_unit_jacobian (K : Type*) [Field K] :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) K, IsUnit (jacobianDet F) → Injective (evalMap F) := by
  intro h
  have hunit : IsUnit (jacobianDet (G K)) := jacobianDet_G K ▸ isUnit_one
  by_cases h2 : (2 : K) = 0
  · have h01 : (![0, 1, 0] : Fin 3 → K) = ![1, 1, 0] :=
      h (G K) hunit (evalMap_G_char_two h2)
    exact zero_ne_one (congrFun h01 0)
  · have h12 : (![1, -(3 / 4), 13 / 4] : Fin 3 → K) = ![-1, 3 / 4, 13 / 4] :=
      h (G K) hunit ((evalMap_G_p1 h2).trans (evalMap_G_p2 h2).symm)
    have h0 : (1 : K) = -1 := congrFun h12 0
    exact h2 (by linear_combination h0)

/-- Specialization: the packaging holds over ℂ. -/
theorem not_injective_unit_jacobian_complex :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) ℂ, IsUnit (jacobianDet F) → Injective (evalMap F) :=
  not_injective_unit_jacobian ℂ
