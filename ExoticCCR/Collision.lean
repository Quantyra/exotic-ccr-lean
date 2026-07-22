/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.AnchorF
import ExoticCCR.DualFields

/-!
# Collision packaging + dual-field export (Lean deepen)

Three-point collision equality for anchor F, and re-export of
`jacobian_mul_adjugate_F` as the algebraic dual-matrix identity.

Exact algebra only — no ESS / CCR / channel claims. See `INTEGRITY.md`.
-/

noncomputable section

open Function MvPolynomial

namespace ExoticCCR

variable {K : Type*} [Field K]

/-- Three distinct inputs collide under F (char ≠ 2). -/
theorem collision_three_points_F (h2 : (2 : K) ≠ 0) :
    evalMap (F K) ![0, 0, -(1 / 4)] =
      evalMap (F K) ![1, -(3 / 2), 13 / 2] ∧
    evalMap (F K) ![1, -(3 / 2), 13 / 2] =
      evalMap (F K) ![-1, 3 / 2, 13 / 2] ∧
    evalMap (F K) ![0, 0, -(1 / 4)] =
      (![-(1 / 4), 0, 0] : Fin 3 → K) := by
  refine ⟨?_, ?_, evalMap_F_p0⟩
  · exact (evalMap_F_p0).trans (evalMap_F_p1 h2).symm
  · exact (evalMap_F_p1 h2).trans (evalMap_F_p2 h2).symm

/-- Collision target is the common image point. -/
theorem collision_target_F (h2 : (2 : K) ≠ 0) :
    evalMap (F K) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] ∧
    evalMap (F K) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] ∧
    evalMap (F K) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by
  exact ⟨evalMap_F_p0, evalMap_F_p1 h2, evalMap_F_p2 h2⟩

/-- Dual-matrix identity: \(J\cdot\operatorname{adj}(J)=(\det J)\,I\) for anchor F. -/
theorem dual_matrix_identity_F :
    jacobianMatrix (F K) * (jacobianMatrix (F K)).adjugate =
      jacobianDet (F K) • (1 : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K)) :=
  jacobian_mul_adjugate_F K

/-- Combined Gate-0 algebra package: det constant and dual-matrix identity. -/
theorem gate0_algebra_F :
    jacobianDet (F K) = C (-2) ∧
      jacobianMatrix (F K) * (jacobianMatrix (F K)).adjugate =
        jacobianDet (F K) • (1 : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K)) :=
  ⟨jacobianDet_F K, dual_matrix_identity_F⟩

end ExoticCCR
