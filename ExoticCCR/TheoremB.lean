/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.DualMatrix

/-!
# Algebraic core of A001 Theorem B

We define the polynomial cotangent-lift evaluation and prove its explicit
non-injectivity at zero covector.  The Poisson-bracket layer is not asserted
here.
-/

noncomputable section

open Function Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- Evaluation of a polynomial `3 × 3` matrix at a point. -/
def evalDualMatrixF (q : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  (dualMatrixF K).map (eval q)

/-- The algebraic cotangent-lift formula `(q,p) ↦ (F(q), B(q)p)`. -/
def cotangentLiftF (z : (Fin 3 → K) × (Fin 3 → K)) :
    (Fin 3 → K) × (Fin 3 → K) :=
  (evalMap (F K) z.1, evalDualMatrixF K z.1 *ᵥ z.2)

variable {K}

/-- T0.B.2: all three collision sources lift to the same point at zero covector. -/
theorem cotangentLiftF_three_zero_collisions (h2 : (2 : K) ≠ 0) :
    cotangentLiftF K (![0, 0, -(1 / 4)], 0) = (![-(1 / 4), 0, 0], 0) ∧
    cotangentLiftF K (![1, -(3 / 2), 13 / 2], 0) = (![-(1 / 4), 0, 0], 0) ∧
    cotangentLiftF K (![-1, 3 / 2, 13 / 2], 0) = (![-(1 / 4), 0, 0], 0) := by
  simp only [cotangentLiftF, Matrix.mulVec_zero, evalMap_F_p0, evalMap_F_p1 h2,
    evalMap_F_p2 h2]
  simp

/-- T0.B.3: the algebraic cotangent lift is not injective. -/
theorem cotangentLiftF_not_injective (h2 : (2 : K) ≠ 0) :
    ¬Injective (cotangentLiftF K) := by
  intro hinj
  have himage :
      cotangentLiftF K (![0, 0, -(1 / 4)], 0) =
        cotangentLiftF K (![1, -(3 / 2), 13 / 2], 0) :=
    (cotangentLiftF_three_zero_collisions h2).1.trans
      (cotangentLiftF_three_zero_collisions h2).2.1.symm
  have hsource := hinj himage
  have hcoord := congrArg (fun z => z.1 0) hsource
  simp at hcoord

end ExoticCCR
