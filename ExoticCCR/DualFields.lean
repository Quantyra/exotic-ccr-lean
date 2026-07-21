/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.AnchorF

/-!
# Dual-field algebraic infrastructure (Gate B/C export)

`jacobian_mul_adjugate_F`: \(J\cdot\operatorname{adj}(J)=(\det J)\,I\) for the
Jacobian of anchor F — polynomial form of the dual-matrix identity behind
\(B=J^{-T}\).

Combined with `jacobianDet_F` (`= C (-2)`), this is the algebraic backbone of
the A001 Poisson/Weyl dual lift. No ESS / channel claims.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

theorem jacobian_mul_adjugate_F :
    jacobianMatrix (F K) * (jacobianMatrix (F K)).adjugate =
      jacobianDet (F K) • (1 : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K)) :=
  Matrix.mul_adjugate _

end ExoticCCR
