/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.DualFields

/-!
# The polynomial dual matrix for the anchor map

This file isolates the exact adjugate construction of `B = J⁻ᵀ`.  It proves only
the polynomial matrix identity `J Bᵀ = I`; no analytic or operator conclusion is
drawn from it.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- The polynomial matrix `B = -(adj J)ᵀ / 2` for the anchor map `F`. -/
def dualMatrixF : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K) :=
  (C (-(2 : K)⁻¹) : MvPolynomial (Fin 3) K) •
    (jacobianMatrix (F K)).adjugate.transpose

/-- T0.B.1: the exact polynomial identity `J Bᵀ = I`. -/
theorem jacobian_mul_dualMatrixF_transpose (h2 : (2 : K) ≠ 0) :
    jacobianMatrix (F K) * (dualMatrixF K).transpose = 1 := by
  rw [dualMatrixF, transpose_smul, transpose_transpose, Matrix.mul_smul]
  rw [jacobian_mul_adjugate_F, jacobianDet_F]
  ext i j
  simp [h2]

end ExoticCCR
