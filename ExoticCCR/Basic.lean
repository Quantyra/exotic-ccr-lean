/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import Mathlib

/-!
# Basic Jacobian helpers for EXOTIC-CCR Gate 0

Jacobian matrix, determinant, and evaluation map for families of
multivariate polynomials. Exact algebraic infrastructure only.
-/

noncomputable section

open Matrix Function

namespace MvPolynomial

variable {R : Type*} {σ : Type*}

/-- Jacobian matrix of a family of multivariate polynomials. -/
def jacobianMatrix [CommSemiring R] [DecidableEq σ] (F : σ → MvPolynomial σ R) :
    Matrix σ σ (MvPolynomial σ R) :=
  Matrix.of fun i j => pderiv j (F i)

/-- Jacobian determinant of a family of multivariate polynomials. -/
def jacobianDet [CommRing R] [Fintype σ] [DecidableEq σ] (F : σ → MvPolynomial σ R) :
    MvPolynomial σ R :=
  (jacobianMatrix F).det

/-- Polynomial self-map induced by a family of multivariate polynomials. -/
def evalMap [CommSemiring R] (F : σ → MvPolynomial σ R) (p : σ → R) : σ → R :=
  fun i => eval p (F i)

end MvPolynomial
