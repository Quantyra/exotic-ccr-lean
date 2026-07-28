/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardWall

/-!
# Base slice for the A001 backward wall

This module records the smooth divided-difference extension of the backward
`G-` equation and constructs its fixed-height local positive-root germ. It does
not assert a global backward sheet or construct a deficiency vector.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- The polynomial extension of the quotient obtained by moving from `alpha`
to `alpha + tau^2` in the wall polynomial. -/
def wallADividedDiffPlus (a alpha c tau : ℝ) : ℝ :=
  -3 * c * alpha ^ 2 - 3 * c * alpha * tau ^ 2 - c * tau ^ 4 +
    2 * alpha + tau ^ 2 + 18 * a * c

/-- The finite difference of `wallA` in the positive direction factors by `tau^2`. -/
theorem wallA_add_eq_tau2_mul_dividedDiffPlus (a alpha c tau : ℝ) :
    wallA a (alpha + tau ^ 2) c - wallA a alpha c =
      tau ^ 2 * wallADividedDiffPlus a alpha c tau := by
  simp [wallA, wallADividedDiffPlus]
  ring_nf

/-- At `tau = 0`, the positive divided difference is the wall derivative. -/
theorem wallADividedDiffPlus_zero (a alpha c : ℝ) :
    wallADividedDiffPlus a alpha c 0 = wallADerivS a alpha c := by
  simp [wallADividedDiffPlus, wallADerivS]

/-- The positive divided-difference extension is smooth in all four variables. -/
theorem contDiff_wallADividedDiffPlus :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      wallADividedDiffPlus p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold wallADividedDiffPlus
  fun_prop

/-- The smooth extended backward equation before dividing the root by `tau`. -/
def wallGMinus (a c alpha tau r : ℝ) : ℝ :=
  wallADividedDiffPlus a alpha c tau * r ^ 3 +
    wallB (alpha + tau ^ 2) c * r + wallC c * tau

/-- The extended backward equation is smooth in its five scalar variables. -/
theorem contDiff_wallGMinus :
    ContDiff ℝ ⊤ (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ =>
      wallGMinus p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2) := by
  unfold wallGMinus wallADividedDiffPlus wallB wallC
  fun_prop

/-- The backward base point lies on the wall polynomial. -/
theorem wallA_backward_basePoint :
    wallA (1 / 54) (1 / 2) 2 = 0 := by
  norm_num [wallA]

/-- The wall derivative at the backward base point is `1/6`. -/
theorem wallADerivS_backward_basePoint :
    wallADerivS (1 / 54) (1 / 2) 2 = 1 / 6 := by
  norm_num [wallADerivS]

/-- At the backward base point, `G-` is `(1/6) r^3 - r`. -/
theorem wallGMinus_backward_base_eq (r : ℝ) :
    wallGMinus (1 / 54) 2 (1 / 2) 0 r = (1 / 6) * r ^ 3 - r := by
  norm_num [wallGMinus, wallADividedDiffPlus, wallB, wallC]
  ring_nf

/-- The positive backward branch base value is a root of the extended equation. -/
theorem wallGMinus_base_sqrt6 :
    wallGMinus (1 / 54) 2 (1 / 2) 0 (Real.sqrt 6) = 0 := by
  have hsqrt : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by norm_num
  rw [wallGMinus_backward_base_eq]
  rw [show (Real.sqrt 6) ^ 3 = 6 * Real.sqrt 6 by
    calc
      (Real.sqrt 6) ^ 3 = (Real.sqrt 6) ^ 2 * Real.sqrt 6 := by ring
      _ = 6 * Real.sqrt 6 := by rw [hsqrt]]
  ring

/-- The root derivative is nonzero at the positive backward base value. -/
theorem wallGMinus_base_deriv_ne :
    deriv (fun r : ℝ => (1 / 6) * r ^ 3 - r) (Real.sqrt 6) ≠ 0 := by
  have hsqrt : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by norm_num
  have hderiv : HasDerivAt (fun r : ℝ => (1 / 6) * r ^ 3 - r) 2
      (Real.sqrt 6) := by
    convert (((hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 6)).pow 3).const_mul
      (1 / 6)).sub (hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 6)) using 1
    all_goals try rfl
    norm_num [hsqrt]
  rw [hderiv.deriv]
  norm_num

/-- The partial derivative in the root variable is nonzero at the backward base point. -/
theorem wallGMinus_base_partial_r_ne :
    deriv (fun r => wallGMinus (1 / 54) 2 (1 / 2) 0 r) (Real.sqrt 6) ≠ 0 := by
  have hfun :
      (fun r : ℝ => wallGMinus (1 / 54) 2 (1 / 2) 0 r) =
        fun r : ℝ => (1 / 6) * r ^ 3 - r := by
    funext r
    exact wallGMinus_backward_base_eq r
  rw [hfun]
  exact wallGMinus_base_deriv_ne

end ExoticCCR
