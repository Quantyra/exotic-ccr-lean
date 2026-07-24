/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardWall

/-!
# Base slice for the A001 forward branch

This module records the extended `G+` polynomial on the wall and verifies the
positive base root and its nondegeneracy. It does not construct an open branch.
-/

noncomputable section

namespace ExoticCCR

/-- The continuous wall value of the cubic part of the forward `G+` equation. -/
def wallGPlusAtWall (As B r : ℝ) : ℝ :=
  (-As) * r ^ 3 + B * r

/-- The wall-value cubic is smooth in its coefficients and root variable. -/
theorem contDiff_wallGPlusAtWall :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ℝ => wallGPlusAtWall p.1.1 p.1.2 p.2) := by
  unfold wallGPlusAtWall
  fun_prop

/-- The positive large-`q₀` branch base value is a root of the wall cubic. -/
theorem wallGPlus_base_sqrt2 :
    wallGPlusAtWall (-(1 / 2)) (-1) (Real.sqrt 2) = 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  unfold wallGPlusAtWall
  rw [show (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt]]
  ring

/-- The root derivative is nonzero at the positive branch base value. -/
theorem wallGPlus_base_deriv_ne :
    deriv (fun r => wallGPlusAtWall (-1 / 2) (-1) r) (Real.sqrt 2) ≠ 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  have hderiv :
      HasDerivAt (fun r : ℝ => wallGPlusAtWall (-1 / 2) (-1) r) 2
        (Real.sqrt 2) := by
    have hraw := (((hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2)).pow 3).const_mul
      (1 / 2)).sub (hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2))
    have hfun :
        (fun r : ℝ => wallGPlusAtWall (-1 / 2) (-1) r) =
          fun r : ℝ => (1 / 2) * r ^ 3 - r := by
      funext r
      simp [wallGPlusAtWall]
      ring
    rw [hfun]
    convert hraw using 1
    all_goals try rfl
    norm_num [hsqrt]
  rw [hderiv.deriv]
  norm_num

end ExoticCCR
