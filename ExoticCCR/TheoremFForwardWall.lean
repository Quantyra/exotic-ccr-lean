/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.Basic

/-!
# Algebraic base point for the A001 forward wall

Only the cubic and its base-point identities are recorded here.  In
particular, this module does not construct an open wall family or a deficiency
vector.
-/

namespace ExoticCCR

/-- The forward-wall cubic from the A001 calculation. -/
def wallA (a s c : ℝ) : ℝ :=
  -c * s ^ 3 + s ^ 2 + 18 * a * c * s - 27 * a ^ 2 * c ^ 2 - 16 * a

/-- The formal partial derivative of `wallA` in its `s` variable. -/
def wallADerivS (a s c : ℝ) : ℝ :=
  -3 * c * s ^ 2 + 2 * s + 18 * a * c

/-- The proposed forward-wall base point lies on the cubic. -/
theorem wallA_basePoint : wallA 0 (1 / 2) 2 = 0 := by
  norm_num [wallA]

/-- The `s`-derivative expression has value `-1/2` at the base point. -/
theorem wallADerivS_basePoint : wallADerivS 0 (1 / 2) 2 = -(1 / 2) := by
  norm_num [wallADerivS]

/-- The `s`-derivative expression is nonzero at the base point. -/
theorem wallADerivS_basePoint_ne_zero : wallADerivS 0 (1 / 2) 2 ≠ 0 := by
  rw [wallADerivS_basePoint]
  norm_num

end ExoticCCR
