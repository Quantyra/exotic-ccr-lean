/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.AnchorF

/-!
# Algebraic core of the A001 Theorem D witness

The square-root parameter is replaced in the definitions by an algebraic
variable `s`.  Current coverage is one exact rational specialization satisfying
`s² = 1 - 2t`; the parameterized identity remains open.  No ODE, limit, or
incompleteness statement is asserted.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- First coordinate of the algebraic blow-up witness. -/
def blowupQ0 (t s : K) : K := (-2 * t - s + 1) / (t * (2 * t - 1))

/-- Third coordinate of the algebraic blow-up witness. -/
def blowupQ2 (t s : K) : K := t ^ 2 * (2 * t - 3 * s - 1)

/-- The radical-cleared parameterized witness point. -/
def blowupCurve (t s : K) : Fin 3 → K := ![blowupQ0 K t s, t, blowupQ2 K t s]

/-- T0.D.alg (partial): an exact rational point on the proposed algebraic witness. -/
theorem evalMap_F_blowupCurve_sample :
    evalMap (F ℚ) (blowupCurve ℚ (3 / 8) (1 / 2)) = ![0, 3 / 8, 2] := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, F, blowupCurve, blowupQ0, blowupQ2] <;>
    norm_num [cons_val_two, head_cons, tail_cons]

end ExoticCCR
