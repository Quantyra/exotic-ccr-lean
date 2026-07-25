/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardBranch
import ExoticCCR.TheoremEDeficiency
import Mathlib.Data.EReal.Basic

/-!
# Forward saturated sheets

This module records the geometric data that a full forward sheet would have to
provide before an integration-by-parts argument can be attempted.  In
particular, both ends of every flow interval are explicit: the upper end
escapes, while the lower end is either `-∞` or a finite escaping end.

`ForwardBranchOpen` does not presently give an inhabitant of this structure.
It is a local `s = β - τ²` collar whose parameter domain need not contain a
whole interval in `s`, and only its wall-end escape has been proved.  Thus this
module deliberately proves no weak-adjoint statement and no Theorem E.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff EReal Topology

namespace ExoticCCR

/-- A full forward flow sheet, including the endpoint data needed to account
for every boundary term in a future integration-by-parts proof.

The maps are total only for Lean convenience.  Their asserted geometric and
differential properties are restricted to `D`. -/
structure ForwardSaturatedSheet where
  /-- Transverse `(a,c)` parameters. -/
  W : Set (ℝ × ℝ)
  isOpen_W : IsOpen W
  nonempty_W : W.Nonempty
  /-- Finite upper flow time. -/
  β : ℝ × ℝ → ℝ
  contDiff_β : ContDiffOn ℝ ⊤ β W
  /-- Possibly infinite lower flow time. -/
  ℓ : ℝ × ℝ → EReal
  lower_lt_upper : ∀ x ∈ W, ℓ x < (β x : EReal)
  /-- The full open interval bundle over `W`. -/
  D : Set ((ℝ × ℝ) × ℝ)
  D_eq : D = {p | p.1 ∈ W ∧ ℓ p.1 < (p.2 : EReal) ∧ p.2 < β p.1}
  isOpen_D : IsOpen D
  /-- Flow-sheet parameterization. -/
  Psi : ((ℝ × ℝ) × ℝ) → R3
  contDiffOn_Psi : ContDiffOn ℝ ⊤ Psi D
  injOn_Psi : Set.InjOn Psi D
  /-- The anchor map reads off `(a,s,c)` on the sheet. -/
  evalMap_Psi : ∀ p ∈ D, evalMap (F ℝ) (Psi p) = ![p.1.1, p.2, p.1.2]
  /-- The `s`-lines are integral curves of `X1` throughout the sheet. -/
  hasDerivAt_Psi_s : ∀ x s, (x, s) ∈ D →
    HasDerivAt (fun t : ℝ => Psi (x, t)) (X1 (Psi (x, s))) s
  /-- Every upper endpoint escapes all compact norm balls. -/
  escape_upper : ∀ x ∈ W,
    Tendsto (fun s : ℝ => ‖Psi (x, s)‖) (𝓝[<] β x) atTop
  /-- A lower endpoint is either `-∞`, or finite and escaping from the right.
  This disjunction prevents a finite lower boundary from being silently
  discarded in integration by parts. -/
  lower_ok : ∀ x ∈ W,
    ℓ x = ⊥ ∨ ∃ L : ℝ, ℓ x = (L : EReal) ∧
      Tendsto (fun s : ℝ => ‖Psi (x, s)‖) (𝓝[>] L) atTop

namespace ForwardSaturatedSheet

/-- Membership in a saturated-sheet domain is exactly membership in its full
open interval bundle. -/
theorem mem_D_iff (S : ForwardSaturatedSheet) (x : ℝ × ℝ) (s : ℝ) :
    (x, s) ∈ S.D ↔ x ∈ S.W ∧ S.ℓ x < (s : EReal) ∧ s < S.β x := by
  rw [S.D_eq]
  rfl

end ForwardSaturatedSheet

end ExoticCCR
