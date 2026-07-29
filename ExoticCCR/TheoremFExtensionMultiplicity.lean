/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFVonNeumannClassification

/-!
# Unit-phase multiplicity for the canonical Theorem F operator

For the specific canonical minimal operator `H_X1_min`, the sign involution
gives a fixed complex-linear isometric equivalence from the `+i` deficiency
space to the `-i` deficiency space.  Multiplying that equivalence by a unitary
complex scalar and applying the proved von Neumann construction gives an
injective family of self-adjoint extension witnesses.

This module deliberately states the parameterized injection.  It does not
identify the exact cardinality of the full extension type.
-/

noncomputable section

namespace ExoticCCR

/-- The self-adjoint extension obtained by multiplying the sigma deficiency
equivalence by a unitary complex phase. -/
noncomputable def theoremFUnitPhaseExtension (α : unitary ℂ) :
    SelfAdjointExtension H_X1_min :=
  vonNeumannSelfAdjointExtension (α • theoremFDeficiencySigmaEquiv)

/-- Distinct unitary complex phases give distinct self-adjoint extension
witnesses for the canonical minimal operator `H_X1_min`. -/
theorem theoremFUnitPhaseExtension_injective :
    Function.Injective theoremFUnitPhaseExtension := by
  letI : Nontrivial TheoremFPlusSpace := theoremFPlusSpace_nontrivial
  intro α β hαβ
  have hEquiv :
      α • theoremFDeficiencySigmaEquiv =
        β • theoremFDeficiencySigmaEquiv := by
    apply vonNeumannSelfAdjointExtension_injective
    exact hαβ
  obtain ⟨p, hp⟩ := exists_ne (0 : TheoremFPlusSpace)
  have hp0 : p ≠ 0 := hp
  have hep0 : theoremFDeficiencySigmaEquiv p ≠ 0 :=
    theoremFDeficiencySigmaEquiv.injective.ne hp0
  have happ := LinearIsometryEquiv.congr_fun hEquiv p
  simp only [LinearIsometryEquiv.smul_apply] at happ
  apply Subtype.ext
  exact smul_left_injective ℂ hep0 happ

end ExoticCCR
