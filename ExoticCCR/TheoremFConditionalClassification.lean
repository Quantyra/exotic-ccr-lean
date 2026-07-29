/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ExoticCCR.TheoremFHilbertIndex

/-!
# Conditional von Neumann extension classification for Theorem F

This module records a generic extension-theoretic formulation as an explicit
hypothesis.  The generic API does not by itself prove that the hypothesis
holds or construct a self-adjoint extension.  For the specific canonical
minimal operator `H_X1_min`, the hypothesis is now constructed and the
classification is proved in `ExoticCCR.TheoremFVonNeumannClassification`.

The generic consequence below is deliberately modest: if a classification
equivalence identifies self-adjoint extension witnesses with linear isometry
equivalences between the two deficiency spaces, then a nontrivial `Nplus`
produces two distinct extension witnesses from any one classification
parameter and its precomposition by negation.  The distinctness proof uses
only the verified `LinearIsometryEquiv.neg` map; no von Neumann theorem is
smuggled in as an axiom or an asserted theorem.
-/

noncomputable section

open scoped LinearPMap

namespace ExoticCCR

/-! ### Extension witnesses and the conditional classification interface -/

/-- A self-adjoint `LinearPMap` extending a given operator. -/
structure SelfAdjointExtension (S : L2R3 →ₗ.[ℂ] L2R3) where
  /-- The candidate extension operator. -/
  op : L2R3 →ₗ.[ℂ] L2R3
  /-- The candidate contains the graph of the original operator. -/
  extendsOp : S ≤ op
  /-- The candidate is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint op

variable {Nplus Nminus : Type*}
variable [NormedAddCommGroup Nplus] [NormedSpace ℂ Nplus]
variable [NormedAddCommGroup Nminus] [NormedSpace ℂ Nminus]

/--
The generic von Neumann classification statement is an input datum.

In particular, constructing a value of this structure requires independently
proving the classification equivalence.  The later
`ExoticCCR.TheoremFVonNeumannClassification` module supplies such a value for
the specific canonical minimal operator `H_X1_min`.
-/
structure VonNeumannClassificationHypothesis
    (S : L2R3 →ₗ.[ℂ] L2R3)
    (Nplus Nminus : Type*)
    [NormedAddCommGroup Nplus] [NormedSpace ℂ Nplus]
    [NormedAddCommGroup Nminus] [NormedSpace ℂ Nminus] where
  /-- The assumed classification parameterization of extension witnesses. -/
  classification :
    SelfAdjointExtension S ≃ (Nplus ≃ₗᵢ[ℂ] Nminus)

/-! ### The generic two-witness consequence -/

/-- Negation changes every nontrivial linear-isometry parameter. -/
theorem linearIsometryEquiv_ne_neg_trans_of_nontrivial
    [Nontrivial Nplus] (e : Nplus ≃ₗᵢ[ℂ] Nminus) :
    e ≠ (LinearIsometryEquiv.neg ℂ (E := Nplus)).trans e := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : Nplus)
  have hx' : e x = e (-x) := by
    simpa using LinearIsometryEquiv.congr_fun h x
  have hx'' : x = -x := e.injective hx'
  have hsum : x + x = 0 := by
    rw [← neg_eq_iff_add_eq_zero]
    exact hx''.symm
  have htwo : (2 : ℂ) • x = 0 := by simpa [two_smul ℂ x] using hsum
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  have hxzero : x = 0 := (smul_eq_zero.mp htwo).resolve_left htwo_ne
  exact hx hxzero

/--
Under the explicit classification hypothesis, any classification parameter
and its negated parameter yield distinct self-adjoint extension witnesses
whenever `Nplus` is nontrivial.
-/
theorem exists_two_distinct_extensions_of_classification
    (S : L2R3 →ₗ.[ℂ] L2R3)
    (hClass : VonNeumannClassificationHypothesis S Nplus Nminus)
    [Nontrivial Nplus] (e : Nplus ≃ₗᵢ[ℂ] Nminus) :
    ∃ A B : SelfAdjointExtension S, A ≠ B := by
  let e' := (LinearIsometryEquiv.neg ℂ (E := Nplus)).trans e
  have he : e ≠ e' := linearIsometryEquiv_ne_neg_trans_of_nontrivial e
  refine ⟨hClass.classification.symm e, hClass.classification.symm e', ?_⟩
  intro h
  apply he
  simpa using congrArg hClass.classification h

/-! ### Theorem F specialization of the generic conditional API -/

/-- The two adjoint eigenspaces used by the verified Theorem F module. -/
abbrev TheoremFPlusSpace := adjointEigenspace H_X1_min Complex.I
abbrev TheoremFMinusSpace := adjointEigenspace H_X1_min (-Complex.I)

/--
The generic classification interface specialized to the canonical Theorem F
minimal operator.  This module only defines the alias; an inhabitant is
constructed later in `ExoticCCR.TheoremFVonNeumannClassification`.
-/
abbrev TheoremFClassificationHypothesis :=
  VonNeumannClassificationHypothesis H_X1_min TheoremFPlusSpace TheoremFMinusSpace

/--
The generic two-witness consequence specialized to Theorem F's deficiency
spaces.  The classification equivalence remains an explicit argument, and
the `Nontrivial` instance remains an explicit argument of this generic
consequence.  Both are discharged for `H_X1_min` in
`ExoticCCR.TheoremFVonNeumannClassification`.
-/
theorem theoremF_exists_two_distinct_extensions_of_classification
    (hClass : TheoremFClassificationHypothesis)
    [Nontrivial TheoremFPlusSpace]
    (e : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    ∃ A B : SelfAdjointExtension H_X1_min, A ≠ B :=
  exists_two_distinct_extensions_of_classification H_X1_min hClass e

end ExoticCCR
