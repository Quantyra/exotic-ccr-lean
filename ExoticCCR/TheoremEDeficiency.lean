/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TransportCore
import ExoticCCR.LinearPMapDeficiency
import ExoticCCR.TheoremD
import ExoticCCR.TheoremE

/-!
# A weak-deficiency route toward A001 Theorem E

This module isolates the remaining geometric/analytic witness needed by the
canonical minimal transport core.  It does not construct that witness and does
not derive it from incompleteness.
-/

noncomputable section

open scoped LinearPMap

namespace ExoticCCR

/-- The canonical minimal transport core for the first escaping dual field. -/
abbrev H_X1_min := minimalTransportCore X1 contDiff_X1.continuous

/-- The remaining geometric/analytic obligation: a nonzero `L²` weak `-i`
eigenvector for the canonical minimal transport of `X1`. Definition only; not
an axiom. -/
def X1ForwardWeakDeficiencyStatement : Prop :=
  ∃ u : L2R3,
    u ≠ 0 ∧
    WeakAdjointEigenvector
      (minimalTransportCore X1 contDiff_X1.continuous)
      (-Complex.I) u

/-- An explicit weak forward-deficiency witness supplies adjoint deficiency for
the canonical minimal transport core. -/
theorem hasAdjointDeficiency_of_forwardWeakDeficiency
    (h : X1ForwardWeakDeficiencyStatement) :
    HasAdjointDeficiency H_X1_min := by
  obtain ⟨u, hu0, hu⟩ := h
  have hDense : Dense (H_X1_min.domain : Set L2R3) :=
    minimalTransportCore_dense_domain X1 contDiff_X1.continuous
  have huDom : u ∈ ((H_X1_min)†).domain :=
    mem_adjoint_domain_of_weakAdjointEigenvector hu
  refine Or.inr ⟨⟨u, huDom⟩, hu0, ?_⟩
  exact adjoint_apply_eq_of_weakAdjointEigenvector hDense hu

/-- Conditional Theorem E from an explicit weak deficiency witness (preferred
over `TransportNecessityStatement`). Still conditional until the wall
construction lands. -/
theorem theoremE_of_forwardWeakDeficiency
    (h : X1ForwardWeakDeficiencyStatement) :
    ¬(minimalTransportCore X1 contDiff_X1.continuous).IsEssentiallySelfAdjoint := by
  apply not_ess_of_deficiency
    (minimalTransportCore_dense_domain X1 contDiff_X1.continuous)
  exact hasAdjointDeficiency_of_forwardWeakDeficiency h

end ExoticCCR
