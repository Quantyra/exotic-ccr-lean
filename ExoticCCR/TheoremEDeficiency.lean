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

open MeasureTheory
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

/-- It is enough to verify the weak `-i` identity on every embedded test
function. -/
theorem weakAdjoint_negI_of_test {u : L2R3}
    (h : ∀ φ : CcinftyR3,
      inner ℂ ((-Complex.I) • u) (testFunctionToL2 φ) =
        inner ℂ u (transportAction X1 contDiff_X1.continuous φ)) :
    WeakAdjointEigenvector
      (minimalTransportCore X1 contDiff_X1.continuous)
      (-Complex.I) u := by
  intro x
  have hxRange : (x : L2R3) ∈ LinearMap.range testFunctionToL2 := by
    rw [← minimalTransportCore_domain X1 contDiff_X1.continuous]
    exact x.property
  rcases hxRange with ⟨φ, hφ⟩
  have hx : x =
      ⟨testFunctionToL2 φ, by
        rw [minimalTransportCore_domain X1 contDiff_X1.continuous]
        exact LinearMap.mem_range_self testFunctionToL2 φ⟩ := by
    exact Subtype.ext hφ.symm
  subst x
  simpa [minimalTransportCore_apply] using h φ

/-- Representative-integral form of the weak `-i` reduction.  The remaining
analytic obligation is exactly the displayed identity for every test function. -/
theorem weakAdjoint_negI_of_representative_integrals {f : R3 → ℂ}
    (hf : MemLp f 2 (volume : Measure R3))
    (h : ∀ φ : CcinftyR3,
      inner ℂ ((-Complex.I) • hf.toLp f) (testFunctionToL2 φ) =
        ∫ q : R3, inner ℂ (f q) (minimalTransportExpression X1 φ q) ∂volume) :
    WeakAdjointEigenvector
      (minimalTransportCore X1 contDiff_X1.continuous)
      (-Complex.I) (hf.toLp f) := by
  apply weakAdjoint_negI_of_test
  intro φ
  rw [h φ]
  exact (inner_toLp_toLp_eq_integral hf
    (transportExpressionMemLp X1 contDiff_X1.continuous φ)).symm

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
