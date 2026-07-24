/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremD
import ExoticCCR.LinearPMapDeficiency

/-!
# Conditional A001 Theorem E infrastructure

The smooth, divergence-free, incomplete properties of `X1` are unconditional.
Failure of essential self-adjointness remains conditional on an explicit
transport-necessity hypothesis; no deficiency vectors are constructed here.
-/

noncomputable section

open Matrix MvPolynomial
open scoped LinearPMap

namespace ExoticCCR

/-- Pointwise evaluation of the polynomial divergence identity for `X1`. -/
theorem divergence_X1_eq_zero (q : R3) :
    eval q (dualFieldDivergence ℝ 1) = 0 := by
  rw [dualFieldDivergence_eq_zero]
  simp

/-- The exact analytic package about `X1` established without operator theory. -/
structure SmoothDivergenceFreeIncomplete (X : R3 → R3) : Prop where
  smooth : ContDiff ℝ ⊤ X
  divergenceFree : ∀ q, eval q (dualFieldDivergence ℝ 1) = 0
  incomplete : ¬IsCompleteVectorField X

/-- `X1` is smooth, polynomially divergence-free, and incomplete. -/
theorem X1_smooth_divergenceFree_incomplete :
    SmoothDivergenceFreeIncomplete X1 := by
  exact ⟨contDiff_X1, divergence_X1_eq_zero, X1_incomplete.2⟩

/-- A nonzero vector in one of the two adjoint eigenspaces at `±i`. -/
def HasAdjointDeficiency (H : L2R3 →ₗ.[ℂ] L2R3) : Prop :=
  (∃ u : H†.domain, (u : L2R3) ≠ 0 ∧ H† u = Complex.I • (u : L2R3)) ∨
  (∃ u : H†.domain, (u : L2R3) ≠ 0 ∧ H† u = -Complex.I • (u : L2R3))

/--
Generic deficiency obstruction for an operator with dense domain.
-/
theorem not_ess_of_deficiency {H : L2R3 →ₗ.[ℂ] L2R3}
    (hDense : Dense (H.domain : Set L2R3))
    (hDef : HasAdjointDeficiency H) : ¬H.IsEssentiallySelfAdjoint :=
  hDef.elim
    (fun ⟨_, hu0, hu⟩ ↦ not_isEssentiallySelfAdjoint_of_adjoint_eigen_I hDense hu0 hu)
    (fun ⟨_, hu0, hu⟩ ↦ not_isEssentiallySelfAdjoint_of_adjoint_eigen_negI hDense hu0 hu)

/--
The missing transport-necessity statement for a specified `L²` realization.
It is a definition, not an axiom and not a theorem asserted by this artifact.

This compatibility surface is superseded for realizations carrying explicit
adjoint deficiency data by `not_ess_of_deficiency` above.
-/
def TransportNecessityStatement : Prop :=
  ∀ H : MinimalTransportRealization X1,
    SmoothDivergenceFreeIncomplete X1 →
      ¬(minimalTransport H).IsEssentiallySelfAdjoint

/-- Conditional A001 Theorem E from the explicit transport-necessity hypothesis. -/
theorem theoremE_of_transportNecessity {H : MinimalTransportRealization X1}
    (hN : TransportNecessityStatement) :
    ¬(minimalTransport H).IsEssentiallySelfAdjoint :=
  hN H X1_smooth_divergenceFree_incomplete

end ExoticCCR
