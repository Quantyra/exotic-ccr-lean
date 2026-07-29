/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFFiniteDeficiency

/-!
# Standard adjoint eigenspaces for the minimal transport core

This module upgrades the weak `-i` eigenspace results to the standard
deficiency formulation: the eigenspace of mathlib's `LinearPMap.adjoint`.
On a densely defined operator the weak eigenspace and the adjoint eigenspace
coincide, so the canonical minimal transport core of `X1` has an
infinite-dimensional standard `-i` deficiency subspace.

It also names the remaining `+i` obligation as an explicit statement
(`X1BackwardWeakFamiliesStatement`, a definition and not an axiom) and records
the conditional two-sided consequence.  It does not assert the `+i`
construction, a deficiency-index pair, or full Theorem F.
-/

noncomputable section

open MeasureTheory
open scoped LinearPMap

namespace ExoticCCR

/-- The standard eigenspace of the adjoint at `z`: vectors of the adjoint
domain on which the adjoint acts by `z`.  For a densely defined symmetric
operator the spaces at `z = ±i` are the two deficiency subspaces, labeled
throughout this repository by the adjoint eigenvalue `z`. -/
def adjointEigenspace (H : L2R3 →ₗ.[ℂ] L2R3) (z : ℂ) : Submodule ℂ L2R3 where
  carrier := {u | ∃ hu : u ∈ (H†).domain, H† ⟨u, hu⟩ = z • u}
  zero_mem' := by
    refine ⟨(H†).domain.zero_mem, ?_⟩
    have h0 : (⟨0, (H†).domain.zero_mem⟩ : (H†).domain) = 0 := rfl
    rw [h0, LinearPMap.map_zero, smul_zero]
  add_mem' := by
    rintro u v ⟨hu, hHu⟩ ⟨hv, hHv⟩
    refine ⟨(H†).domain.add_mem hu hv, ?_⟩
    have hsum : (⟨u + v, (H†).domain.add_mem hu hv⟩ : (H†).domain) =
        ⟨u, hu⟩ + ⟨v, hv⟩ := Subtype.ext rfl
    rw [hsum, LinearPMap.map_add, hHu, hHv]
    exact (smul_add z u v).symm
  smul_mem' := by
    rintro c u ⟨hu, hHu⟩
    refine ⟨(H†).domain.smul_mem c hu, ?_⟩
    have hsc : (⟨c • u, (H†).domain.smul_mem c hu⟩ : (H†).domain) =
        c • ⟨u, hu⟩ := Subtype.ext rfl
    rw [hsc, LinearPMap.map_smul, hHu]
    exact smul_comm c z u

/-- Membership in the standard adjoint eigenspace, unfolded. -/
theorem mem_adjointEigenspace_iff {H : L2R3 →ₗ.[ℂ] L2R3} {z : ℂ} {u : L2R3} :
    u ∈ adjointEigenspace H z ↔
      ∃ hu : u ∈ (H†).domain, H† ⟨u, hu⟩ = z • u := Iff.rfl

/-! ### Cardinal-valued standard deficiency indices -/

/-- The standard cardinal-valued deficiency index at `z`, defined as the
dimension of the standard adjoint eigenspace.  The usual deficiency indices
are obtained by evaluating this at `+i` and `-i` for a densely defined
symmetric operator. -/
def standardDeficiencyIndex (H : L2R3 →ₗ.[ℂ] L2R3) (z : ℂ) : Cardinal :=
  Module.rank ℂ (adjointEigenspace H z)

/-- A non-finite-dimensional standard eigenspace has at least countable
cardinal dimension.  This records the consequence supported by the
finite-family arguments without asserting exact equality with `ℵ₀`. -/
theorem aleph0_le_standardDeficiencyIndex_of_not_finiteDimensional
    {H : L2R3 →ₗ.[ℂ] L2R3} {z : ℂ}
    (h : ¬ FiniteDimensional ℂ (adjointEigenspace H z)) :
    ℵ₀ ≤ standardDeficiencyIndex H z := by
  rw [standardDeficiencyIndex, ← not_lt, Module.rank_lt_aleph0_iff]
  exact h

/-- On a densely defined operator the weak adjoint eigenspace is exactly the
standard eigenspace of the adjoint. -/
theorem weakAdjointEigenspace_eq_adjointEigenspace
    (H : L2R3 →ₗ.[ℂ] L2R3) (hDense : Dense (H.domain : Set L2R3)) (z : ℂ) :
    weakAdjointEigenspace H z = adjointEigenspace H z := by
  ext u
  constructor
  · intro hu
    have hu' : WeakAdjointEigenvector H z u := hu
    exact ⟨mem_adjoint_domain_of_weakAdjointEigenvector hu',
      adjoint_apply_eq_of_weakAdjointEigenvector hDense hu'⟩
  · rintro ⟨huDom, huEq⟩
    intro x
    rw [← huEq]
    exact H.adjoint_isFormalAdjoint hDense ⟨u, huDom⟩ x

/-- The standard `-i` deficiency subspace of the canonical minimal transport
core is not finite-dimensional. -/
theorem adjointEigenspace_negI_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (adjointEigenspace H_X1_min (-Complex.I)) := by
  rw [← weakAdjointEigenspace_eq_adjointEigenspace H_X1_min
    (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) (-Complex.I)]
  exact weakAdjointEigenspace_negI_not_finiteDimensional

/-- The forward branch therefore gives a countable lower bound for the
standard `-i` deficiency index. -/
theorem aleph0_le_standardDeficiencyIndex_negI :
    ℵ₀ ≤ standardDeficiencyIndex H_X1_min (-Complex.I) :=
  aleph0_le_standardDeficiencyIndex_of_not_finiteDimensional
    adjointEigenspace_negI_not_finiteDimensional

/-- The remaining obligation for the `+i` side of Theorem F: arbitrarily large
finite linearly independent weak `+i` families for the canonical minimal
transport core.  Definition only; not an axiom and not asserted. -/
def X1BackwardWeakFamiliesStatement : Prop :=
  ∀ n : ℕ, ∃ u : Fin n → L2R3,
    LinearIndependent ℂ u ∧
      ∀ i, WeakAdjointEigenvector H_X1_min Complex.I (u i)

/-- Conditional two-sided statement: the named `+i` obligation would make both
standard deficiency subspaces of the canonical minimal transport core
infinite-dimensional.  The hypothesis is not discharged by this artifact. -/
theorem adjointEigenspace_both_not_finiteDimensional_of_backwardFamilies
    (h : X1BackwardWeakFamiliesStatement) :
    ¬ FiniteDimensional ℂ (adjointEigenspace H_X1_min Complex.I) ∧
      ¬ FiniteDimensional ℂ (adjointEigenspace H_X1_min (-Complex.I)) := by
  constructor
  · rw [← weakAdjointEigenspace_eq_adjointEigenspace H_X1_min
      (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) Complex.I]
    exact weakAdjointEigenspace_not_finiteDimensional_of_finite_families
      H_X1_min Complex.I h
  · exact adjointEigenspace_negI_not_finiteDimensional

end ExoticCCR
