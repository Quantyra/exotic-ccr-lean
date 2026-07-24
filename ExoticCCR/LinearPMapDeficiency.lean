/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TransportOperator

/-!
# Deficiency vectors for partially defined operators

This file connects the weak inner-product formulation of an adjoint
eigenvector to mathlib's `LinearPMap.adjoint`, and records the standard
obstruction at the two nonreal points `±i`.
-/

noncomputable section

open Set
open scoped LinearPMap

namespace ExoticCCR

/-- The weak adjoint eigenvector identity on the domain of `H`. -/
def WeakAdjointEigenvector (H : L2R3 →ₗ.[ℂ] L2R3) (z : ℂ) (u : L2R3) : Prop :=
  ∀ x : H.domain, inner ℂ (z • u) (x : L2R3) = inner ℂ u (H x)

/-- A weak adjoint eigenvector belongs to the domain of the adjoint. -/
theorem mem_adjoint_domain_of_weakAdjointEigenvector
    {H : L2R3 →ₗ.[ℂ] L2R3} {z : ℂ} {u : L2R3}
    (hu : WeakAdjointEigenvector H z u) : u ∈ H†.domain :=
  H.mem_adjoint_domain_of_exists u ⟨z • u, fun x ↦ by simpa using hu x⟩

/-- On a dense domain, the adjoint acts on a weak eigenvector by its weak eigenvalue. -/
theorem adjoint_apply_eq_of_weakAdjointEigenvector
    {H : L2R3 →ₗ.[ℂ] L2R3} {z : ℂ} {u : L2R3}
    (hDense : Dense (H.domain : Set L2R3))
    (hu : WeakAdjointEigenvector H z u) :
    H† ⟨u, mem_adjoint_domain_of_weakAdjointEigenvector hu⟩ = z • u :=
  H.adjoint_apply_eq hDense _ fun x ↦ by simpa using hu x

/-- A weak adjoint identity extends from a closable operator to its closure. -/
private theorem weakAdjointEigenvector_closure
    {H : L2R3 →ₗ.[ℂ] L2R3} {z : ℂ} {u : L2R3}
    (hClosable : H.IsClosable) (hu : WeakAdjointEigenvector H z u) :
    WeakAdjointEigenvector H.closure z u := by
  intro x
  let S : Set (L2R3 × L2R3) :=
    {p | inner ℂ (z • u) p.1 = inner ℂ u p.2}
  have hSclosed : IsClosed S := by
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hgraph : ((x : L2R3), H.closure x) ∈ H.graph.topologicalClosure := by
    rw [hClosable.graph_closure_eq_closure_graph]
    exact H.closure.mem_graph x
  change ((x : L2R3), H.closure x) ∈ closure (H.graph : Set (L2R3 × L2R3)) at hgraph
  have hsub : (H.graph : Set (L2R3 × L2R3)) ⊆ S := by
    intro p hp
    obtain ⟨y, hy₁, hy₂⟩ := H.mem_graph_iff.mp hp
    change inner ℂ (z • u) p.1 = inner ℂ u p.2
    simpa [← hy₁, ← hy₂] using hu y
  exact closure_minimal hsub hSclosed hgraph

/-- A nonzero weak adjoint eigenvector at `i` obstructs essential self-adjointness. -/
private theorem not_isEssentiallySelfAdjoint_of_weak_eigen_I
    {H : L2R3 →ₗ.[ℂ] L2R3} {u : L2R3} (hu0 : u ≠ 0)
    (hu : WeakAdjointEigenvector H Complex.I u) :
    ¬H.IsEssentiallySelfAdjoint := by
  rintro ⟨hClosable, hSelf⟩
  have huClosure := weakAdjointEigenvector_closure hClosable hu
  have huDom : u ∈ H.closure†.domain :=
    mem_adjoint_domain_of_weakAdjointEigenvector huClosure
  have hApply : H.closure† ⟨u, huDom⟩ = Complex.I • u :=
    adjoint_apply_eq_of_weakAdjointEigenvector hSelf.dense_domain huClosure
  have hAdj : H.closure† = H.closure := LinearPMap.isSelfAdjoint_def.mp hSelf
  have hle : H.closure† ≤ H.closure := hAdj.le
  have huDom' : u ∈ H.closure.domain := hle.1 huDom
  have hApply' : H.closure ⟨u, huDom'⟩ = Complex.I • u := by
    exact (hle.2 (x := ⟨u, huDom⟩) (y := ⟨u, huDom'⟩) rfl).symm.trans hApply
  have hinner := huClosure ⟨u, huDom'⟩
  rw [hApply'] at hinner
  have hnormsq : -(‖u‖ ^ 2) = ‖u‖ ^ 2 := by
    have him := congrArg Complex.im hinner
    simp [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K] at him
    norm_num [pow_two, Complex.mul_re] at him
    simpa [pow_two] using him
  have hnorm : ‖u‖ = 0 := by nlinarith [sq_nonneg ‖u‖]
  exact hu0 (norm_eq_zero.mp hnorm)

/-- A nonzero weak adjoint eigenvector at `-i` obstructs essential self-adjointness. -/
private theorem not_isEssentiallySelfAdjoint_of_weak_eigen_negI
    {H : L2R3 →ₗ.[ℂ] L2R3} {u : L2R3} (hu0 : u ≠ 0)
    (hu : WeakAdjointEigenvector H (-Complex.I) u) :
    ¬H.IsEssentiallySelfAdjoint := by
  rintro ⟨hClosable, hSelf⟩
  have huClosure := weakAdjointEigenvector_closure hClosable hu
  have huDom : u ∈ H.closure†.domain :=
    mem_adjoint_domain_of_weakAdjointEigenvector huClosure
  have hApply : H.closure† ⟨u, huDom⟩ = (-Complex.I) • u :=
    adjoint_apply_eq_of_weakAdjointEigenvector hSelf.dense_domain huClosure
  have hAdj : H.closure† = H.closure := LinearPMap.isSelfAdjoint_def.mp hSelf
  have hle : H.closure† ≤ H.closure := hAdj.le
  have huDom' : u ∈ H.closure.domain := hle.1 huDom
  have hApply' : H.closure ⟨u, huDom'⟩ = (-Complex.I) • u := by
    exact (hle.2 (x := ⟨u, huDom⟩) (y := ⟨u, huDom'⟩) rfl).symm.trans hApply
  have hinner := huClosure ⟨u, huDom'⟩
  rw [hApply'] at hinner
  have hnormsq : ‖u‖ ^ 2 = -(‖u‖ ^ 2) := by
    have him := congrArg Complex.im hinner
    simp [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K] at him
    norm_num [pow_two, Complex.mul_re] at him
    simpa [pow_two] using him
  have hnorm : ‖u‖ = 0 := by nlinarith [sq_nonneg ‖u‖]
  exact hu0 (norm_eq_zero.mp hnorm)

/-- A nonzero `i`-eigenvector of the adjoint obstructs essential self-adjointness. -/
theorem not_isEssentiallySelfAdjoint_of_adjoint_eigen_I
    {H : L2R3 →ₗ.[ℂ] L2R3} (hDense : Dense (H.domain : Set L2R3))
    {u : H†.domain} (hu0 : (u : L2R3) ≠ 0)
    (hu : H† u = Complex.I • (u : L2R3)) :
    ¬H.IsEssentiallySelfAdjoint := by
  apply not_isEssentiallySelfAdjoint_of_weak_eigen_I hu0
  intro x
  rw [← hu]
  exact (H.adjoint_isFormalAdjoint hDense u x)

/-- A nonzero `-i`-eigenvector of the adjoint obstructs essential self-adjointness. -/
theorem not_isEssentiallySelfAdjoint_of_adjoint_eigen_negI
    {H : L2R3 →ₗ.[ℂ] L2R3} (hDense : Dense (H.domain : Set L2R3))
    {u : H†.domain} (hu0 : (u : L2R3) ≠ 0)
    (hu : H† u = -Complex.I • (u : L2R3)) :
    ¬H.IsEssentiallySelfAdjoint := by
  apply not_isEssentiallySelfAdjoint_of_weak_eigen_negI hu0
  intro x
  rw [← hu]
  exact (H.adjoint_isFormalAdjoint hDense u x)

end ExoticCCR
