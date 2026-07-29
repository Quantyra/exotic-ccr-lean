/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFVonNeumannFormula
import ExoticCCR.TheoremFConditionalClassification

/-!
# Von Neumann extension graphs for Theorem F

This module constructs the operator graph associated to a linear isometry
equivalence between the two standard deficiency spaces.  It proves that the
candidate graph is functional, defines the corresponding `LinearPMap`, gives
its exact graph formula, and proves that it densely extends the closed minimal
operator.

Self-adjointness and the classification equivalence are not asserted here.
-/

noncomputable section

open scoped LinearPMap

namespace ExoticCCR

/-! ### The boundary graph selected by a deficiency-space isometry -/

/-- The boundary contribution selected by a deficiency-space isometry:
`u ↦ (u + Uu, i u - i Uu)`. -/
def vonNeumannBoundaryGraphMap
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    TheoremFPlusSpace →ₗ[ℂ] L2R3 × L2R3 where
  toFun u :=
    ((u : L2R3) + (U u : L2R3),
      Complex.I • (u : L2R3) - Complex.I • (U u : L2R3))
  map_add' u v := by
    simp only [map_add, Submodule.coe_add, Prod.mk_add_mk]
    apply Prod.ext <;> module
  map_smul' c u := by
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply, Prod.smul_mk]
    apply Prod.ext <;> module

/-- The plain-product graph prescribed by von Neumann's extension formula:
the graph of the closed minimal operator plus the selected boundary graph. -/
def vonNeumannExtensionGraph
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    Submodule ℂ (L2R3 × L2R3) :=
  H_X1_min.closure.graph ⊔ LinearMap.range (vonNeumannBoundaryGraphMap U)

/-- Every selected boundary vector lies in the graph of the adjoint.  This is
the point where the exact Stage B graph decomposition is consumed. -/
theorem vonNeumannBoundaryGraphMap_mem_adjoint_graph
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (u : TheoremFPlusSpace) :
    vonNeumannBoundaryGraphMap U u ∈ (H_X1_min†).graph := by
  have hplus :
      toGraphSpace ((u : L2R3), Complex.I • (u : L2R3)) ∈
        deficiencyLine Complex.I :=
    mem_deficiencyLine_iff.mpr ⟨u, u.property, rfl⟩
  have hminus :
      toGraphSpace ((U u : L2R3), (-Complex.I) • (U u : L2R3)) ∈
        deficiencyLine (-Complex.I) :=
    mem_deficiencyLine_iff.mpr ⟨U u, (U u).property, rfl⟩
  have hsum :
      toGraphSpace ((u : L2R3), Complex.I • (u : L2R3)) +
          toGraphSpace ((U u : L2R3), (-Complex.I) • (U u : L2R3)) ∈
        minimalGraphL2.topologicalClosure ⊔
          deficiencyLine Complex.I ⊔ deficiencyLine (-Complex.I) := by
    apply Submodule.add_mem
    · exact (le_sup_left :
        minimalGraphL2.topologicalClosure ⊔ deficiencyLine Complex.I ≤
          (minimalGraphL2.topologicalClosure ⊔ deficiencyLine Complex.I) ⊔
            deficiencyLine (-Complex.I))
        ((le_sup_right :
          deficiencyLine Complex.I ≤
            minimalGraphL2.topologicalClosure ⊔ deficiencyLine Complex.I) hplus)
    · exact (le_sup_right :
        deficiencyLine (-Complex.I) ≤
          (minimalGraphL2.topologicalClosure ⊔ deficiencyLine Complex.I) ⊔
            deficiencyLine (-Complex.I)) hminus
  have hadj :
      toGraphSpace
          ((u : L2R3) + (U u : L2R3),
            Complex.I • (u : L2R3) - Complex.I • (U u : L2R3)) ∈
        adjointGraphL2 := by
    rw [adjointGraphL2_eq_minimalGraphL2_topologicalClosure_sup_deficiencyLines]
    convert hsum using 1
    simp only [← map_add, Prod.mk_add_mk, neg_smul, sub_eq_add_neg]
  exact (mem_graphL2_iff (H_X1_min†)).mp hadj

/-- The candidate von Neumann graph is a subgraph of the adjoint graph. -/
theorem vonNeumannExtensionGraph_le_adjoint_graph
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    vonNeumannExtensionGraph U ≤ (H_X1_min†).graph := by
  refine sup_le ?_ ?_
  · exact LinearPMap.le_graph_of_le H_X1_min_closure_le_adjoint
  · rintro x ⟨u, rfl⟩
    exact vonNeumannBoundaryGraphMap_mem_adjoint_graph U u

/-- The candidate graph is functional because it is contained in the graph of
the adjoint operator. -/
theorem vonNeumannExtensionGraph_functional
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    ∀ x : L2R3 × L2R3, x ∈ vonNeumannExtensionGraph U →
      x.fst = 0 → x.snd = 0 := by
  intro x hx hx0
  exact (H_X1_min†).graph_fst_eq_zero_snd
    (vonNeumannExtensionGraph_le_adjoint_graph U hx) hx0

/-! ### The associated densely defined operator -/

/-- The `LinearPMap` associated to the selected von Neumann graph. -/
def vonNeumannExtension
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    L2R3 →ₗ.[ℂ] L2R3 :=
  (vonNeumannExtensionGraph U).toLinearPMap

/-- The operator constructed from the candidate graph has exactly that graph;
the fallback branch of `Submodule.toLinearPMap` is never used. -/
theorem vonNeumannExtension_graph
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    (vonNeumannExtension U).graph = vonNeumannExtensionGraph U :=
  Submodule.toLinearPMap_graph_eq _ (vonNeumannExtensionGraph_functional U)

/-- Exact membership in the selected graph, in the classical von Neumann
coordinates `x + u + Uu`. -/
theorem mem_vonNeumannExtensionGraph_iff
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    {p : L2R3 × L2R3} :
    p ∈ vonNeumannExtensionGraph U ↔
      ∃ x : H_X1_min.closure.domain, ∃ u : TheoremFPlusSpace,
        p =
          ((x : L2R3) + (u : L2R3) + (U u : L2R3),
            H_X1_min.closure x +
              Complex.I • (u : L2R3) - Complex.I • (U u : L2R3)) := by
  rw [vonNeumannExtensionGraph, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, ⟨u, rfl⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (LinearPMap.mem_graph_iff' H_X1_min.closure).mp ha
    refine ⟨x, u, ?_⟩
    simp only [vonNeumannBoundaryGraphMap, LinearMap.coe_mk,
      AddHom.coe_mk, Prod.mk_add_mk]
    apply Prod.ext <;> module
  · rintro ⟨x, u, rfl⟩
    refine
      ⟨((x : L2R3), H_X1_min.closure x),
        H_X1_min.closure.mem_graph x,
        vonNeumannBoundaryGraphMap U u, ⟨u, rfl⟩, ?_⟩
    simp only [vonNeumannBoundaryGraphMap, LinearMap.coe_mk,
      AddHom.coe_mk, Prod.mk_add_mk]
    apply Prod.ext <;> module

/-- Exact membership in the domain selected by `U`. -/
theorem mem_vonNeumannExtension_domain_iff
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    {v : L2R3} :
    v ∈ (vonNeumannExtension U).domain ↔
      ∃ x : H_X1_min.closure.domain, ∃ u : TheoremFPlusSpace,
        v = (x : L2R3) + (u : L2R3) + (U u : L2R3) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    rw [vonNeumannExtension_graph, mem_vonNeumannExtensionGraph_iff] at hy
    obtain ⟨x, u, hpair⟩ := hy
    exact ⟨x, u, congrArg Prod.fst hpair⟩
  · rintro ⟨x, u, rfl⟩
    refine
      ⟨H_X1_min.closure x +
          Complex.I • (u : L2R3) - Complex.I • (U u : L2R3), ?_⟩
    rw [vonNeumannExtension_graph, mem_vonNeumannExtensionGraph_iff]
    exact ⟨x, u, rfl⟩

/-- A canonical proof that a von Neumann coordinate sum belongs to the
selected domain. -/
theorem vonNeumannExtension_sum_mem_domain
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (x : H_X1_min.closure.domain) (u : TheoremFPlusSpace) :
    (x : L2R3) + (u : L2R3) + (U u : L2R3) ∈
      (vonNeumannExtension U).domain :=
  (mem_vonNeumannExtension_domain_iff U).mpr ⟨x, u, rfl⟩

/-- The operator action on every von Neumann coordinate sum is
`cl(H)x + i u - i Uu`. -/
theorem vonNeumannExtension_apply_sum
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (x : H_X1_min.closure.domain) (u : TheoremFPlusSpace) :
    vonNeumannExtension U
        ⟨(x : L2R3) + (u : L2R3) + (U u : L2R3),
          vonNeumannExtension_sum_mem_domain U x u⟩ =
      H_X1_min.closure x +
        Complex.I • (u : L2R3) - Complex.I • (U u : L2R3) := by
  apply (vonNeumannExtension U).mem_graph_snd_inj
    ((vonNeumannExtension U).mem_graph
      ⟨(x : L2R3) + (u : L2R3) + (U u : L2R3),
        vonNeumannExtension_sum_mem_domain U x u⟩)
  · rw [vonNeumannExtension_graph, mem_vonNeumannExtensionGraph_iff]
    exact ⟨x, u, rfl⟩
  · rfl

/-- The selected operator extends the closed minimal operator. -/
theorem H_X1_min_closure_le_vonNeumannExtension
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    H_X1_min.closure ≤ vonNeumannExtension U := by
  apply LinearPMap.le_of_le_graph
  rw [vonNeumannExtension_graph]
  exact le_sup_left

/-- In particular, the selected operator extends the original minimal core. -/
theorem H_X1_min_le_vonNeumannExtension
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    H_X1_min ≤ vonNeumannExtension U :=
  H_X1_min.le_closure.trans
    (H_X1_min_closure_le_vonNeumannExtension U)

/-- Every selected von Neumann operator is densely defined. -/
theorem vonNeumannExtension_dense_domain
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    Dense ((vonNeumannExtension U).domain : Set L2R3) :=
  H_X1_min_dense_domain.mono (H_X1_min_le_vonNeumannExtension U).1

/-- The selected boundary vector belongs to the candidate operator domain. -/
theorem vonNeumannExtension_boundary_mem_domain
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (u : TheoremFPlusSpace) :
    (u : L2R3) + (U u : L2R3) ∈ (vonNeumannExtension U).domain := by
  rw [LinearPMap.mem_domain_iff]
  refine ⟨Complex.I • (u : L2R3) - Complex.I • (U u : L2R3), ?_⟩
  rw [vonNeumannExtension_graph]
  exact (le_sup_right :
    LinearMap.range (vonNeumannBoundaryGraphMap U) ≤
      H_X1_min.closure.graph ⊔ LinearMap.range (vonNeumannBoundaryGraphMap U))
        ⟨u, rfl⟩

/-- On the selected boundary vector the candidate has the prescribed action
`i u - i Uu`. -/
theorem vonNeumannExtension_apply_boundary
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (u : TheoremFPlusSpace) :
    vonNeumannExtension U
        ⟨(u : L2R3) + (U u : L2R3),
          vonNeumannExtension_boundary_mem_domain U u⟩ =
      Complex.I • (u : L2R3) - Complex.I • (U u : L2R3) := by
  apply (vonNeumannExtension U).mem_graph_snd_inj
    ((vonNeumannExtension U).mem_graph
      ⟨(u : L2R3) + (U u : L2R3),
        vonNeumannExtension_boundary_mem_domain U u⟩)
  · rw [vonNeumannExtension_graph]
    exact (le_sup_right :
      LinearMap.range (vonNeumannBoundaryGraphMap U) ≤
        H_X1_min.closure.graph ⊔ LinearMap.range (vonNeumannBoundaryGraphMap U))
          ⟨u, rfl⟩
  · rfl

/-- The candidate operator is an intermediate restriction of the adjoint. -/
theorem vonNeumannExtension_le_adjoint
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    vonNeumannExtension U ≤ H_X1_min† := by
  apply LinearPMap.le_of_le_graph
  rw [vonNeumannExtension_graph]
  exact vonNeumannExtensionGraph_le_adjoint_graph U

end ExoticCCR
