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
operator.  It then computes the submodule adjoint of that graph and proves the
candidate operator self-adjoint, yielding an unconditional
`SelfAdjointExtension` witness for every deficiency-space isometry.

The full classification equivalence is not asserted here.
-/

noncomputable section

open scoped LinearPMap

namespace ExoticCCR

/-! ### Closure and Stage B coordinate prerequisites -/

/-- The adjoint of the minimal core remains a formal adjoint after the minimal
operator is replaced by its closure. -/
theorem H_X1_min_adjoint_isFormalAdjoint_closure :
    (H_X1_min†).IsFormalAdjoint H_X1_min.closure := by
  intro u x
  let S : Set (L2R3 × L2R3) :=
    {p | inner ℂ (H_X1_min† u) p.1 = inner ℂ (u : L2R3) p.2}
  have hSclosed : IsClosed S := isClosed_eq (by fun_prop) (by fun_prop)
  have hxgraph :
      ((x : L2R3), H_X1_min.closure x) ∈
        closure (H_X1_min.graph : Set (L2R3 × L2R3)) := by
    rw [← Submodule.topologicalClosure_coe,
      H_X1_min_isClosable.graph_closure_eq_closure_graph]
    exact H_X1_min.closure.mem_graph x
  have hsub : (H_X1_min.graph : Set (L2R3 × L2R3)) ⊆ S := by
    intro p hp
    obtain ⟨y, hy₁, hy₂⟩ := H_X1_min.mem_graph_iff.mp hp
    change inner ℂ (H_X1_min† u) p.1 = inner ℂ (u : L2R3) p.2
    simpa [← hy₁, ← hy₂] using
      H_X1_min.adjoint_isFormalAdjoint H_X1_min_dense_domain u y
  exact closure_minimal hsub hSclosed hxgraph

/-- The closure of the symmetric minimal core is formally symmetric. -/
theorem H_X1_min_closure_isFormalAdjoint :
    H_X1_min.closure.IsFormalAdjoint H_X1_min.closure := by
  intro x y
  let xa : (H_X1_min†).domain :=
    ⟨x, H_X1_min_closure_le_adjoint.1 x.property⟩
  have hxa :
      H_X1_min† xa = H_X1_min.closure x :=
    (H_X1_min_closure_le_adjoint.2 (x := x) (y := xa) rfl).symm
  rw [← hxa]
  exact H_X1_min_adjoint_isFormalAdjoint_closure xa y

/-- Exact Stage B coordinates for every vector in the adjoint graph. -/
theorem mem_adjoint_graph_exists_vonNeumann_coordinates
    {a b : L2R3} (h : (a, b) ∈ (H_X1_min†).graph) :
    ∃ x : H_X1_min.closure.domain,
      ∃ p : TheoremFPlusSpace, ∃ q : TheoremFMinusSpace,
        (a, b) =
          ((x : L2R3) + (p : L2R3) + (q : L2R3),
            H_X1_min.closure x +
              Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) := by
  have hL2 : toGraphSpace (a, b) ∈ adjointGraphL2 :=
    (mem_graphL2_iff (H_X1_min†)).mpr h
  rw [adjointGraphL2_eq_minimalGraphL2_topologicalClosure_sup_deficiencyLines,
    Submodule.mem_sup] at hL2
  obtain ⟨r, hr, mq, hmq, hsum⟩ := hL2
  rw [Submodule.mem_sup] at hr
  obtain ⟨c, hc, mp, hmp, hcp⟩ := hr
  rw [minimalGraphL2_topologicalClosure_eq_graphL2_closure] at hc
  obtain ⟨x, rfl⟩ := (mem_graphL2_iff_exists H_X1_min.closure).mp hc
  obtain ⟨p, hp, rfl⟩ := mem_deficiencyLine_iff.mp hmp
  obtain ⟨q, hq, rfl⟩ := mem_deficiencyLine_iff.mp hmq
  refine ⟨x, ⟨p, hp⟩, ⟨q, hq⟩, ?_⟩
  apply toGraphSpace.injective
  rw [← hsum, ← hcp, ← map_add, ← map_add]
  congr 1
  apply Prod.ext
  · rfl
  · simp only [Prod.snd_add, neg_smul, sub_eq_add_neg]

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

/-! ### The symplectic boundary calculation -/

/-- A selected boundary graph vector pairs trivially with every vector in the
closed minimal graph. -/
theorem vonNeumannBoundary_pairing_closure
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (u : TheoremFPlusSpace) (x : H_X1_min.closure.domain) :
    inner ℂ
          (Complex.I • (u : L2R3) - Complex.I • (U u : L2R3))
          (x : L2R3) -
        inner ℂ ((u : L2R3) + (U u : L2R3))
          (H_X1_min.closure x) = 0 := by
  obtain ⟨huDom, huEq⟩ :=
    mem_adjointEigenspace_iff.mp u.property
  obtain ⟨hUuDom, hUuEq⟩ :=
    mem_adjointEigenspace_iff.mp (U u).property
  have hplus :
      inner ℂ (Complex.I • (u : L2R3)) (x : L2R3) =
        inner ℂ (u : L2R3) (H_X1_min.closure x) := by
    simpa only [huEq, Subtype.coe_eta] using
      H_X1_min_adjoint_isFormalAdjoint_closure
        ⟨(u : L2R3), huDom⟩ x
  have hminus :
      inner ℂ ((-Complex.I) • (U u : L2R3)) (x : L2R3) =
        inner ℂ (U u : L2R3) (H_X1_min.closure x) := by
    simpa only [hUuEq, Subtype.coe_eta] using
      H_X1_min_adjoint_isFormalAdjoint_closure
        ⟨(U u : L2R3), hUuDom⟩ x
  have hminus' :
      -inner ℂ (Complex.I • (U u : L2R3)) (x : L2R3) =
        inner ℂ (U u : L2R3) (H_X1_min.closure x) := by
    simpa only [neg_smul, inner_neg_left] using hminus
  rw [inner_sub_left, inner_add_left]
  linear_combination hplus + hminus'

/-- The reversed closure-boundary pairing also vanishes. -/
theorem closure_pairing_vonNeumannBoundary
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (x : H_X1_min.closure.domain) (u : TheoremFPlusSpace) :
    inner ℂ (H_X1_min.closure x)
          ((u : L2R3) + (U u : L2R3)) -
        inner ℂ (x : L2R3)
          (Complex.I • (u : L2R3) - Complex.I • (U u : L2R3)) = 0 := by
  have h := congrArg (starRingEnd ℂ)
    (vonNeumannBoundary_pairing_closure U u x)
  have h' :
      inner ℂ (x : L2R3)
          (Complex.I • (u : L2R3) - Complex.I • (U u : L2R3)) -
        inner ℂ (H_X1_min.closure x)
          ((u : L2R3) + (U u : L2R3)) = 0 := by
    simpa only [map_sub, map_zero, inner_conj_symm] using h
  linear_combination -h'

/-- Two selected boundary vectors have zero boundary pairing.  Isometry of
`U` is exactly what cancels the two same-sign terms. -/
theorem vonNeumannBoundary_pairing_self
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (u v : TheoremFPlusSpace) :
    inner ℂ
          (Complex.I • (v : L2R3) - Complex.I • (U v : L2R3))
          ((u : L2R3) + (U u : L2R3)) -
        inner ℂ ((v : L2R3) + (U v : L2R3))
          (Complex.I • (u : L2R3) - Complex.I • (U u : L2R3)) = 0 := by
  simp only [inner_sub_left, inner_add_right, inner_add_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  have hiso :
      inner ℂ (U v : L2R3) (U u : L2R3) =
        inner ℂ (v : L2R3) (u : L2R3) := by
    exact U.inner_map_map v u
  rw [hiso]
  ring

/-- The candidate graph is isotropic for the adjoint graph pairing, hence is
contained in its submodule adjoint. -/
theorem vonNeumannExtensionGraph_le_adjoint_self
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    vonNeumannExtensionGraph U ≤ (vonNeumannExtensionGraph U).adjoint := by
  intro z hz
  rw [Submodule.mem_adjoint_iff]
  intro a b hab
  obtain ⟨x, u, rfl⟩ := (mem_vonNeumannExtensionGraph_iff U).mp hz
  obtain ⟨y, v, habEq⟩ := (mem_vonNeumannExtensionGraph_iff U).mp hab
  have haEq := congrArg Prod.fst habEq
  have hbEq := congrArg Prod.snd habEq
  simp only at haEq hbEq
  subst a
  subst b
  have hcc :
      inner ℂ (H_X1_min.closure y) (x : L2R3) -
        inner ℂ (y : L2R3) (H_X1_min.closure x) = 0 := by
    rw [H_X1_min_closure_isFormalAdjoint y x, sub_self]
  have hcb := closure_pairing_vonNeumannBoundary U y u
  have hbc := vonNeumannBoundary_pairing_closure U v x
  have hbb := vonNeumannBoundary_pairing_self U u v
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right] at *
  linear_combination hcc + hcb + hbc + hbb

/-- Any vector in the adjoint of the candidate graph already belongs to the
adjoint graph of the minimal core. -/
theorem vonNeumannExtensionGraph_adjoint_le_adjoint_graph
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    (vonNeumannExtensionGraph U).adjoint ≤ (H_X1_min†).graph := by
  intro z hz
  rw [H_X1_min.adjoint_graph_eq_graph_adjoint H_X1_min_dense_domain]
  rw [Submodule.mem_adjoint_iff] at hz ⊢
  intro a b hab
  apply hz a b
  exact (le_sup_left :
    H_X1_min.closure.graph ≤ vonNeumannExtensionGraph U)
      (LinearPMap.le_graph_of_le H_X1_min.le_closure hab)

/-- The adjoint condition on a Stage B coordinate vector forces its negative
deficiency coordinate to be the image under `U` of its positive coordinate. -/
theorem vonNeumann_adjoint_condition_forces_boundary_relation
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace)
    (x : H_X1_min.closure.domain)
    (p : TheoremFPlusSpace) (q : TheoremFMinusSpace)
    (h :
      ((x : L2R3) + (p : L2R3) + (q : L2R3),
          H_X1_min.closure x +
            Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) ∈
        (vonNeumannExtensionGraph U).adjoint) :
    q = U p := by
  have hrel : ∀ u : TheoremFPlusSpace,
      inner ℂ (U u : L2R3) (q : L2R3) =
        inner ℂ (u : L2R3) (p : L2R3) := by
    intro u
    have hraw := ((Submodule.mem_adjoint_iff _ _).mp h)
      ((u : L2R3) + (U u : L2R3))
      (Complex.I • (u : L2R3) - Complex.I • (U u : L2R3))
      ((le_sup_right :
        LinearMap.range (vonNeumannBoundaryGraphMap U) ≤
          vonNeumannExtensionGraph U) ⟨u, rfl⟩)
    have hcl := vonNeumannBoundary_pairing_closure U u x
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_I] at hraw hcl
    have hboundary :
        (2 * Complex.I) *
          (inner ℂ (U u : L2R3) (q : L2R3) -
            inner ℂ (u : L2R3) (p : L2R3)) = 0 := by
      linear_combination hraw - hcl
    have hcoef : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
    exact sub_eq_zero.mp ((mul_eq_zero.mp hboundary).resolve_left hcoef)
  let r : TheoremFPlusSpace := U.symm q
  let d : TheoremFPlusSpace := p - r
  have hdr : inner ℂ (d : L2R3) (r : L2R3) =
      inner ℂ (d : L2R3) (p : L2R3) := by
    calc
      inner ℂ (d : L2R3) (r : L2R3) =
          inner ℂ (U d : L2R3) (U r : L2R3) := by
            symm
            exact U.inner_map_map d r
      _ = inner ℂ (U d : L2R3) (q : L2R3) := by
            rw [show U r = q by simp [r]]
      _ = inner ℂ (d : L2R3) (p : L2R3) := hrel d
  have hdd : inner ℂ (d : L2R3) (d : L2R3) = 0 := by
    dsimp [d]
    rw [inner_sub_right]
    exact sub_eq_zero.mpr hdr.symm
  have hd0 : d = 0 := by
    apply Subtype.ext
    exact inner_self_eq_zero.mp hdd
  have hpr : p = r := sub_eq_zero.mp hd0
  calc
    q = U r := by simp [r]
    _ = U p := by rw [hpr]

/-- The submodule adjoint of the selected graph is exactly the selected graph. -/
theorem vonNeumannExtensionGraph_adjoint_eq
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    (vonNeumannExtensionGraph U).adjoint = vonNeumannExtensionGraph U := by
  apply le_antisymm
  · intro z hz
    have hzAdj :=
      vonNeumannExtensionGraph_adjoint_le_adjoint_graph U hz
    obtain ⟨x, p, q, hzEq⟩ :=
      mem_adjoint_graph_exists_vonNeumann_coordinates hzAdj
    have hq : q = U p := by
      apply vonNeumann_adjoint_condition_forces_boundary_relation U x p q
      rw [← hzEq]
      exact hz
    have hzEq' :
        z =
          ((x : L2R3) + (p : L2R3) + (q : L2R3),
            H_X1_min.closure x +
              Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) := by
      simpa using hzEq
    rw [hzEq', hq, mem_vonNeumannExtensionGraph_iff]
    exact ⟨x, p, rfl⟩
  · exact vonNeumannExtensionGraph_le_adjoint_self U

/-! ### Unconditional self-adjoint extension -/

/-- The operator selected by every deficiency-space isometry is
self-adjoint. -/
theorem vonNeumannExtension_isSelfAdjoint
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    IsSelfAdjoint (vonNeumannExtension U) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  calc
    ((vonNeumannExtension U)†).graph =
        (vonNeumannExtension U).graph.adjoint :=
      (vonNeumannExtension U).adjoint_graph_eq_graph_adjoint
        (vonNeumannExtension_dense_domain U)
    _ = (vonNeumannExtensionGraph U).adjoint := by
      rw [vonNeumannExtension_graph]
    _ = vonNeumannExtensionGraph U :=
      vonNeumannExtensionGraph_adjoint_eq U
    _ = (vonNeumannExtension U).graph :=
      (vonNeumannExtension_graph U).symm

/-- The unconditional self-adjoint extension witness associated to `U`, in
the public structure used by the conditional classification interface. -/
def vonNeumannSelfAdjointExtension
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    SelfAdjointExtension H_X1_min where
  op := vonNeumannExtension U
  extendsOp := H_X1_min_le_vonNeumannExtension U
  selfAdjoint := vonNeumannExtension_isSelfAdjoint U

end ExoticCCR
