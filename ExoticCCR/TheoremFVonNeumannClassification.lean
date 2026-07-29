/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFVonNeumannExtension

/-!
# Converse von Neumann boundary relation for Theorem F

This module begins the converse classification.  For an arbitrary
self-adjoint extension it extracts the exact linear boundary relation in the
two deficiency spaces and proves the corresponding exact graph formula.
-/

noncomputable section

open scoped LinearPMap

namespace ExoticCCR

/-- The full deficiency-boundary graph map
`(p,q) ↦ (p+q, i p-i q)`. -/
def vonNeumannFullBoundaryGraphMap :
    (TheoremFPlusSpace × TheoremFMinusSpace) →ₗ[ℂ] (L2R3 × L2R3) where
  toFun pq :=
    (((pq.1 : TheoremFPlusSpace) : L2R3) +
        ((pq.2 : TheoremFMinusSpace) : L2R3),
      Complex.I • (((pq.1 : TheoremFPlusSpace) : L2R3)) -
        Complex.I • (((pq.2 : TheoremFMinusSpace) : L2R3)))
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Prod.mk_add_mk]
    apply Prod.ext <;> module
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
      RingHom.id_apply, Prod.smul_mk]
    apply Prod.ext <;> module

/-- The boundary relation cut out by an arbitrary self-adjoint extension. -/
def selfAdjointExtensionBoundaryRelation
    (E : SelfAdjointExtension H_X1_min) :
    Submodule ℂ (TheoremFPlusSpace × TheoremFMinusSpace) :=
  E.op.graph.comap vonNeumannFullBoundaryGraphMap

/-- Every self-adjoint extension of the minimal core is a restriction of its
adjoint. -/
theorem selfAdjointExtension_le_adjoint
    (E : SelfAdjointExtension H_X1_min) :
    E.op ≤ H_X1_min† := by
  apply LinearPMap.le_of_le_graph
  have hEgraph :
      E.op.graph.adjoint = E.op.graph := by
    rw [← E.op.adjoint_graph_eq_graph_adjoint E.selfAdjoint.dense_domain,
      LinearPMap.isSelfAdjoint_def.mp E.selfAdjoint]
  intro z hz
  rw [H_X1_min.adjoint_graph_eq_graph_adjoint H_X1_min_dense_domain]
  rw [← hEgraph] at hz
  rw [Submodule.mem_adjoint_iff] at hz ⊢
  intro a b hab
  exact hz a b (LinearPMap.le_graph_of_le E.extendsOp hab)

/-- Every self-adjoint extension contains the closed minimal operator. -/
theorem H_X1_min_closure_le_selfAdjointExtension
    (E : SelfAdjointExtension H_X1_min) :
    H_X1_min.closure ≤ E.op := by
  refine LinearPMap.le_of_le_graph ?_
  rw [← H_X1_min_isClosable.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _
    (LinearPMap.le_graph_of_le E.extendsOp)
    E.selfAdjoint.isClosed

/-- Membership in the extracted boundary relation is exactly membership of
the corresponding deficiency-boundary vector in the extension graph. -/
theorem mem_selfAdjointExtensionBoundaryRelation_iff
    (E : SelfAdjointExtension H_X1_min)
    {p : TheoremFPlusSpace} {q : TheoremFMinusSpace} :
    (p, q) ∈ selfAdjointExtensionBoundaryRelation E ↔
      ((p : L2R3) + (q : L2R3),
          Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) ∈ E.op.graph :=
  Iff.rfl

/-- Exact Stage B graph coordinates for an arbitrary self-adjoint extension:
its graph is the closed minimal graph plus its extracted boundary relation. -/
theorem mem_selfAdjointExtension_graph_iff
    (E : SelfAdjointExtension H_X1_min) {a b : L2R3} :
    (a, b) ∈ E.op.graph ↔
      ∃ x : H_X1_min.closure.domain,
        ∃ p : TheoremFPlusSpace, ∃ q : TheoremFMinusSpace,
          (p, q) ∈ selfAdjointExtensionBoundaryRelation E ∧
          (a, b) =
            ((x : L2R3) + (p : L2R3) + (q : L2R3),
              H_X1_min.closure x +
                Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) := by
  constructor
  · intro hab
    have habAdj :
        (a, b) ∈ (H_X1_min†).graph :=
      LinearPMap.le_graph_of_le (selfAdjointExtension_le_adjoint E) hab
    obtain ⟨x, p, q, hcoord⟩ :=
      mem_adjoint_graph_exists_vonNeumann_coordinates habAdj
    have hclosure :
        ((x : L2R3), H_X1_min.closure x) ∈ E.op.graph :=
      LinearPMap.le_graph_of_le
        (H_X1_min_closure_le_selfAdjointExtension E)
        (H_X1_min.closure.mem_graph x)
    have hboundary :
        ((p : L2R3) + (q : L2R3),
          Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) ∈ E.op.graph := by
      have := E.op.graph.sub_mem hab hclosure
      rw [hcoord] at this
      have heq :
          ((p : L2R3) + (q : L2R3),
            Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) =
          ((x : L2R3) + (p : L2R3) + (q : L2R3),
              H_X1_min.closure x +
                Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) -
            ((x : L2R3), H_X1_min.closure x) := by
        apply Prod.ext <;>
          simp only [Prod.fst_sub, Prod.snd_sub] <;> module
      rw [heq]
      exact this
    exact ⟨x, p, q,
      (mem_selfAdjointExtensionBoundaryRelation_iff E).mpr hboundary,
      hcoord⟩
  · rintro ⟨x, p, q, hpq, habEq⟩
    have haEq := congrArg Prod.fst habEq
    have hbEq := congrArg Prod.snd habEq
    simp only at haEq hbEq
    subst a
    subst b
    have hclosure :
        ((x : L2R3), H_X1_min.closure x) ∈ E.op.graph :=
      LinearPMap.le_graph_of_le
        (H_X1_min_closure_le_selfAdjointExtension E)
        (H_X1_min.closure.mem_graph x)
    have hboundary :
        ((p : L2R3) + (q : L2R3),
          Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) ∈ E.op.graph :=
      (mem_selfAdjointExtensionBoundaryRelation_iff E).mp hpq
    have hsum := E.op.graph.add_mem hclosure hboundary
    have heq :
        ((x : L2R3) + (p : L2R3) + (q : L2R3),
          H_X1_min.closure x +
            Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) =
        ((x : L2R3), H_X1_min.closure x) +
          ((p : L2R3) + (q : L2R3),
            Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) := by
      apply Prod.ext <;>
        simp only [Prod.fst_add, Prod.snd_add] <;> module
    rw [heq]
    exact hsum

/-! ### Neutrality and maximality of the boundary relation -/

/-- The Hermitian boundary form on the two deficiency coordinates. -/
def vonNeumannBoundaryPairing
    (r : TheoremFPlusSpace) (s : TheoremFMinusSpace)
    (p : TheoremFPlusSpace) (q : TheoremFMinusSpace) : ℂ :=
  inner ℂ (s : L2R3) (q : L2R3) -
    inner ℂ (r : L2R3) (p : L2R3)

/-- The graph-adjoint pairing of two pure boundary vectors is `2i` times the
deficiency-space boundary form. -/
theorem fullBoundary_graph_pairing
    (r : TheoremFPlusSpace) (s : TheoremFMinusSpace)
    (p : TheoremFPlusSpace) (q : TheoremFMinusSpace) :
    inner ℂ
          (Complex.I • (r : L2R3) - Complex.I • (s : L2R3))
          ((p : L2R3) + (q : L2R3)) -
        inner ℂ ((r : L2R3) + (s : L2R3))
          (Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) =
      (2 * Complex.I) * vonNeumannBoundaryPairing r s p q := by
  simp only [vonNeumannBoundaryPairing, inner_sub_left, inner_add_right,
    inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I]
  ring

/-- A pure boundary vector pairs trivially with the closed minimal graph. -/
theorem fullBoundary_pairing_closure
    (p : TheoremFPlusSpace) (q : TheoremFMinusSpace)
    (x : H_X1_min.closure.domain) :
    inner ℂ
          (Complex.I • (p : L2R3) - Complex.I • (q : L2R3))
          (x : L2R3) -
        inner ℂ ((p : L2R3) + (q : L2R3))
          (H_X1_min.closure x) = 0 := by
  obtain ⟨hpDom, hpEq⟩ := mem_adjointEigenspace_iff.mp p.property
  obtain ⟨hqDom, hqEq⟩ := mem_adjointEigenspace_iff.mp q.property
  have hp :
      inner ℂ (Complex.I • (p : L2R3)) (x : L2R3) =
        inner ℂ (p : L2R3) (H_X1_min.closure x) := by
    simpa only [hpEq, Subtype.coe_eta] using
      H_X1_min_adjoint_isFormalAdjoint_closure
        ⟨(p : L2R3), hpDom⟩ x
  have hq :
      -inner ℂ (Complex.I • (q : L2R3)) (x : L2R3) =
        inner ℂ (q : L2R3) (H_X1_min.closure x) := by
    have hq' := H_X1_min_adjoint_isFormalAdjoint_closure
      ⟨(q : L2R3), hqDom⟩ x
    rw [hqEq] at hq'
    simpa only [neg_smul, inner_neg_left, Subtype.coe_eta] using hq'
  rw [inner_sub_left, inner_add_left]
  linear_combination hp + hq

/-- The boundary relation of a self-adjoint extension is neutral. -/
theorem selfAdjointExtensionBoundaryRelation_neutral
    (E : SelfAdjointExtension H_X1_min)
    {r p : TheoremFPlusSpace} {s q : TheoremFMinusSpace}
    (hrs : (r, s) ∈ selfAdjointExtensionBoundaryRelation E)
    (hpq : (p, q) ∈ selfAdjointExtensionBoundaryRelation E) :
    vonNeumannBoundaryPairing r s p q = 0 := by
  have hrsGraph :=
    (mem_selfAdjointExtensionBoundaryRelation_iff E).mp hrs
  have hpqGraph :=
    (mem_selfAdjointExtensionBoundaryRelation_iff E).mp hpq
  have hformal : E.op.IsFormalAdjoint E.op := by
    have hf := E.op.adjoint_isFormalAdjoint E.selfAdjoint.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp E.selfAdjoint] at hf
    exact hf
  obtain ⟨rs, hrsDom, hrsApply⟩ := E.op.mem_graph_iff.mp hrsGraph
  obtain ⟨pq, hpqDom, hpqApply⟩ := E.op.mem_graph_iff.mp hpqGraph
  simp only at hrsDom hrsApply hpqDom hpqApply
  have hzero :
      inner ℂ
          (Complex.I • (r : L2R3) - Complex.I • (s : L2R3))
          ((p : L2R3) + (q : L2R3)) -
        inner ℂ ((r : L2R3) + (s : L2R3))
          (Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) = 0 := by
    rw [← hrsApply, ← hpqDom, ← hrsDom, ← hpqApply,
      hformal rs pq, sub_self]
  rw [fullBoundary_graph_pairing] at hzero
  have hcoef : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hzero).resolve_left hcoef

/-- Maximality: every boundary pair orthogonal to the extracted relation for
the boundary form already belongs to that relation. -/
theorem selfAdjointExtensionBoundaryRelation_maximal
    (E : SelfAdjointExtension H_X1_min)
    (p : TheoremFPlusSpace) (q : TheoremFMinusSpace)
    (horth : ∀ r : TheoremFPlusSpace, ∀ s : TheoremFMinusSpace,
      (r, s) ∈ selfAdjointExtensionBoundaryRelation E →
        vonNeumannBoundaryPairing r s p q = 0) :
    (p, q) ∈ selfAdjointExtensionBoundaryRelation E := by
  rw [mem_selfAdjointExtensionBoundaryRelation_iff]
  have hAdj :
      ((p : L2R3) + (q : L2R3),
        Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) ∈
        E.op.graph.adjoint := by
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    obtain ⟨x, r, s, hrs, habEq⟩ :=
      (mem_selfAdjointExtension_graph_iff E).mp hab
    have haEq := congrArg Prod.fst habEq
    have hbEq := congrArg Prod.snd habEq
    simp only at haEq hbEq
    subst a
    subst b
    have hcl := fullBoundary_pairing_closure p q x
    have hbd := fullBoundary_graph_pairing r s p q
    rw [horth r s hrs] at hbd
    simp only [mul_zero] at hbd
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right] at *
    have hclStar := congrArg (starRingEnd ℂ) hcl
    simp only [map_sub, map_add, map_zero, inner_conj_symm] at hclStar
    have hclRev :
        inner ℂ (H_X1_min.closure x)
              ((p : L2R3) + (q : L2R3)) -
            inner ℂ (x : L2R3)
              (Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) = 0 := by
      simp only [inner_add_right, inner_sub_right]
      linear_combination -hclStar
    simp only [inner_add_right, inner_sub_right] at hclRev
    linear_combination hclRev + hbd
  rw [← E.op.adjoint_graph_eq_graph_adjoint E.selfAdjoint.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp E.selfAdjoint] at hAdj
  exact hAdj

/-! ### The induced densely defined boundary isometry -/

/-- Neutrality gives equality of the two deficiency-coordinate norms. -/
theorem norm_eq_of_mem_selfAdjointExtensionBoundaryRelation
    (E : SelfAdjointExtension H_X1_min)
    {p : TheoremFPlusSpace} {q : TheoremFMinusSpace}
    (hpq : (p, q) ∈ selfAdjointExtensionBoundaryRelation E) :
    ‖p‖ = ‖q‖ := by
  have h :=
    selfAdjointExtensionBoundaryRelation_neutral E hpq hpq
  change inner ℂ (q : L2R3) (q : L2R3) -
    inner ℂ (p : L2R3) (p : L2R3) = 0 at h
  have heq := sub_eq_zero.mp h
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at heq
  have hre : ‖q‖ ^ 2 = ‖p‖ ^ 2 := by
    exact_mod_cast heq
  nlinarith [norm_nonneg p, norm_nonneg q]

/-- The boundary relation is functional over its positive coordinate. -/
theorem selfAdjointExtensionBoundaryRelation_functional
    (E : SelfAdjointExtension H_X1_min) :
    ∀ z : TheoremFPlusSpace × TheoremFMinusSpace,
      z ∈ selfAdjointExtensionBoundaryRelation E →
        z.fst = 0 → z.snd = 0 := by
  intro z hz hz0
  have hn := norm_eq_of_mem_selfAdjointExtensionBoundaryRelation E hz
  rw [hz0, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- The partial linear isometry encoded by an arbitrary self-adjoint
extension's boundary relation. -/
def selfAdjointExtensionBoundaryPMap
    (E : SelfAdjointExtension H_X1_min) :
    TheoremFPlusSpace →ₗ.[ℂ] TheoremFMinusSpace :=
  (selfAdjointExtensionBoundaryRelation E).toLinearPMap

/-- The graph of the induced partial map is exactly the extracted relation. -/
theorem selfAdjointExtensionBoundaryPMap_graph
    (E : SelfAdjointExtension H_X1_min) :
    (selfAdjointExtensionBoundaryPMap E).graph =
      selfAdjointExtensionBoundaryRelation E :=
  Submodule.toLinearPMap_graph_eq _
    (selfAdjointExtensionBoundaryRelation_functional E)

/-- The induced boundary partial map preserves norms on its domain. -/
theorem selfAdjointExtensionBoundaryPMap_norm
    (E : SelfAdjointExtension H_X1_min)
    (p : (selfAdjointExtensionBoundaryPMap E).domain) :
    ‖selfAdjointExtensionBoundaryPMap E p‖ = ‖p‖ := by
  have hpq :
      ((p : TheoremFPlusSpace), selfAdjointExtensionBoundaryPMap E p) ∈
        selfAdjointExtensionBoundaryRelation E := by
    rw [← selfAdjointExtensionBoundaryPMap_graph]
    exact (selfAdjointExtensionBoundaryPMap E).mem_graph p
  exact (norm_eq_of_mem_selfAdjointExtensionBoundaryRelation E hpq).symm

/-- Maximality forces the positive-coordinate domain of the induced partial
isometry to be dense. -/
theorem selfAdjointExtensionBoundaryPMap_dense_domain
    (E : SelfAdjointExtension H_X1_min) :
    Dense ((selfAdjointExtensionBoundaryPMap E).domain :
      Set TheoremFPlusSpace) := by
  letI : IsClosed (TheoremFPlusSpace : Set L2R3) :=
    adjointEigenspace_isClosed H_X1_min H_X1_min_dense_domain Complex.I
  letI : CompleteSpace TheoremFPlusSpace :=
    IsClosed.completeSpace_coe
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  have huRel :
      (u, (0 : TheoremFMinusSpace)) ∈
        selfAdjointExtensionBoundaryRelation E := by
    apply selfAdjointExtensionBoundaryRelation_maximal E
    intro r s hrs
    have hrDom :
        r ∈ (selfAdjointExtensionBoundaryPMap E).domain := by
      rw [← LinearPMap.graph_map_fst_eq_domain,
        selfAdjointExtensionBoundaryPMap_graph]
      exact ⟨(r, s), hrs, rfl⟩
    have hinnerUR : inner ℂ u (r : TheoremFPlusSpace) = 0 :=
      (Submodule.mem_orthogonal' _ _).mp hu r hrDom
    change inner ℂ (u : L2R3) (r : L2R3) = 0 at hinnerUR
    have hinner : inner ℂ (r : L2R3) (u : L2R3) = 0 := by
      have hs := congrArg (starRingEnd ℂ) hinnerUR
      simpa only [map_zero, inner_conj_symm] using hs
    change inner ℂ (s : L2R3) (0 : L2R3) -
      inner ℂ (r : L2R3) (u : L2R3) = 0
    rw [inner_zero_right, hinner, sub_zero]
  have hn := norm_eq_of_mem_selfAdjointExtensionBoundaryRelation E huRel
  rw [norm_zero] at hn
  exact norm_eq_zero.mp hn


end ExoticCCR
