/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFVonNeumannExtension
import Mathlib.Analysis.Normed.Operator.Extend

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

/-! ### Completion to a total boundary isometry -/

/-- The extracted boundary relation is closed.  This is the point where
closedness of the arbitrary self-adjoint extension enters the converse
classification. -/
theorem selfAdjointExtensionBoundaryRelation_isClosed
    (E : SelfAdjointExtension H_X1_min) :
    IsClosed (selfAdjointExtensionBoundaryRelation E :
      Set (TheoremFPlusSpace × TheoremFMinusSpace)) := by
  exact E.selfAdjoint.isClosed.preimage (by
    change Continuous fun pq : TheoremFPlusSpace × TheoremFMinusSpace =>
      (((pq.1 : TheoremFPlusSpace) : L2R3) +
          ((pq.2 : TheoremFMinusSpace) : L2R3),
        Complex.I • (((pq.1 : TheoremFPlusSpace) : L2R3)) -
          Complex.I • (((pq.2 : TheoremFMinusSpace) : L2R3)))
    fun_prop)

/-- The continuous linear extension of the densely defined boundary
isometry. -/
noncomputable def selfAdjointExtensionBoundaryCLM
    (E : SelfAdjointExtension H_X1_min) :
    TheoremFPlusSpace →L[ℂ] TheoremFMinusSpace := by
  letI : IsClosed (TheoremFMinusSpace : Set L2R3) :=
    adjointEigenspace_isClosed H_X1_min H_X1_min_dense_domain (-Complex.I)
  letI : CompleteSpace TheoremFMinusSpace :=
    IsClosed.completeSpace_coe
  exact (selfAdjointExtensionBoundaryPMap E).toFun.extendOfNorm
    (selfAdjointExtensionBoundaryPMap E).domain.subtypeₗᵢ

/-- The total extension agrees with the partial boundary map on its dense
domain. -/
theorem selfAdjointExtensionBoundaryCLM_apply_domain
    (E : SelfAdjointExtension H_X1_min)
    (p : (selfAdjointExtensionBoundaryPMap E).domain) :
    selfAdjointExtensionBoundaryCLM E (p : TheoremFPlusSpace) =
      selfAdjointExtensionBoundaryPMap E p := by
  letI : IsClosed (TheoremFMinusSpace : Set L2R3) :=
    adjointEigenspace_isClosed H_X1_min H_X1_min_dense_domain (-Complex.I)
  letI : CompleteSpace TheoremFMinusSpace :=
    IsClosed.completeSpace_coe
  apply LinearMap.extendOfNorm_eq
  · simpa using
      (selfAdjointExtensionBoundaryPMap_dense_domain E).denseRange_val
  · refine ⟨1, ?_⟩
    intro x
    change ‖selfAdjointExtensionBoundaryPMap E x‖ ≤
      1 * ‖(x : TheoremFPlusSpace)‖
    rw [selfAdjointExtensionBoundaryPMap_norm]
    simp

/-- The continuous extension remains an isometry on the whole positive
deficiency space. -/
theorem selfAdjointExtensionBoundaryCLM_norm
    (E : SelfAdjointExtension H_X1_min)
    (p : TheoremFPlusSpace) :
    ‖selfAdjointExtensionBoundaryCLM E p‖ = ‖p‖ :=
  Dense.induction (selfAdjointExtensionBoundaryPMap_dense_domain E)
    (fun x hx => by
      let x' : (selfAdjointExtensionBoundaryPMap E).domain := ⟨x, hx⟩
      have hext :
          selfAdjointExtensionBoundaryCLM E x =
            selfAdjointExtensionBoundaryPMap E x' := by
        exact selfAdjointExtensionBoundaryCLM_apply_domain E x'
      rw [hext, selfAdjointExtensionBoundaryPMap_norm]
      rfl)
    (isClosed_eq (continuous_norm.comp
      (selfAdjointExtensionBoundaryCLM E).continuous) continuous_norm)
    p

/-- The total isometric embedding obtained by completion of the partial
boundary map. -/
noncomputable def selfAdjointExtensionBoundaryIsometry
    (E : SelfAdjointExtension H_X1_min) :
    TheoremFPlusSpace →ₗᵢ[ℂ] TheoremFMinusSpace where
  __ := (selfAdjointExtensionBoundaryCLM E).toLinearMap
  norm_map' := selfAdjointExtensionBoundaryCLM_norm E

/-- Every graph point of the completed isometry remains in the extracted
closed boundary relation. -/
theorem selfAdjointExtensionBoundaryIsometry_mem_relation
    (E : SelfAdjointExtension H_X1_min)
    (p : TheoremFPlusSpace) :
    (p, selfAdjointExtensionBoundaryIsometry E p) ∈
      selfAdjointExtensionBoundaryRelation E :=
  Dense.induction (selfAdjointExtensionBoundaryPMap_dense_domain E)
    (fun x hx => by
      let x' : (selfAdjointExtensionBoundaryPMap E).domain := ⟨x, hx⟩
      rw [show selfAdjointExtensionBoundaryIsometry E x =
          selfAdjointExtensionBoundaryPMap E x' by
        exact selfAdjointExtensionBoundaryCLM_apply_domain E x']
      rw [← selfAdjointExtensionBoundaryPMap_graph]
      exact (selfAdjointExtensionBoundaryPMap E).mem_graph x')
    ((selfAdjointExtensionBoundaryRelation_isClosed E).preimage (by
      change Continuous fun p : TheoremFPlusSpace =>
        (p, selfAdjointExtensionBoundaryIsometry E p)
      fun_prop))
    p

/-- The extracted boundary relation is exactly the graph of the completed
isometry. -/
theorem mem_selfAdjointExtensionBoundaryRelation_iff_isometry
    (E : SelfAdjointExtension H_X1_min)
    {p : TheoremFPlusSpace} {q : TheoremFMinusSpace} :
    (p, q) ∈ selfAdjointExtensionBoundaryRelation E ↔
      q = selfAdjointExtensionBoundaryIsometry E p := by
  constructor
  · intro hpq
    have hdiff :
        (0, q - selfAdjointExtensionBoundaryIsometry E p) ∈
          selfAdjointExtensionBoundaryRelation E := by
      simpa using (selfAdjointExtensionBoundaryRelation E).sub_mem hpq
        (selfAdjointExtensionBoundaryIsometry_mem_relation E p)
    exact sub_eq_zero.mp
      (selfAdjointExtensionBoundaryRelation_functional E
        (0, q - selfAdjointExtensionBoundaryIsometry E p) hdiff rfl)
  · intro hq
    rw [hq]
    exact selfAdjointExtensionBoundaryIsometry_mem_relation E p

/-- The completed boundary isometry has dense range.  Maximal neutrality
rules out a nonzero vector orthogonal to its range. -/
theorem selfAdjointExtensionBoundaryIsometry_denseRange
    (E : SelfAdjointExtension H_X1_min) :
    DenseRange (selfAdjointExtensionBoundaryIsometry E) := by
  letI : IsClosed (TheoremFMinusSpace : Set L2R3) :=
    adjointEigenspace_isClosed H_X1_min H_X1_min_dense_domain (-Complex.I)
  letI : CompleteSpace TheoremFMinusSpace :=
    IsClosed.completeSpace_coe
  change Dense ((LinearMap.range
    (selfAdjointExtensionBoundaryIsometry E).toLinearMap :
      Submodule ℂ TheoremFMinusSpace) : Set TheoremFMinusSpace)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro q hq
  have hzeroRel :
      ((0 : TheoremFPlusSpace), q) ∈
        selfAdjointExtensionBoundaryRelation E := by
    apply selfAdjointExtensionBoundaryRelation_maximal E
    intro r s hrs
    have hs : s = selfAdjointExtensionBoundaryIsometry E r :=
      (mem_selfAdjointExtensionBoundaryRelation_iff_isometry E).mp hrs
    have hinner :
        inner ℂ (selfAdjointExtensionBoundaryIsometry E r) q = 0 := by
      have hqr := (Submodule.mem_orthogonal' _ _).mp hq
        (selfAdjointExtensionBoundaryIsometry E r)
        ⟨r, rfl⟩
      have hstar := congrArg (starRingEnd ℂ) hqr
      simpa only [map_zero, inner_conj_symm] using hstar
    change inner ℂ (s : L2R3) (q : L2R3) -
      inner ℂ (r : L2R3) (0 : L2R3) = 0
    rw [inner_zero_right, sub_zero, hs]
    exact hinner
  have hn := norm_eq_of_mem_selfAdjointExtensionBoundaryRelation E hzeroRel
  rw [norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- Maximality upgrades the completed isometric embedding to a surjective
linear isometry equivalence. -/
noncomputable def selfAdjointExtensionBoundaryEquiv
    (E : SelfAdjointExtension H_X1_min) :
    TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace := by
  let U := selfAdjointExtensionBoundaryIsometry E
  have hsurj : Function.Surjective U := by
    letI : IsClosed (TheoremFPlusSpace : Set L2R3) :=
      adjointEigenspace_isClosed H_X1_min H_X1_min_dense_domain Complex.I
    letI : CompleteSpace TheoremFPlusSpace :=
      IsClosed.completeSpace_coe
    have hclosed : IsClosed (Set.range U) :=
      U.isometry.isUniformInducing.isComplete_range.isClosed
    intro q
    have hq : q ∈ closure (Set.range U) :=
      selfAdjointExtensionBoundaryIsometry_denseRange E q
    rw [hclosed.closure_eq] at hq
    exact hq
  exact LinearIsometryEquiv.ofSurjective U hsurj

/-- The graph of the recovered equivalence is the original boundary
relation. -/
theorem mem_selfAdjointExtensionBoundaryRelation_iff_equiv
    (E : SelfAdjointExtension H_X1_min)
    {p : TheoremFPlusSpace} {q : TheoremFMinusSpace} :
    (p, q) ∈ selfAdjointExtensionBoundaryRelation E ↔
      q = selfAdjointExtensionBoundaryEquiv E p := by
  rw [mem_selfAdjointExtensionBoundaryRelation_iff_isometry]
  rfl

/-! ### Converse classification -/

/-- Self-adjoint extension witnesses are determined by their operator
field; the remaining fields are propositions. -/
theorem SelfAdjointExtension.ext_op
    {E F : SelfAdjointExtension H_X1_min} (h : E.op = F.op) :
    E = F := by
  cases E with
  | mk opE extendsE selfAdjointE =>
      cases F with
      | mk opF extendsF selfAdjointF =>
          simp only at h
          cases h
          rfl

/-- The graph of an arbitrary self-adjoint extension is the von Neumann
graph selected by its recovered boundary equivalence. -/
theorem selfAdjointExtension_graph_eq_vonNeumannExtensionGraph
    (E : SelfAdjointExtension H_X1_min) :
    E.op.graph =
      vonNeumannExtensionGraph (selfAdjointExtensionBoundaryEquiv E) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, p, q, hpq, hzEq⟩ :=
      (mem_selfAdjointExtension_graph_iff E).mp hz
    have hzEq' :
        z =
          ((x : L2R3) + (p : L2R3) + (q : L2R3),
            H_X1_min.closure x +
              Complex.I • (p : L2R3) - Complex.I • (q : L2R3)) := by
      simpa using hzEq
    rw [hzEq']
    have hq : q = selfAdjointExtensionBoundaryEquiv E p :=
      (mem_selfAdjointExtensionBoundaryRelation_iff_equiv E).mp hpq
    rw [hq, mem_vonNeumannExtensionGraph_iff]
    exact ⟨x, p, rfl⟩
  · intro hz
    obtain ⟨x, p, rfl⟩ :=
      (mem_vonNeumannExtensionGraph_iff
        (selfAdjointExtensionBoundaryEquiv E)).mp hz
    rw [mem_selfAdjointExtension_graph_iff]
    exact ⟨x, p, selfAdjointExtensionBoundaryEquiv E p,
      (mem_selfAdjointExtensionBoundaryRelation_iff_equiv E).mpr rfl, rfl⟩

/-- Every arbitrary self-adjoint extension is recovered exactly from its
boundary equivalence. -/
theorem selfAdjointExtension_eq_vonNeumannSelfAdjointExtension
    (E : SelfAdjointExtension H_X1_min) :
    E = vonNeumannSelfAdjointExtension
      (selfAdjointExtensionBoundaryEquiv E) := by
  let F := vonNeumannSelfAdjointExtension
    (selfAdjointExtensionBoundaryEquiv E)
  change E = F
  have hop : E.op = F.op := by
    change E.op =
      vonNeumannExtension (selfAdjointExtensionBoundaryEquiv E)
    apply LinearPMap.eq_of_eq_graph
    rw [selfAdjointExtension_graph_eq_vonNeumannExtensionGraph,
      vonNeumannExtension_graph]
  exact SelfAdjointExtension.ext_op hop

/-- The recovered boundary equivalence of the extension constructed from
`U` is exactly `U`. -/
theorem selfAdjointExtensionBoundaryEquiv_vonNeumannSelfAdjointExtension
    (U : TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) :
    selfAdjointExtensionBoundaryEquiv
      (vonNeumannSelfAdjointExtension U) = U := by
  apply LinearIsometryEquiv.ext
  intro p
  have hpRel :
      (p, U p) ∈ selfAdjointExtensionBoundaryRelation
        (vonNeumannSelfAdjointExtension U) := by
    rw [mem_selfAdjointExtensionBoundaryRelation_iff]
    change
      ((p : L2R3) + (U p : L2R3),
        Complex.I • (p : L2R3) - Complex.I • (U p : L2R3)) ∈
          (vonNeumannExtension U).graph
    rw [vonNeumannExtension_graph, mem_vonNeumannExtensionGraph_iff]
    refine ⟨0, p, ?_⟩
    simp
  exact ((mem_selfAdjointExtensionBoundaryRelation_iff_equiv
    (vonNeumannSelfAdjointExtension U)).mp hpRel).symm

/-- The unconditional von Neumann classification for the verified Theorem F
minimal operator. -/
noncomputable def theoremFVonNeumannClassification :
    SelfAdjointExtension H_X1_min ≃
      (TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) where
  toFun := selfAdjointExtensionBoundaryEquiv
  invFun := vonNeumannSelfAdjointExtension
  left_inv := fun E =>
    (selfAdjointExtension_eq_vonNeumannSelfAdjointExtension E).symm
  right_inv :=
    selfAdjointExtensionBoundaryEquiv_vonNeumannSelfAdjointExtension

/-- The formerly conditional classification interface is inhabited
unconditionally. -/
noncomputable def theoremFClassificationHypothesis :
    TheoremFClassificationHypothesis where
  classification := theoremFVonNeumannClassification

/-- The construction of von Neumann self-adjoint extensions is injective. -/
theorem vonNeumannSelfAdjointExtension_injective :
    Function.Injective
      (vonNeumannSelfAdjointExtension :
        (TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace) →
          SelfAdjointExtension H_X1_min) :=
  theoremFVonNeumannClassification.symm.injective

/-! ### Unconditional multiplicity -/

/-- Sign transport carries each adjoint eigenspace onto the eigenspace at
the opposite eigenvalue. -/
theorem sigmaL2_mem_adjointEigenspace_neg
    {z : ℂ} {u : L2R3}
    (hu : u ∈ adjointEigenspace H_X1_min z) :
    sigmaL2 u ∈ adjointEigenspace H_X1_min (-z) := by
  rw [← weakAdjointEigenspace_eq_adjointEigenspace H_X1_min
    H_X1_min_dense_domain (-z)]
  apply weakAdjointEigenvector_sigmaL2
  change u ∈ weakAdjointEigenspace H_X1_min z
  rw [weakAdjointEigenspace_eq_adjointEigenspace H_X1_min
    H_X1_min_dense_domain z]
  exact hu

/-- The sign involution gives an explicit linear isometry equivalence
between the two deficiency spaces. -/
noncomputable def theoremFDeficiencySigmaEquiv :
    TheoremFPlusSpace ≃ₗᵢ[ℂ] TheoremFMinusSpace where
  toFun p :=
    ⟨sigmaL2 (p : L2R3), by
      simpa using sigmaL2_mem_adjointEigenspace_neg p.property⟩
  invFun q :=
    ⟨sigmaL2 (q : L2R3), by
      have h := sigmaL2_mem_adjointEigenspace_neg q.property
      simpa using h⟩
  left_inv p := by
    apply Subtype.ext
    exact sigmaL2_sigmaL2 p
  right_inv q := by
    apply Subtype.ext
    exact sigmaL2_sigmaL2 q
  map_add' p r := by
    apply Subtype.ext
    exact sigmaL2.map_add p r
  map_smul' c p := by
    apply Subtype.ext
    exact sigmaL2.map_smul c p
  norm_map' p := by
    change ‖sigmaL2 (p : L2R3)‖ = ‖(p : L2R3)‖
    exact MeasureTheory.Lp.norm_compMeasurePreserving _
      measurePreserving_sigmaMap

/-- The positive deficiency space is nontrivial. -/
theorem theoremFPlusSpace_nontrivial :
    Nontrivial TheoremFPlusSpace := by
  obtain ⟨u, huLI, huEig⟩ :=
    exists_finite_weakAdjointEigenvector_posI_family 1
  let p : TheoremFPlusSpace :=
    ⟨u 0, by
      change u 0 ∈ adjointEigenspace H_X1_min Complex.I
      rw [← weakAdjointEigenspace_eq_adjointEigenspace H_X1_min
        H_X1_min_dense_domain Complex.I]
      exact huEig 0⟩
  have hp : p ≠ 0 := by
    intro hp0
    have hu0 : u 0 = 0 := congrArg Subtype.val hp0
    exact huLI.ne_zero 0 hu0
  exact ⟨⟨p, 0, hp⟩⟩

/-- The verified Theorem F operator has at least two distinct self-adjoint
extensions, with no remaining classification hypothesis. -/
theorem theoremF_exists_two_distinct_selfAdjointExtensions :
    ∃ A B : SelfAdjointExtension H_X1_min, A ≠ B := by
  letI : Nontrivial TheoremFPlusSpace := theoremFPlusSpace_nontrivial
  exact theoremF_exists_two_distinct_extensions_of_classification
    theoremFClassificationHypothesis theoremFDeficiencySigmaEquiv


end ExoticCCR
