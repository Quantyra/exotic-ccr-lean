/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFSymmetricCore
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Graph-space foundations for the von Neumann layer of Theorem F

This module is the graph-space foundation layer for the unconditional von
Neumann classification program for the canonical minimal transport core
`H_X1_min = -i X1`.  It records:

* closability of `H_X1_min` and the containment of its closure in its adjoint,
  both derived from the proved formal symmetry;
* the `L²`-product graph space `WithLp 2 (L2R3 × L2R3)` together with the
  graph submodules of the minimal core and of its adjoint, and the deficiency
  lines `(u, z • u)` cut out by the adjoint eigenspaces;
* the graph-space orthogonality relations between the two deficiency lines and
  between the (closure of the) minimal graph and each deficiency line;
* the bridge identifying the topological closure of the minimal graph with the
  graph of the operator closure.

It contains no extension-classification assertion.
-/

noncomputable section

open scoped LinearPMap

namespace ExoticCCR

/-! ### Closability of the minimal core -/

/-- The canonical minimal transport core of `X1` has dense domain. -/
theorem H_X1_min_dense_domain : Dense (H_X1_min.domain : Set L2R3) :=
  minimalTransportCore_dense_domain X1 contDiff_X1.continuous

/-- The formally symmetric minimal core is contained in its adjoint. -/
theorem H_X1_min_le_adjoint : H_X1_min ≤ H_X1_min† :=
  H_X1_min_isFormalAdjoint_H_X1_min.le_adjoint H_X1_min_dense_domain

/-- The canonical minimal transport core is closable: it is contained in its
adjoint, which is a closed operator. -/
theorem H_X1_min_isClosable : H_X1_min.IsClosable :=
  (LinearPMap.adjoint_isClosed H_X1_min_dense_domain).isClosable.leIsClosable
    H_X1_min_le_adjoint

/-- The closure of the minimal core is still contained in the adjoint: the
closure is the least closed extension and the adjoint is a closed extension. -/
theorem H_X1_min_closure_le_adjoint : H_X1_min.closure ≤ H_X1_min† := by
  refine LinearPMap.le_of_le_graph ?_
  rw [← H_X1_min_isClosable.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _
    (LinearPMap.le_graph_of_le H_X1_min_le_adjoint)
    (LinearPMap.adjoint_isClosed H_X1_min_dense_domain)

/-! ### The `L²` graph space -/

/-- The ambient graph space: the product `L2R3 × L2R3` carrying the `L²`
(inner-product) norm. -/
abbrev GraphSpace := WithLp 2 (L2R3 × L2R3)

/-- The canonical continuous linear identification of the plain product with
the graph space. -/
def toGraphSpace : (L2R3 × L2R3) ≃L[ℂ] GraphSpace :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ L2R3 L2R3).symm

/-- The identification acts as the `WithLp` cast. -/
theorem toGraphSpace_apply (a : L2R3 × L2R3) :
    toGraphSpace a = WithLp.toLp 2 a := rfl

/-- The inverse identification acts as the `WithLp` forgetful cast. -/
theorem toGraphSpace_symm_apply (x : GraphSpace) :
    toGraphSpace.symm x = WithLp.ofLp x := rfl

/-- The graph-space inner product is the sum of the componentwise inner
products. -/
theorem toGraphSpace_inner (a₁ a₂ b₁ b₂ : L2R3) :
    inner ℂ (toGraphSpace (a₁, a₂)) (toGraphSpace (b₁, b₂)) =
      inner ℂ a₁ b₁ + inner ℂ a₂ b₂ := rfl

/-! ### Graph submodules -/

/-- The graph of an unbounded operator, realized as a submodule of the `L²`
graph space via the canonical identification. -/
def graphL2 (H : L2R3 →ₗ.[ℂ] L2R3) : Submodule ℂ GraphSpace :=
  H.graph.comap
    (WithLp.linearEquiv 2 ℂ (L2R3 × L2R3) : GraphSpace →ₗ[ℂ] L2R3 × L2R3)

/-- Membership in a realized graph, in terms of the underlying product. -/
theorem mem_graphL2_iff (H : L2R3 →ₗ.[ℂ] L2R3) {x : GraphSpace} :
    x ∈ graphL2 H ↔ WithLp.ofLp x ∈ H.graph := Iff.rfl

/-- Membership in a realized graph, in terms of a domain element. -/
theorem mem_graphL2_iff_exists (H : L2R3 →ₗ.[ℂ] L2R3) {x : GraphSpace} :
    x ∈ graphL2 H ↔ ∃ φ : H.domain, x = toGraphSpace (↑φ, H φ) := by
  rw [mem_graphL2_iff, LinearPMap.mem_graph_iff']
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    rw [hφ]
    exact rfl
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, rfl⟩

/-- The realized graph as a set is the continuous preimage of the plain graph
under the inverse identification. -/
theorem graphL2_coe (H : L2R3 →ₗ.[ℂ] L2R3) :
    (graphL2 H : Set GraphSpace) =
      ⇑toGraphSpace.symm ⁻¹' (H.graph : Set (L2R3 × L2R3)) := rfl

/-- The realized graph is also the image of the plain graph under the forward
identification. -/
theorem graphL2_eq_map (H : L2R3 →ₗ.[ℂ] L2R3) :
    graphL2 H = H.graph.map
      (toGraphSpace.toLinearEquiv : (L2R3 × L2R3) →ₗ[ℂ] GraphSpace) := by
  ext x
  rw [Submodule.mem_map_equiv, mem_graphL2_iff]
  exact Iff.rfl

/-- A closed plain graph realizes to a closed graph submodule. -/
theorem graphL2_isClosed {H : L2R3 →ₗ.[ℂ] L2R3}
    (h : IsClosed (H.graph : Set (L2R3 × L2R3))) :
    IsClosed (graphL2 H : Set GraphSpace) := by
  rw [graphL2_coe]
  exact h.preimage toGraphSpace.symm.continuous

/-- The graph-space realization of the graph of the adjoint of the minimal
core. -/
abbrev adjointGraphL2 : Submodule ℂ GraphSpace := graphL2 (H_X1_min†)

/-- The graph-space realization of the graph of the minimal core itself.  No
closedness is asserted for this submodule. -/
abbrev minimalGraphL2 : Submodule ℂ GraphSpace := graphL2 H_X1_min

/-- The realized adjoint graph is closed. -/
theorem adjointGraphL2_isClosed : IsClosed (adjointGraphL2 : Set GraphSpace) :=
  graphL2_isClosed (LinearPMap.adjoint_isClosed H_X1_min_dense_domain)

/-! ### Deficiency lines -/

/-- The continuous defect map `x ↦ x₂ - z • x₁` on the graph space; its kernel
cuts out the graph line `v = z • u`. -/
def deficiencyDefect (z : ℂ) : GraphSpace →L[ℂ] L2R3 :=
  WithLp.sndL 2 ℂ L2R3 L2R3 - z • WithLp.fstL 2 ℂ L2R3 L2R3

/-- Evaluation of the defect map on an identified pair. -/
theorem deficiencyDefect_toGraphSpace (z : ℂ) (a b : L2R3) :
    deficiencyDefect z (toGraphSpace (a, b)) = b - z • a := rfl

/-- The deficiency line at `z`: the part of the realized adjoint graph lying
on the graph line `v = z • u`.  At `z = ±i` these are the two deficiency
subspaces of the minimal core, viewed inside the graph space. -/
def deficiencyLine (z : ℂ) : Submodule ℂ GraphSpace :=
  adjointGraphL2 ⊓ LinearMap.ker (deficiencyDefect z : GraphSpace →ₗ[ℂ] L2R3)

/-- The deficiency line unfolds to its defining intersection. -/
theorem deficiencyLine_eq_inf (z : ℂ) :
    deficiencyLine z =
      adjointGraphL2 ⊓ LinearMap.ker (deficiencyDefect z : GraphSpace →ₗ[ℂ] L2R3) :=
  rfl

/-- Membership in a deficiency line, in terms of the adjoint eigenspace. -/
theorem mem_deficiencyLine_iff {z : ℂ} {x : GraphSpace} :
    x ∈ deficiencyLine z ↔
      ∃ u ∈ adjointEigenspace H_X1_min z, x = toGraphSpace (u, z • u) := by
  rw [deficiencyLine_eq_inf, Submodule.mem_inf]
  constructor
  · rintro ⟨hxA, hxK⟩
    obtain ⟨u, rfl⟩ := (mem_graphL2_iff_exists (H_X1_min†)).mp hxA
    have h0 : deficiencyDefect z (toGraphSpace ((u : L2R3), H_X1_min† u)) = 0 :=
      LinearMap.mem_ker.mp hxK
    rw [deficiencyDefect_toGraphSpace, sub_eq_zero] at h0
    exact ⟨(u : L2R3), mem_adjointEigenspace_iff.mpr ⟨u.property, h0⟩, by rw [h0]⟩
  · rintro ⟨u, huE, rfl⟩
    obtain ⟨hu, huEq⟩ := mem_adjointEigenspace_iff.mp huE
    refine ⟨(mem_graphL2_iff_exists (H_X1_min†)).mpr ⟨⟨u, hu⟩, by rw [huEq]⟩, ?_⟩
    rw [LinearMap.mem_ker]
    change deficiencyDefect z (toGraphSpace (u, z • u)) = 0
    rw [deficiencyDefect_toGraphSpace, sub_self]

/-- Each deficiency line is closed: it is the intersection of the closed
realized adjoint graph with the closed kernel of the defect map. -/
theorem deficiencyLine_isClosed (z : ℂ) :
    IsClosed (deficiencyLine z : Set GraphSpace) := by
  have h : (deficiencyLine z : Set GraphSpace) =
      (adjointGraphL2 : Set GraphSpace) ∩
        (LinearMap.ker (deficiencyDefect z : GraphSpace →ₗ[ℂ] L2R3) :
          Submodule ℂ GraphSpace) := by
    rw [deficiencyLine_eq_inf, Submodule.coe_inf]
  rw [h]
  exact adjointGraphL2_isClosed.inter (deficiencyDefect z).isClosed_ker

/-! ### Graph-space orthogonality -/

/-- The two deficiency lines at `+i` and `-i` are orthogonal in the graph
space. -/
theorem deficiencyLine_orthogonal_plus_minus :
    ∀ x ∈ deficiencyLine Complex.I, ∀ y ∈ deficiencyLine (-Complex.I),
      inner ℂ x y = 0 := by
  intro x hx y hy
  obtain ⟨u, -, rfl⟩ := mem_deficiencyLine_iff.mp hx
  obtain ⟨v, -, rfl⟩ := mem_deficiencyLine_iff.mp hy
  rw [toGraphSpace_inner, inner_smul_left, inner_smul_right, Complex.conj_I]
  have hsq : -Complex.I * (-Complex.I * inner ℂ u v) =
      Complex.I ^ 2 * inner ℂ u v := by ring
  rw [hsq, Complex.I_sq]
  ring

/-- The realized minimal graph is orthogonal to the deficiency line at any
square root of `-1`.  This is the graph-space form of the symmetry computation
`⟪φ, u⟫ + z²⟪φ, u⟫ = 0`. -/
theorem minimalGraphL2_orthogonal_deficiencyLine (z : ℂ) (hz : z ^ 2 = -1) :
    ∀ x ∈ minimalGraphL2, ∀ y ∈ deficiencyLine z, inner ℂ x y = 0 := by
  intro x hx y hy
  obtain ⟨φ, rfl⟩ := (mem_graphL2_iff_exists H_X1_min).mp hx
  obtain ⟨u, huE, rfl⟩ := mem_deficiencyLine_iff.mp hy
  obtain ⟨hu, huEq⟩ := mem_adjointEigenspace_iff.mp huE
  have hform : inner ℂ (H_X1_min† ⟨u, hu⟩) ((φ : L2R3)) =
      inner ℂ u (H_X1_min φ) :=
    LinearPMap.adjoint_isFormalAdjoint H_X1_min_dense_domain ⟨u, hu⟩ φ
  rw [huEq, inner_smul_left] at hform
  have hHphi : inner ℂ (H_X1_min φ) u = z * inner ℂ (φ : L2R3) u := by
    rw [← inner_conj_symm, ← hform, map_mul, Complex.conj_conj, inner_conj_symm]
  rw [toGraphSpace_inner, inner_smul_right, hHphi]
  have hsq : z * (z * inner ℂ (φ : L2R3) u) =
      z ^ 2 * inner ℂ (φ : L2R3) u := by ring
  rw [hsq, hz]
  ring

/-- Orthogonality persists to the topological closure of the realized minimal
graph, since orthogonal complements are closed. -/
theorem minimalGraphL2_topologicalClosure_orthogonal_deficiencyLine
    (z : ℂ) (hz : z ^ 2 = -1) :
    ∀ x ∈ minimalGraphL2.topologicalClosure, ∀ y ∈ deficiencyLine z,
      inner ℂ x y = 0 := by
  intro x hx y hy
  have hle : minimalGraphL2 ≤ (deficiencyLine z)ᗮ := by
    intro w hw
    rw [Submodule.mem_orthogonal']
    intro v hv
    exact minimalGraphL2_orthogonal_deficiencyLine z hz w hw v hv
  have hx' : x ∈ (deficiencyLine z)ᗮ :=
    Submodule.topologicalClosure_minimal _ hle
      (deficiencyLine z).isClosed_orthogonal hx
  exact (Submodule.mem_orthogonal' _ _).mp hx' y hy

/-- The deficiency line is contained in the orthogonal complement of the
closed realized minimal graph. -/
theorem deficiencyLine_le_orthogonal_topologicalClosure
    (z : ℂ) (hz : z ^ 2 = -1) :
    deficiencyLine z ≤ minimalGraphL2.topologicalClosureᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  exact minimalGraphL2_topologicalClosure_orthogonal_deficiencyLine z hz x hx y hy

/-! ### The closure bridge -/

/-- The topological closure of the realized minimal graph is exactly the
realized graph of the operator closure of the minimal core. -/
theorem minimalGraphL2_topologicalClosure_eq_graphL2_closure :
    minimalGraphL2.topologicalClosure = graphL2 H_X1_min.closure := by
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe, graphL2_coe, graphL2_coe,
    ← H_X1_min_isClosable.graph_closure_eq_closure_graph,
    Submodule.topologicalClosure_coe]
  exact (toGraphSpace.symm.toHomeomorph.preimage_closure _).symm

end ExoticCCR
