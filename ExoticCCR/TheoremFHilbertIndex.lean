/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ExoticCCR.TheoremFPlusITransport

/-!
# Hilbert-space deficiency indices for Theorem F

This module separates the Hilbert dimension of an adjoint eigenspace from its
algebraic (`Module.rank`) dimension.  The index is the cardinality of a chosen
Hilbert basis.  Closedness is proved from the closed graph of the adjoint by a
continuous graph-line preimage; countability is proved from disjoint open balls
around the orthonormal basis vectors.
-/

noncomputable section

open MeasureTheory Set
open scoped LinearPMap ENNReal

namespace ExoticCCR

/-! ### Closed adjoint eigenspaces -/

/-- The graph line for the equation `v = z • u`. -/
def adjointEigenspaceGraphLine (z : ℂ) :
    L2R3 →L[ℂ] L2R3 × L2R3 where
  toFun u := (u, z • u)
  map_add' u v := by simp
  map_smul' c u := by simp [smul_smul, mul_comm]
  cont := Continuous.prodMk continuous_id (continuous_const_smul z)

@[simp]
theorem adjointEigenspaceGraphLine_apply (z : ℂ) (u : L2R3) :
    adjointEigenspaceGraphLine z u = (u, z • u) :=
  rfl

/-- The eigenspace is the preimage of the adjoint graph under its graph line. -/
theorem adjointEigenspace_eq_graphLine_preimage
    (H : L2R3 →ₗ.[ℂ] L2R3) (z : ℂ) :
    (adjointEigenspace H z : Set L2R3) =
      (adjointEigenspaceGraphLine z) ⁻¹' ((H†).graph : Set (L2R3 × L2R3)) := by
  ext u
  change u ∈ adjointEigenspace H z ↔
    adjointEigenspaceGraphLine z u ∈ (H†).graph
  rw [adjointEigenspaceGraphLine_apply]
  simp only [LinearPMap.mem_graph_iff]
  rw [mem_adjointEigenspace_iff]
  constructor
  · rintro ⟨hu, hHu⟩
    exact ⟨⟨u, hu⟩, rfl, hHu⟩
  · intro hu
    rcases hu with ⟨⟨u', hu'⟩, rfl, hHu⟩
    exact ⟨hu', hHu⟩

/-- If `H.domain` is dense, then the adjoint eigenspace at any scalar is closed. -/
theorem adjointEigenspace_isClosed
    (H : L2R3 →ₗ.[ℂ] L2R3) (hDense : Dense (H.domain : Set L2R3)) (z : ℂ) :
    IsClosed (adjointEigenspace H z : Set L2R3) := by
  rw [adjointEigenspace_eq_graphLine_preimage]
  exact (LinearPMap.adjoint_isClosed hDense).preimage
    (adjointEigenspaceGraphLine z).continuous

/-! ### Chosen Hilbert-basis cardinal -/

/-- The index type of a chosen Hilbert basis for a closed subspace. -/
noncomputable def hilbertBasisIndex
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3)) : Set S := by
  letI : IsClosed (S : Set L2R3) := hS
  exact (exists_hilbertBasis ℂ S).choose

/-- A chosen Hilbert basis for a closed subspace. -/
noncomputable def chosenHilbertBasis
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3)) :
    HilbertBasis (hilbertBasisIndex S hS) ℂ S := by
  letI : IsClosed (S : Set L2R3) := hS
  simpa only [hilbertBasisIndex] using (exists_hilbertBasis ℂ S).choose_spec.choose

/-- The Hilbert-space deficiency index, using the chosen Hilbert-basis index. -/
noncomputable def hilbertDeficiencyIndex
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3)) : Cardinal :=
  Cardinal.mk (hilbertBasisIndex S hS)

private theorem dist_chosenHilbertBasis_ge_one
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3))
    {i j : hilbertBasisIndex S hS} (hij : i ≠ j) :
    1 ≤ dist (chosenHilbertBasis S hS i) (chosenHilbertBasis S hS j) := by
  have hnorm : ‖chosenHilbertBasis S hS i - chosenHilbertBasis S hS j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq ℂ]
    rw [(chosenHilbertBasis S hS).orthonormal.norm_eq_one i,
      (chosenHilbertBasis S hS).orthonormal.norm_eq_one j,
      (chosenHilbertBasis S hS).orthonormal.inner_eq_zero hij]
    norm_num
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (chosenHilbertBasis S hS i - chosenHilbertBasis S hS j)]

/-- The radius-`1/2` balls around distinct chosen Hilbert-basis vectors are disjoint. -/
private theorem pairwiseDisjoint_chosenHilbertBasis_balls
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3)) :
    (Set.univ : Set (hilbertBasisIndex S hS)).PairwiseDisjoint
      (fun i => Metric.ball (chosenHilbertBasis S hS i) (1 / 2 : ℝ)) := by
  intro i hi j hj hij
  apply Metric.ball_disjoint_ball
  have hdist := dist_chosenHilbertBasis_ge_one S hS hij
  norm_num at hdist ⊢
  exact hdist

/-- A chosen Hilbert-basis index of a closed subspace of `L2(R³)` is countable. -/
theorem countable_hilbertBasisIndex
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3)) :
    Countable (hilbertBasisIndex S hS) := by
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact Pairwise.countable_of_isOpen_disjoint
    (s := fun i : hilbertBasisIndex S hS =>
      Metric.ball (chosenHilbertBasis S hS i) (1 / 2 : ℝ))
    (fun i j hij => by
      apply Metric.ball_disjoint_ball (x := chosenHilbertBasis S hS i)
        (y := chosenHilbertBasis S hS j)
      have hdist := dist_chosenHilbertBasis_ge_one S hS hij
      norm_num at hdist ⊢
      exact hdist)
    (fun i => Metric.isOpen_ball)
    (fun i => ⟨chosenHilbertBasis S hS i,
      Metric.mem_ball_self (show (0 : ℝ) < 1 / 2 by norm_num)⟩)

/-- A finite chosen Hilbert-basis index would make the subspace finite-dimensional. -/
private theorem finiteDimensional_of_finite_hilbertBasisIndex
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3))
    [Finite (hilbertBasisIndex S hS)] :
    FiniteDimensional ℂ S := by
  letI : Fintype (hilbertBasisIndex S hS) := Fintype.ofFinite _
  exact (chosenHilbertBasis S hS).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- A non-finite-dimensional closed subspace has an infinite chosen Hilbert-basis index. -/
theorem infinite_hilbertBasisIndex_of_not_finiteDimensional
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3))
    (h : ¬ FiniteDimensional ℂ S) :
    Infinite (hilbertBasisIndex S hS) := by
  rw [← not_finite_iff_infinite]
  intro hfinite
  letI := hfinite
  exact h (finiteDimensional_of_finite_hilbertBasisIndex S hS)

/-- A non-finite-dimensional closed subspace has Hilbert deficiency index `aleph0`. -/
theorem hilbertDeficiencyIndex_eq_aleph0_of_not_finiteDimensional
    (S : Submodule ℂ L2R3) (hS : IsClosed (S : Set L2R3))
    (h : ¬ FiniteDimensional ℂ S) :
    hilbertDeficiencyIndex S hS = Cardinal.aleph0 := by
  letI : Countable (hilbertBasisIndex S hS) := countable_hilbertBasisIndex S hS
  letI : Infinite (hilbertBasisIndex S hS) :=
    infinite_hilbertBasisIndex_of_not_finiteDimensional S hS h
  exact Cardinal.mk_eq_aleph0 _

/-! ### Theorem F applications -/

theorem hilbertDeficiencyIndex_posI_eq_aleph0 :
    hilbertDeficiencyIndex
        (adjointEigenspace H_X1_min Complex.I)
        (adjointEigenspace_isClosed H_X1_min
          (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) Complex.I) =
      Cardinal.aleph0 :=
  hilbertDeficiencyIndex_eq_aleph0_of_not_finiteDimensional
    (adjointEigenspace H_X1_min Complex.I)
    (adjointEigenspace_isClosed H_X1_min
      (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) Complex.I)
    theoremF.1

theorem hilbertDeficiencyIndex_negI_eq_aleph0 :
    hilbertDeficiencyIndex
        (adjointEigenspace H_X1_min (-Complex.I))
        (adjointEigenspace_isClosed H_X1_min
          (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) (-Complex.I)) =
      Cardinal.aleph0 :=
  hilbertDeficiencyIndex_eq_aleph0_of_not_finiteDimensional
    (adjointEigenspace H_X1_min (-Complex.I))
    (adjointEigenspace_isClosed H_X1_min
      (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) (-Complex.I))
    theoremF.2

theorem hilbertDeficiencyIndex_X1_eq_aleph0 :
    hilbertDeficiencyIndex
        (adjointEigenspace H_X1_min Complex.I)
        (adjointEigenspace_isClosed H_X1_min
          (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) Complex.I) =
      Cardinal.aleph0 ∧
    hilbertDeficiencyIndex
        (adjointEigenspace H_X1_min (-Complex.I))
        (adjointEigenspace_isClosed H_X1_min
          (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) (-Complex.I)) =
      Cardinal.aleph0 :=
  ⟨hilbertDeficiencyIndex_posI_eq_aleph0, hilbertDeficiencyIndex_negI_eq_aleph0⟩

end ExoticCCR
