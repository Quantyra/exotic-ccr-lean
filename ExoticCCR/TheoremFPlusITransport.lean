/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFAdjointEigenspace
import ExoticCCR.TheoremFSigmaSymmetry

/-!
# The `+i` weak deficiency family by sign-involution transport

The measure-preserving involution `σ(q₀,q₁,q₂) = (-q₀,-q₁,q₂)` reverses the
first dual field (`X1 ∘ σ = -σ ∘ X1`), so composition with `σ` is a
`ℂ`-linear involution of `L²(ℝ³)` that conjugates the minimal transport core
to its negative on the test-function domain.  Consequently it carries weak
`z`-adjoint eigenvectors to weak `-z`-adjoint eigenvectors.

Applied to the forward maximal-sheet `-i` families this discharges the named
`+i` obligation `X1BackwardWeakFamiliesStatement` and yields the bounded
Theorem F export `theoremF`: both adjoint eigenspaces `ker(H† ∓ i)` of the
canonical minimal transport core — the deficiency subspaces in the standard
reading for a densely defined symmetric operator; symmetry of the core on
`C_c^∞` is classical from `div X1 = 0` and is not separately formalized
here — are infinite dimensional.  No deficiency-index arithmetic, von
Neumann extension classification, or claim beyond the two displayed
non-finite-dimensionality statements is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped LinearPMap

namespace ExoticCCR

/-! ### Transport of test functions -/

/-- Composition with `σ` preserves the test-function space. -/
def sigmaTest (φ : CcinftyR3) : CcinftyR3 where
  toFun := (φ : R3 → ℂ) ∘ sigmaMap
  contDiff' := φ.contDiff.comp (contDiff_sigmaMap.of_le le_top)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph sigmaHomeomorph
  tsupport_subset' := by
    intro x _
    simp [allR3]

theorem sigmaTest_coe (φ : CcinftyR3) :
    (sigmaTest φ : R3 → ℂ) = (φ : R3 → ℂ) ∘ sigmaMap := rfl

/-! ### Transport on `L²` -/

/-- Composition with `σ` as a `ℂ`-linear endomorphism of `L²(ℝ³)`. -/
def sigmaL2 : L2R3 →ₗ[ℂ] L2R3 where
  toFun := Lp.compMeasurePreserving sigmaMap measurePreserving_sigmaMap
  map_add' u v := map_add _ u v
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • u) measurePreserving_sigmaMap,
      (measurePreserving_sigmaMap.quasiMeasurePreserving).ae_eq_comp
        (Lp.coeFn_smul c u),
      Lp.coeFn_compMeasurePreserving u measurePreserving_sigmaMap,
      Lp.coeFn_smul c
        (Lp.compMeasurePreserving sigmaMap measurePreserving_sigmaMap u)]
      with q h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] at h1 h2 h3 h4 ⊢
    rw [h4, h1, h2, ← h3]

theorem sigmaL2_apply (u : L2R3) :
    sigmaL2 u = Lp.compMeasurePreserving sigmaMap measurePreserving_sigmaMap u :=
  rfl

theorem coeFn_sigmaL2 (u : L2R3) :
    (sigmaL2 u : R3 → ℂ) =ᵐ[volume] (u : R3 → ℂ) ∘ sigmaMap :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_sigmaMap

/-- `σ`-transport of a selected representative. -/
theorem sigmaL2_toLp {f : R3 → ℂ} (hf : MemLp f 2 (volume : Measure R3)) :
    sigmaL2 (hf.toLp f) =
      (hf.comp_measurePreserving measurePreserving_sigmaMap).toLp (f ∘ sigmaMap) :=
  Lp.toLp_compMeasurePreserving hf measurePreserving_sigmaMap

/-- The `L²` transport is an involution. -/
theorem sigmaL2_sigmaL2 (u : L2R3) : sigmaL2 (sigmaL2 u) = u := by
  apply Lp.ext
  have h1 := coeFn_sigmaL2 (sigmaL2 u)
  have h2 : ((sigmaL2 u : L2R3) : R3 → ℂ) ∘ sigmaMap
      =ᵐ[volume] ((u : R3 → ℂ) ∘ sigmaMap) ∘ sigmaMap :=
    (measurePreserving_sigmaMap.quasiMeasurePreserving).ae_eq_comp
      (coeFn_sigmaL2 u)
  refine h1.trans (h2.trans ?_)
  filter_upwards with q
  simp [Function.comp, sigmaMap_involutive q]

theorem sigmaL2_injective : Function.Injective sigmaL2 :=
  Function.LeftInverse.injective sigmaL2_sigmaL2

/-- The transport is symmetric for the `L²` inner product. -/
theorem inner_sigmaL2_left (u v : L2R3) :
    inner ℂ (sigmaL2 u) v = inner ℂ u (sigmaL2 v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hswap :
      ∫ q : R3, inner ℂ ((u : R3 → ℂ) (sigmaMap q)) ((v : R3 → ℂ) q) ∂volume =
        ∫ q : R3, inner ℂ ((u : R3 → ℂ) q) ((v : R3 → ℂ) (sigmaMap q)) ∂volume := by
    have := measurePreserving_sigmaMap.integral_comp measurableEmbedding_sigmaMap
      (fun y : R3 => inner ℂ ((u : R3 → ℂ) y) ((v : R3 → ℂ) (sigmaMap y)))
    calc
      ∫ q : R3, inner ℂ ((u : R3 → ℂ) (sigmaMap q)) ((v : R3 → ℂ) q) ∂volume =
          ∫ q : R3, inner ℂ ((u : R3 → ℂ) (sigmaMap q))
            ((v : R3 → ℂ) (sigmaMap (sigmaMap q))) ∂volume := by
        apply integral_congr_ae
        filter_upwards with q
        rw [sigmaMap_involutive q]
      _ = _ := this
  calc
    ∫ q : R3, inner ℂ ((sigmaL2 u : R3 → ℂ) q) ((v : R3 → ℂ) q) ∂volume =
        ∫ q : R3, inner ℂ ((u : R3 → ℂ) (sigmaMap q)) ((v : R3 → ℂ) q) ∂volume := by
      apply integral_congr_ae
      filter_upwards [coeFn_sigmaL2 u] with q hq
      rw [hq]; rfl
    _ = ∫ q : R3, inner ℂ ((u : R3 → ℂ) q) ((v : R3 → ℂ) (sigmaMap q)) ∂volume :=
      hswap
    _ = ∫ q : R3, inner ℂ ((u : R3 → ℂ) q) ((sigmaL2 v : R3 → ℂ) q) ∂volume := by
      apply integral_congr_ae
      filter_upwards [coeFn_sigmaL2 v] with q hq
      rw [hq]; rfl

/-- Transport commutes with the test-function embedding. -/
theorem testFunctionToL2_sigmaTest (φ : CcinftyR3) :
    testFunctionToL2 (sigmaTest φ) = sigmaL2 (testFunctionToL2 φ) := by
  rw [testFunctionToL2_apply, testFunctionToL2_apply, sigmaL2_toLp]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun q => rfl

/-! ### The core anti-commutation -/

/-- Pointwise, the transport expression of the reflected test function is the
negative of the reflected transport expression.  This is the chain rule plus
the field reversal `σ (X1 q) = -X1 (σ q)`. -/
theorem minimalTransportExpression_sigmaTest (φ : CcinftyR3) (q : R3) :
    minimalTransportExpression X1 (sigmaTest φ) q =
      -(minimalTransportExpression X1 φ (sigmaMap q)) := by
  have hφd : DifferentiableAt ℝ (φ : R3 → ℂ) (sigmaMap q) :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  have hcomp :
      HasFDerivAt ((φ : R3 → ℂ) ∘ sigmaMap)
        ((fderiv ℝ (φ : R3 → ℂ) (sigmaMap q)).comp sigmaCLM) q :=
    (hφd.hasFDerivAt).comp q (hasFDerivAt_sigmaMap q)
  have hfd : fderiv ℝ ((φ : R3 → ℂ) ∘ sigmaMap) q =
      (fderiv ℝ (φ : R3 → ℂ) (sigmaMap q)).comp sigmaCLM :=
    hcomp.fderiv
  have happ :
      fderiv ℝ ((φ : R3 → ℂ) ∘ sigmaMap) q (X1 q) =
        -(fderiv ℝ (φ : R3 → ℂ) (sigmaMap q) (X1 (sigmaMap q))) := by
    rw [hfd]
    change fderiv ℝ (φ : R3 → ℂ) (sigmaMap q) (sigmaCLM (X1 q)) = _
    rw [sigmaCLM_apply, sigmaMap_X1, map_neg]
  calc
    minimalTransportExpression X1 (sigmaTest φ) q =
        -Complex.I * fderiv ℝ ((φ : R3 → ℂ) ∘ sigmaMap) q (X1 q) := by
      rw [minimalTransportExpression, sigmaTest_coe]
    _ = -Complex.I * -(fderiv ℝ (φ : R3 → ℂ) (sigmaMap q) (X1 (sigmaMap q))) := by
      rw [happ]
    _ = -(minimalTransportExpression X1 φ (sigmaMap q)) := by
      rw [minimalTransportExpression]
      ring

/-- `L²` form of the anti-commutation: the transport action of the reflected
test function is minus the transported action. -/
theorem transportAction_sigmaTest (φ : CcinftyR3) :
    transportAction X1 contDiff_X1.continuous (sigmaTest φ) =
      -(sigmaL2 (transportAction X1 contDiff_X1.continuous φ)) := by
  change (transportExpressionMemLp X1 contDiff_X1.continuous (sigmaTest φ)).toLp
      (minimalTransportExpression X1 (sigmaTest φ)) = _
  rw [show transportAction X1 contDiff_X1.continuous φ =
      (transportExpressionMemLp X1 contDiff_X1.continuous φ).toLp
        (minimalTransportExpression X1 φ) from rfl]
  rw [sigmaL2_toLp, ← MemLp.toLp_neg]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun q =>
    minimalTransportExpression_sigmaTest φ q

/-! ### Weak eigenvector transport -/

/-- The generic test-function reduction of the weak adjoint identity for the
canonical minimal transport core. -/
theorem weakAdjointEigenvector_of_test {z : ℂ} {u : L2R3}
    (h : ∀ φ : CcinftyR3,
      inner ℂ (z • u) (testFunctionToL2 φ) =
        inner ℂ u (transportAction X1 contDiff_X1.continuous φ)) :
    WeakAdjointEigenvector H_X1_min z u := by
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

/-- Applying the weak identity to an embedded test function. -/
theorem weakAdjointEigenvector_apply_test {z : ℂ} {u : L2R3}
    (hu : WeakAdjointEigenvector H_X1_min z u) (φ : CcinftyR3) :
    inner ℂ (z • u) (testFunctionToL2 φ) =
      inner ℂ u (transportAction X1 contDiff_X1.continuous φ) := by
  have hmem : testFunctionToL2 φ ∈ H_X1_min.domain := by
    rw [minimalTransportCore_domain]
    exact LinearMap.mem_range_self testFunctionToL2 φ
  have := hu ⟨testFunctionToL2 φ, hmem⟩
  rwa [minimalTransportCore_apply] at this

/-- The sign involution transports weak `z`-adjoint eigenvectors to weak
`-z`-adjoint eigenvectors. -/
theorem weakAdjointEigenvector_sigmaL2 {z : ℂ} {u : L2R3}
    (hu : WeakAdjointEigenvector H_X1_min z u) :
    WeakAdjointEigenvector H_X1_min (-z) (sigmaL2 u) := by
  apply weakAdjointEigenvector_of_test
  intro φ
  have hswap := inner_sigmaL2_left u (testFunctionToL2 φ)
  calc
    inner ℂ ((-z) • sigmaL2 u) (testFunctionToL2 φ) =
        -((starRingEnd ℂ) z * inner ℂ (sigmaL2 u) (testFunctionToL2 φ)) := by
      rw [inner_smul_left, map_neg]
      ring
    _ = -((starRingEnd ℂ) z * inner ℂ u (sigmaL2 (testFunctionToL2 φ))) := by
      rw [hswap]
    _ = -((starRingEnd ℂ) z * inner ℂ u (testFunctionToL2 (sigmaTest φ))) := by
      rw [testFunctionToL2_sigmaTest]
    _ = -(inner ℂ (z • u) (testFunctionToL2 (sigmaTest φ))) := by
      rw [inner_smul_left]
    _ = -(inner ℂ u (transportAction X1 contDiff_X1.continuous (sigmaTest φ))) := by
      rw [weakAdjointEigenvector_apply_test hu]
    _ = -(inner ℂ u (-(sigmaL2 (transportAction X1 contDiff_X1.continuous φ)))) := by
      rw [transportAction_sigmaTest]
    _ = inner ℂ u (sigmaL2 (transportAction X1 contDiff_X1.continuous φ)) := by
      rw [inner_neg_right]
      ring
    _ = inner ℂ (sigmaL2 u) (transportAction X1 contDiff_X1.continuous φ) :=
      (inner_sigmaL2_left u (transportAction X1 contDiff_X1.continuous φ)).symm

/-! ### The `+i` families and the bounded Theorem F export -/

/-- For every finite cardinality there are linearly independent `L²` weak `+i`
adjoint eigenvectors for the canonical minimal transport core of `X1`,
obtained by `σ`-transport of the forward maximal-sheet `-i` families. -/
theorem exists_finite_weakAdjointEigenvector_posI_family (n : ℕ) :
    ∃ u : Fin n → L2R3,
      LinearIndependent ℂ u ∧
        ∀ i, WeakAdjointEigenvector H_X1_min Complex.I (u i) := by
  obtain ⟨u, hu, huEig⟩ := exists_finite_weakAdjointEigenvector_negI_family n
  refine ⟨fun i => sigmaL2 (u i), ?_, ?_⟩
  · exact hu.map' sigmaL2 (LinearMap.ker_eq_bot.mpr sigmaL2_injective)
  · intro i
    have h := weakAdjointEigenvector_sigmaL2 (huEig i)
    simpa using h

/-- The named `+i` obligation of the adjoint-eigenspace module holds. -/
theorem X1BackwardWeakFamiliesStatement_holds : X1BackwardWeakFamiliesStatement :=
  exists_finite_weakAdjointEigenvector_posI_family

/-- The weak `+i` eigenspace of the canonical minimal transport core is not
finite-dimensional. -/
theorem weakAdjointEigenspace_posI_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (weakAdjointEigenspace H_X1_min Complex.I) :=
  weakAdjointEigenspace_not_finiteDimensional_of_finite_families
    H_X1_min Complex.I exists_finite_weakAdjointEigenvector_posI_family

/-- The sign-transport construction gives a countable lower bound for the
standard `+i` deficiency index. -/
theorem aleph0_le_standardDeficiencyIndex_posI :
    Cardinal.aleph0 ≤ standardDeficiencyIndex H_X1_min Complex.I :=
  aleph0_le_standardDeficiencyIndex_of_not_finiteDimensional
    (by
      rw [← weakAdjointEigenspace_eq_adjointEigenspace H_X1_min
        (minimalTransportCore_dense_domain X1 contDiff_X1.continuous) Complex.I]
      exact weakAdjointEigenspace_posI_not_finiteDimensional)

/-- Both cardinal-valued standard deficiency indices have the lower bound
supported by the current finite-family constructions. -/
theorem aleph0_le_standardDeficiencyIndex_X1 :
    Cardinal.aleph0 ≤ standardDeficiencyIndex H_X1_min Complex.I ∧
      Cardinal.aleph0 ≤ standardDeficiencyIndex H_X1_min (-Complex.I) :=
  ⟨aleph0_le_standardDeficiencyIndex_posI,
    aleph0_le_standardDeficiencyIndex_negI⟩

/-- **A001 Theorem F, bounded Lean form.**  Both eigenspaces of mathlib's
`LinearPMap.adjoint` at `+i` and `-i` for the canonical minimal transport
core of `X1` are infinite dimensional.  These are the deficiency subspaces
in the standard reading for a densely defined symmetric operator; symmetry
of the core on `C_c^∞` is classical from `div X1 = 0` and is not
separately formalized here.  In the classical notation this is
`(n₊, n₋) = (∞, ∞)` read as non-finite-dimensionality of `ker(H† - i)`
and `ker(H† + i)`; no further deficiency-index arithmetic or extension
classification is asserted. -/
theorem theoremF :
    ¬ FiniteDimensional ℂ (adjointEigenspace H_X1_min Complex.I) ∧
      ¬ FiniteDimensional ℂ (adjointEigenspace H_X1_min (-Complex.I)) :=
  adjointEigenspace_both_not_finiteDimensional_of_backwardFamilies
    X1BackwardWeakFamiliesStatement_holds

end ExoticCCR
