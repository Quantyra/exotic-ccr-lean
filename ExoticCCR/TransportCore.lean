/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TransportOperator
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The canonical minimal transport core

This module realizes the pointwise expression `-i Xφ` on compactly supported
smooth functions as a partially defined operator on `L²(ℝ³)`.  Density of the
test-function embedding is isolated as an explicit statement rather than
silently imported as an analytic axiom.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace ExoticCCR

/-- A compactly supported smooth function belongs to `L²(ℝ³)`. -/
theorem testFunctionMemLp (φ : CcinftyR3) :
    MemLp (φ : R3 → ℂ) 2 (volume : Measure R3) :=
  φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

/-- The canonical linear embedding of test functions into `L²(ℝ³)`. -/
def testFunctionToL2 : CcinftyR3 →ₗ[ℂ] L2R3 where
  toFun φ := (testFunctionMemLp φ).toLp (φ : R3 → ℂ)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add (testFunctionMemLp φ) (testFunctionMemLp ψ)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  map_smul' c φ := by
    change (testFunctionMemLp (c • φ)).toLp (c • (φ : R3 → ℂ)) =
      c • (testFunctionMemLp φ).toLp (φ : R3 → ℂ)
    rw [← MemLp.toLp_const_smul c (testFunctionMemLp φ)]

/-- The test-function embedding is represented by the original function almost everywhere. -/
theorem testFunctionToL2_apply (φ : CcinftyR3) :
    testFunctionToL2 φ = (testFunctionMemLp φ).toLp (φ : R3 → ℂ) :=
  rfl

/-- The `L²` inner product of two chosen representatives is the integral of
their pointwise inner product, using mathlib's convention that the first
argument is conjugate-linear. -/
theorem inner_toLp_toLp_eq_integral {f g : R3 → ℂ}
    (hf : MemLp f 2 (volume : Measure R3)) (hg : MemLp g 2 (volume : Measure R3)) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ q : R3, inner ℂ (f q) (g q) ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with q hfq hgq
  simp [hfq, hgq]

/-- Inner product against an embedded test function, exposed as an integral
over the selected `L²` representative. -/
theorem inner_toLp_testFunctionToL2_eq_integral {f : R3 → ℂ}
    (hf : MemLp f 2 (volume : Measure R3)) (φ : CcinftyR3) :
    inner ℂ (hf.toLp f) (testFunctionToL2 φ) =
      ∫ q : R3, inner ℂ (f q) (φ q) ∂volume := by
  simpa [testFunctionToL2_apply] using
    inner_toLp_toLp_eq_integral hf (testFunctionMemLp φ)

/-- Inner product of an embedded test function against a selected `L²`
representative, exposed as a representative integral. -/
theorem inner_testFunctionToL2_toLp_eq_integral {f : R3 → ℂ}
    (hf : MemLp f 2 (volume : Measure R3)) (φ : CcinftyR3) :
    inner ℂ (testFunctionToL2 φ) (hf.toLp f) =
      ∫ q : R3, inner ℂ (φ q) (f q) ∂volume := by
  simpa [testFunctionToL2_apply] using
    inner_toLp_toLp_eq_integral (testFunctionMemLp φ) hf

/-- A continuous representative that is nonzero at some point gives a nonzero
`L²` class. -/
theorem toLp_ne_zero_of_continuous_exists_ne {f : R3 → ℂ}
    (hf : MemLp f 2 (volume : Measure R3)) (hfc : Continuous f)
    (hne : ∃ q : R3, f q ≠ 0) :
    hf.toLp f ≠ 0 := by
  rintro hzero
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero] at hzero
  obtain ⟨q, hq⟩ := hne
  have hfae : f =ᵐ[volume] 0 := hf.coeFn_toLp.symm.trans hzero
  have hzeroMeasure : volume {x : R3 | f x ≠ 0} = 0 := by
    simpa only [Pi.zero_apply, ne_eq] using (ae_iff.mp hfae)
  have hne_nhds : {x : R3 | f x ≠ 0} ∈ 𝓝 q :=
    hfc.continuousAt.eventually_ne hq
  have hpos : 0 < volume {x : R3 | f x ≠ 0} :=
    Measure.measure_pos_of_mem_nhds (μ := volume) hne_nhds
  exact hpos.ne' hzeroMeasure

/-- A representative that is not almost everywhere zero gives a nonzero `L²`
class. -/
theorem toLp_ne_zero_of_not_ae_eq_zero {f : R3 → ℂ}
    (hf : MemLp f 2 (volume : Measure R3)) (hne : ¬ f =ᵐ[volume] 0) :
    hf.toLp f ≠ 0 := by
  rintro hzero
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero] at hzero
  exact hne (hf.coeFn_toLp.symm.trans hzero)

/-- The canonical test-function embedding into `L²(ℝ³)` is injective. -/
theorem testFunctionToL2_injective : Function.Injective testFunctionToL2 :=
  fun φ ψ h ↦ by
    have heq := (Continuous.ae_eq_iff_eq (volume : Measure R3) φ.continuous ψ.continuous).mp
      ((MemLp.toLp_eq_toLp_iff (testFunctionMemLp φ) (testFunctionMemLp ψ)).mp h)
    ext q
    exact congrFun heq q

/-- For continuous `X`, the pointwise transport expression is continuous. -/
theorem continuous_minimalTransportExpression (X : R3 → R3) (hX : Continuous X)
    (φ : CcinftyR3) : Continuous (minimalTransportExpression X φ) := by
  have hderiv : Continuous fun q : R3 ↦ fderiv ℝ (φ : R3 → ℂ) q (X q) :=
    φ.contDiff.continuous_fderiv_apply (by simp) |>.comp (continuous_id.prodMk hX)
  change Continuous fun q : R3 ↦ -Complex.I * fderiv ℝ (φ : R3 → ℂ) q (X q)
  exact continuous_const.mul hderiv

/-- For continuous `X`, the pointwise transport expression has compact support. -/
theorem hasCompactSupport_minimalTransportExpression (X : R3 → R3) (φ : CcinftyR3) :
    HasCompactSupport (minimalTransportExpression X φ) := by
  apply (φ.hasCompactSupport.fderiv ℝ).mono'
  intro q hq
  change minimalTransportExpression X φ q ≠ 0 at hq
  apply subset_tsupport
  change fderiv ℝ (φ : R3 → ℂ) q ≠ 0
  intro hzero
  apply hq
  simp [minimalTransportExpression, hzero]

/-- The pointwise transport expression of a test function belongs to `L²(ℝ³)`. -/
theorem transportExpressionMemLp (X : R3 → R3) (hX : Continuous X) (φ : CcinftyR3) :
    MemLp (minimalTransportExpression X φ) 2 (volume : Measure R3) :=
  (continuous_minimalTransportExpression X hX φ).memLp_of_hasCompactSupport
    (hasCompactSupport_minimalTransportExpression X φ)

/-- The transport expression is additive in its test-function argument. -/
theorem minimalTransportExpression_add (X : R3 → R3) (φ ψ : CcinftyR3) :
    minimalTransportExpression X (φ + ψ) =
      minimalTransportExpression X φ + minimalTransportExpression X ψ := by
  funext q
  simp only [minimalTransportExpression, Pi.add_apply]
  rw [show ((φ + ψ : CcinftyR3) : R3 → ℂ) =
    (φ : R3 → ℂ) + (ψ : R3 → ℂ) by rfl]
  rw [fderiv_add (φ.contDiff.differentiable (by simp)).differentiableAt
    (ψ.contDiff.differentiable (by simp)).differentiableAt]
  simp [mul_add]

/-- The transport expression is complex-linear in its test-function argument. -/
theorem minimalTransportExpression_smul (X : R3 → R3) (c : ℂ) (φ : CcinftyR3) :
    minimalTransportExpression X (c • φ) = c • minimalTransportExpression X φ := by
  funext q
  simp only [minimalTransportExpression, Pi.smul_apply]
  rw [show ((c • φ : CcinftyR3) : R3 → ℂ) = c • (φ : R3 → ℂ) by rfl]
  rw [fderiv_const_smul (φ.contDiff.differentiable (by simp)).differentiableAt c]
  change -Complex.I * (c * fderiv ℝ (φ : R3 → ℂ) q (X q)) =
    c * (-Complex.I * fderiv ℝ (φ : R3 → ℂ) q (X q))
  ring

/-- The `L²` action of the transport expression on test functions. -/
def transportAction (X : R3 → R3) (hX : Continuous X) : CcinftyR3 →ₗ[ℂ] L2R3 where
  toFun φ := (transportExpressionMemLp X hX φ).toLp (minimalTransportExpression X φ)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add (transportExpressionMemLp X hX φ)
      (transportExpressionMemLp X hX ψ)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun q ↦ congrFun (minimalTransportExpression_add X φ ψ) q
  map_smul' c φ := by
    change (transportExpressionMemLp X hX (c • φ)).toLp
        (minimalTransportExpression X (c • φ)) =
      c • (transportExpressionMemLp X hX φ).toLp (minimalTransportExpression X φ)
    rw [← MemLp.toLp_const_smul c (transportExpressionMemLp X hX φ)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun q ↦ congrFun (minimalTransportExpression_smul X c φ) q

/-- The linear map whose range is the graph of the minimal transport core. -/
def minimalTransportGraphMap (X : R3 → R3) (hX : Continuous X) :
    CcinftyR3 →ₗ[ℂ] L2R3 × L2R3 :=
  testFunctionToL2.prod (transportAction X hX)

/-- The proposed graph of the minimal transport core is single-valued. -/
theorem minimalTransportGraph_functional (X : R3 → R3) (hX : Continuous X) :
    ∀ (x : L2R3 × L2R3), x ∈ LinearMap.range (minimalTransportGraphMap X hX) →
      x.fst = 0 → x.snd = 0 := by
  rintro _ ⟨φ, rfl⟩ hφ
  have : φ = 0 := testFunctionToL2_injective (by simpa [minimalTransportGraphMap] using hφ)
  subst φ
  simp [minimalTransportGraphMap]

/-- The canonical minimal transport operator with domain the embedded test functions. -/
def minimalTransportCore (X : R3 → R3) (hX : Continuous X) : L2R3 →ₗ.[ℂ] L2R3 :=
  (LinearMap.range (minimalTransportGraphMap X hX)).toLinearPMap

/-- The domain of the minimal transport core is exactly the range of the test-function embedding. -/
theorem minimalTransportCore_domain (X : R3 → R3) (hX : Continuous X) :
    (minimalTransportCore X hX).domain = LinearMap.range testFunctionToL2 := by
  ext u
  simp [minimalTransportCore, minimalTransportGraphMap, Submodule.toLinearPMap_domain,
    LinearMap.mem_range]

/-- On an embedded test function, the minimal transport core has the expected `L²` action. -/
theorem minimalTransportCore_apply (X : R3 → R3) (hX : Continuous X) (φ : CcinftyR3) :
    minimalTransportCore X hX
        ⟨testFunctionToL2 φ, by
          rw [minimalTransportCore_domain]
          exact LinearMap.mem_range_self testFunctionToL2 φ⟩ =
      transportAction X hX φ := by
  symm
  rw [LinearPMap.image_iff]
  unfold minimalTransportCore
  rw [Submodule.toLinearPMap_graph_eq _ (minimalTransportGraph_functional X hX)]
  exact LinearMap.mem_range_self (minimalTransportGraphMap X hX) φ

/-- The standard density assertion for the canonical test-function embedding. -/
def TestFunctionL2DensityStatement : Prop :=
  Dense (LinearMap.range testFunctionToL2 : Set L2R3)

/-- Compactly supported smooth functions are dense in `L²(ℝ³)`. -/
theorem testFunctionL2_dense : TestFunctionL2DensityStatement := by
  apply Dense.mono ?_ (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (by norm_num))
  rintro f ⟨g, hfg, hg_compact, hg_smooth⟩
  let φ : CcinftyR3 := ⟨g, hg_smooth, hg_compact, Set.subset_univ _⟩
  refine ⟨φ, ?_⟩
  rw [testFunctionToL2_apply]
  calc
    _ = (MeasureTheory.Lp.memLp f).toLp f :=
      MemLp.toLp_congr _ _ (by
        change g =ᵐ[volume] (f : R3 → ℂ)
        exact hfg.symm)
    _ = f := MeasureTheory.Lp.toLp_coeFn f (MeasureTheory.Lp.memLp f)

/-- The named density theorem gives density of the test-function embedding. -/
theorem dense_range_testFunctionToL2 :
    Dense (LinearMap.range testFunctionToL2 : Set L2R3) :=
  testFunctionL2_dense

/-- The domain of the canonical minimal transport core is dense. -/
theorem minimalTransportCore_dense_domain (X : R3 → R3) (hX : Continuous X) :
    Dense ((minimalTransportCore X hX).domain : Set L2R3) := by
  rw [minimalTransportCore_domain]
  exact testFunctionL2_dense

end ExoticCCR
