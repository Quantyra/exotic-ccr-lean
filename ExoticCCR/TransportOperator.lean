/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Minimal transport-operator infrastructure

This module fixes the ambient Hilbert space and the compactly supported smooth
core for the formal differential expression `-i X`.  It deliberately does not
assert that this expression has already been realized as a densely defined
operator on `L²`; that analytic realization is recorded separately below.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace ExoticCCR

/-- Real three-space in the coordinate model used by the anchor. -/
abbrev R3 := Fin 3 → ℝ

/-- The complex Hilbert space `L²(ℝ³)`. -/
abbrev L2R3 := ↥(MeasureTheory.Lp ℂ 2 (volume : Measure R3))

/-- The open set underlying all of `ℝ³`. -/
def allR3 : Opens R3 := ⟨Set.univ, isOpen_univ⟩

/-- Compactly supported smooth complex-valued functions on `ℝ³`. -/
abbrev CcinftyR3 := TestFunction allR3 ℂ ⊤

/-- The pointwise differential expression `-i Xφ`. -/
def minimalTransportExpression (X : R3 → R3) (φ : CcinftyR3) (q : R3) : ℂ :=
  -Complex.I * fderiv ℝ (φ : R3 → ℂ) q (X q)

/-- Local definition of essential self-adjointness for a partially defined operator. -/
def _root_.LinearPMap.IsEssentiallySelfAdjoint (H : L2R3 →ₗ.[ℂ] L2R3) : Prop :=
  H.IsClosable ∧ IsSelfAdjoint H.closure

/--
An analytic realization of the minimal transport expression on `L²(ℝ³)`.

The field `agreesOnCore` keeps the unbounded-operator boundary explicit: a
realization must supply an `L²` representative of every test function and show
that the operator has the displayed pointwise differential expression there.
-/
structure MinimalTransportRealization (X : R3 → R3) where
  operator : L2R3 →ₗ.[ℂ] L2R3
  coreToL2 : CcinftyR3 →ₗ[ℂ] L2R3
  core_mem_domain : ∀ φ, coreToL2 φ ∈ operator.domain
  agreesOnCore : ∀ φ, ∃ hmem : MemLp (minimalTransportExpression X φ) 2 volume,
    operator ⟨coreToL2 φ, core_mem_domain φ⟩ = hmem.toLp (minimalTransportExpression X φ)

/-- The partially defined `L²` operator carried by a transport realization. -/
def minimalTransport {X : R3 → R3} (H : MinimalTransportRealization X) :
    L2R3 →ₗ.[ℂ] L2R3 := H.operator

end ExoticCCR
