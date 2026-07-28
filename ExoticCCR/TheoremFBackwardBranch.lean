/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardWall

/-!
# Base slice for the A001 backward branch

This module constructs the fixed-height local positive-root germ of the smooth
extended backward equation at the distinguished backward wall point.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- A local smooth positive-root model at the fixed backward wall height `alpha = 1/2`. -/
theorem exists_backwardBranchR_germ :
    ∃ (V : Set ((ℝ × ℝ) × ℝ)) (rMinus : ((ℝ × ℝ) × ℝ) → ℝ),
      IsOpen V ∧
      (((1 / 54), 2), 0) ∈ V ∧
      ContDiffOn ℝ ⊤ rMinus V ∧
      rMinus (((1 / 54), 2), 0) = Real.sqrt 6 ∧
      (∀ p ∈ V, wallGMinus p.1.1 p.1.2 (1 / 2) p.2 (rMinus p) = 0) ∧
      (∀ p ∈ V, rMinus p ≠ 0) := by
  let f : (((ℝ × ℝ) × ℝ) × ℝ) → ℝ := fun p =>
    wallGMinus p.1.1.1 p.1.1.2 (1 / 2) p.1.2 p.2
  let u : (((ℝ × ℝ) × ℝ) × ℝ) := ((((1 / 54), 2), 0), Real.sqrt 6)
  have hf : ContDiffAt ℝ ω f u := by
    unfold f wallGMinus wallADividedDiffPlus wallB wallC
    fun_prop
  have hpartial :
      (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ).IsInvertible := by
    have hsqrt : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by norm_num
    have hraw : HasDerivAt (fun r : ℝ => (1 / 6) * r ^ 3 - r) 2
        (Real.sqrt 6) := by
      convert (((hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 6)).pow 3).const_mul
        (1 / 6)).sub (hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 6)) using 1
      all_goals try rfl
      norm_num [hsqrt]
    have hderiv : HasDerivAt
        (fun r : ℝ => f ((((1 / 54), 2), 0), r)) 2 (Real.sqrt 6) := by
      convert hraw using 1 <;>
        norm_num [f, wallGMinus, wallADividedDiffPlus, wallB, wallC] <;> ring
    have hline : HasFDerivAt (fun r : ℝ => ((((1 / 54), 2), 0), r))
        (ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ) (Real.sqrt 6) := by
      fun_prop
    have hcomp :
        fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ =
          (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
      have hderiv' : HasFDerivAt
          (f ∘ fun r : ℝ => ((((1 / 54), 2), 0), r))
          ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (Real.sqrt 6) := by
        apply hderiv.hasFDerivAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro x
        simp
        ring
      exact (((hf.differentiableAt (by simp)).hasFDerivAt.comp (Real.sqrt 6) hline).unique
        hderiv')
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) (by norm_num)), by
      apply ContinuousLinearMap.ext
      intro x
      simp⟩
  let rMinus : ((ℝ × ℝ) × ℝ) → ℝ := hf.implicitFunction (by simp) hpartial
  have hrbase : rMinus (((1 / 54), 2), 0) = Real.sqrt 6 := by
    exact hf.implicitFunction_apply_self (by simp) hpartial
  have hranalytic : AnalyticAt ℝ rMinus (((1 / 54), 2), 0) := by
    exact (hf.contDiffAt_implicitFunction (by simp) hpartial).analyticAt
  have hroot : ∀ᶠ p in 𝓝 (((1 / 54), 2), 0),
      wallGMinus p.1.1 p.1.2 (1 / 2) p.2 (rMinus p) = 0 := by
    filter_upwards [hf.eventually_apply_implicitFunction (by simp) hpartial] with p hp
    change wallGMinus p.1.1 p.1.2 (1 / 2) p.2 (rMinus p) =
      wallGMinus (1 / 54) 2 (1 / 2) 0 (Real.sqrt 6) at hp
    simpa only [wallGMinus_base_sqrt6] using hp
  have hrcont : ContinuousAt rMinus (((1 / 54), 2), 0) := hranalytic.continuousAt
  have hrne : ∀ᶠ p in 𝓝 (((1 / 54), 2), 0), rMinus p ≠ 0 := by
    apply hrcont.eventually_ne
    rw [hrbase]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  let good : Set ((ℝ × ℝ) × ℝ) :=
    {p | wallGMinus p.1.1 p.1.2 (1 / 2) p.2 (rMinus p) = 0 ∧ rMinus p ≠ 0}
  let V : Set ((ℝ × ℝ) × ℝ) := interior good ∩ {p | AnalyticAt ℝ rMinus p}
  have hgood : ∀ᶠ p in 𝓝 (((1 / 54), 2), 0), p ∈ good := by
    filter_upwards [hroot, hrne] with p hp hnp
    exact ⟨hp, hnp⟩
  refine ⟨V, rMinus, ?_, ?_, ?_, hrbase, ?_, ?_⟩
  · exact isOpen_interior.inter (isOpen_analyticAt ℝ rMinus)
  · exact ⟨mem_interior_iff_mem_nhds.2 hgood, hranalytic⟩
  · intro p hp
    exact hp.2.contDiffAt.contDiffWithinAt
  · intro p hp
    exact (interior_subset hp.1).1
  · intro p hp
    exact (interior_subset hp.1).2

end ExoticCCR
