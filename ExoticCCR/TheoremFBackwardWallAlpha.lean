/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardReconstruction

/-!
# Local smooth germ for the A001 backward wall

This module constructs the local smooth backward-wall germ through
`((1/54, 2), 1/2)`. It makes no global-sheet or deficiency claim.
-/

noncomputable section

open MvPolynomial
open scoped ContDiff Topology

namespace ExoticCCR

/-- Local smooth backward-wall function near `(1/54, 2)`. -/
theorem exists_backwardWallAlpha_germ :
    ∃ (U : Set (ℝ × ℝ)) (alpha : ℝ × ℝ → ℝ),
      IsOpen U ∧
      ((1 / 54), 2) ∈ U ∧
      ContDiffOn ℝ ⊤ alpha U ∧
      alpha ((1 / 54), 2) = (1 / 2 : ℝ) ∧
      (∀ p ∈ U, wallA p.1 (alpha p) p.2 = 0) ∧
      (∀ p ∈ U, wallADerivS p.1 (alpha p) p.2 ≠ 0) := by
  let f : (ℝ × ℝ) × ℝ → ℝ := fun p => wallA p.1.1 p.2 p.1.2
  let u : (ℝ × ℝ) × ℝ := (((1 / 54), 2), 1 / 2)
  have hf : ContDiffAt ℝ ω f u := by
    apply contDiff_wallA.contDiffAt
  have hpartial : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    have hpoly : HasDerivAt
        (fun s : ℝ => -2 * s ^ 3 + s ^ 2 + (2 / 3) * s - 1 / 3) (1 / 6) (1 / 2) := by
      convert (((((hasDerivAt_id (𝕜 := ℝ) (1 / 2)).pow 3).const_mul (-2)).add
        ((hasDerivAt_id (𝕜 := ℝ) (1 / 2)).pow 2)).add
          ((hasDerivAt_id (𝕜 := ℝ) (1 / 2)).const_mul (2 / 3))).sub
            (hasDerivAt_const (x := (1 / 2 : ℝ)) (c := (1 / 3 : ℝ))) using 1 <;> try rfl
      norm_num
    have hderiv : HasDerivAt (fun s : ℝ => f (((1 / 54), 2), s)) (1 / 6) (1 / 2) := by
      convert hpoly using 1 <;> norm_num [f, wallA] <;> ring
    have hcomp :
        fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ =
          ((1 / 6 : ℝ)) • ContinuousLinearMap.id ℝ ℝ := by
      have hline : HasFDerivAt (fun s : ℝ => (((1 / 54), 2), s))
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) (1 / 2) := by
        fun_prop
      have hderiv' : HasFDerivAt (f ∘ fun s : ℝ => (((1 / 54), 2), s))
          ((1 / 6 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (1 / 2) := by
        apply hderiv.hasFDerivAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro x
        simp
        ring
      exact (((hf.differentiableAt (by simp)).hasFDerivAt.comp (1 / 2) hline).unique
        hderiv')
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 (1 / 6 : ℝ) (by norm_num)), by
      apply ContinuousLinearMap.ext
      intro x
      simp⟩
  let alpha : ℝ × ℝ → ℝ := hf.implicitFunction (by simp) hpartial
  have halphaBase : alpha ((1 / 54), 2) = (1 / 2 : ℝ) := by
    exact hf.implicitFunction_apply_self (by simp) hpartial
  have halphaAnalytic : AnalyticAt ℝ alpha ((1 / 54), 2) := by
    exact (hf.contDiffAt_implicitFunction (by simp) hpartial).analyticAt
  have hwall : ∀ᶠ p in 𝓝 ((1 / 54), 2), wallA p.1 (alpha p) p.2 = 0 := by
    filter_upwards [hf.eventually_apply_implicitFunction (by simp) hpartial] with p hp
    change wallA p.1 (alpha p) p.2 = wallA (1 / 54) (1 / 2) 2 at hp
    simpa only [wallA_backward_basePoint] using hp
  have hderivCont : ContinuousAt
      (fun p => wallADerivS p.1 (alpha p) p.2) ((1 / 54), 2) := by
    unfold wallADerivS
    fun_prop
  have hderiv : ∀ᶠ p in 𝓝 ((1 / 54), 2), wallADerivS p.1 (alpha p) p.2 ≠ 0 := by
    apply hderivCont.eventually_ne
    rw [halphaBase, wallADerivS_backward_basePoint]
    norm_num
  let good : Set (ℝ × ℝ) :=
    {p | wallA p.1 (alpha p) p.2 = 0 ∧ wallADerivS p.1 (alpha p) p.2 ≠ 0}
  let U : Set (ℝ × ℝ) := interior good ∩ {p | AnalyticAt ℝ alpha p}
  have hgood : ∀ᶠ p in 𝓝 ((1 / 54), 2), p ∈ good := by
    filter_upwards [hwall, hderiv] with p hp hdp
    exact ⟨hp, hdp⟩
  refine ⟨U, alpha, ?_, ?_, ?_, halphaBase, ?_, ?_⟩
  · exact isOpen_interior.inter (isOpen_analyticAt ℝ alpha)
  · refine ⟨mem_interior_iff_mem_nhds.2 ?_, halphaAnalytic⟩
    exact hgood
  · intro p hp
    exact hp.2.contDiffAt.contDiffWithinAt
  · intro p hp
    exact (interior_subset hp.1).1
  · intro p hp
    exact (interior_subset hp.1).2

end ExoticCCR
