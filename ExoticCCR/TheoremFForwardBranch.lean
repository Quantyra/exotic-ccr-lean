/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardWall

/-!
# Base slice for the A001 forward branch

This module records the smooth divided-difference extension of the forward
`G+` equation, constructs its fixed-height local positive-root germ, and links
nonzero germ points satisfying the wall equation to algebraic reconstruction.
-/

noncomputable section

open MvPolynomial
open scoped ContDiff Topology

namespace ExoticCCR

/-- The polynomial extension of the quotient obtained by moving from `β` to
`β - τ²` in the forward-wall polynomial. -/
def wallADividedDiff (a β c τ : ℝ) : ℝ :=
  3 * c * β ^ 2 - 3 * c * β * τ ^ 2 + c * τ ^ 4 - 2 * β + τ ^ 2 - 18 * a * c

/-- The finite difference of `wallA` factors by `τ²` without a piecewise definition. -/
theorem wallA_sub_eq_tau2_mul_dividedDiff (a β c τ : ℝ) :
    wallA a (β - τ ^ 2) c - wallA a β c =
      τ ^ 2 * wallADividedDiff a β c τ := by
  simp [wallA, wallADividedDiff]
  ring

/-- At `τ = 0`, the divided difference is minus the wall derivative. -/
theorem wallADividedDiff_zero (a β c : ℝ) :
    wallADividedDiff a β c 0 = -wallADerivS a β c := by
  simp [wallADividedDiff, wallADerivS]
  ring

/-- The divided-difference extension is smooth in all four variables. -/
theorem contDiff_wallADividedDiff :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      wallADividedDiff p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold wallADividedDiff
  fun_prop

/-- On the wall, the nonzero-`τ` quotient equals its polynomial extension. -/
theorem wallA_div_tau2_eq_dividedDiff {a β c τ : ℝ}
    (hτ : τ ≠ 0) (hwall : wallA a β c = 0) :
    wallA a (β - τ ^ 2) c / τ ^ 2 = wallADividedDiff a β c τ := by
  have h := wallA_sub_eq_tau2_mul_dividedDiff a β c τ
  rw [hwall, sub_zero] at h
  rw [h]
  field_simp

/-- The smooth extended forward equation before dividing the root by `τ`. -/
def wallGPlus (a c β τ r : ℝ) : ℝ :=
  wallADividedDiff a β c τ * r ^ 3 + wallB (β - τ ^ 2) c * r + wallC c * τ

/-- The extended forward equation is smooth in its five scalar variables. -/
theorem contDiff_wallGPlus :
    ContDiff ℝ ⊤ (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ =>
      wallGPlus p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2) := by
  unfold wallGPlus wallADividedDiff wallB wallC
  fun_prop

/-- The continuous wall value of the cubic part of the forward `G+` equation. -/
def wallGPlusAtWall (As B r : ℝ) : ℝ :=
  (-As) * r ^ 3 + B * r

/-- The wall-value cubic is smooth in its coefficients and root variable. -/
theorem contDiff_wallGPlusAtWall :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ℝ => wallGPlusAtWall p.1.1 p.1.2 p.2) := by
  unfold wallGPlusAtWall
  fun_prop

/-- The positive large-`q₀` branch base value is a root of the wall cubic. -/
theorem wallGPlus_base_sqrt2 :
    wallGPlusAtWall (-(1 / 2)) (-1) (Real.sqrt 2) = 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  unfold wallGPlusAtWall
  rw [show (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt]]
  ring

/-- The smooth extended equation has the positive base root. -/
theorem wallGPlus_base :
    wallGPlus 0 2 (1 / 2) 0 (Real.sqrt 2) = 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  simp [wallGPlus, wallADividedDiff, wallB, wallC]
  rw [show (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 by
    calc
      (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrt]]
  ring

/-- The root derivative is nonzero at the positive branch base value. -/
theorem wallGPlus_base_deriv_ne :
    deriv (fun r => wallGPlusAtWall (-1 / 2) (-1) r) (Real.sqrt 2) ≠ 0 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  have hderiv :
      HasDerivAt (fun r : ℝ => wallGPlusAtWall (-1 / 2) (-1) r) 2
        (Real.sqrt 2) := by
    have hraw := (((hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2)).pow 3).const_mul
      (1 / 2)).sub (hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2))
    have hfun :
        (fun r : ℝ => wallGPlusAtWall (-1 / 2) (-1) r) =
          fun r : ℝ => (1 / 2) * r ^ 3 - r := by
      funext r
      simp [wallGPlusAtWall]
      ring
    rw [hfun]
    convert hraw using 1
    all_goals try rfl
    norm_num [hsqrt]
  rw [hderiv.deriv]
  norm_num

/-- The partial derivative in the root variable is nonzero at the base point. -/
theorem wallGPlus_base_partial_r_ne :
    deriv (fun r => wallGPlus 0 2 (1 / 2) 0 r) (Real.sqrt 2) ≠ 0 := by
  have hfun :
      (fun r : ℝ => wallGPlus 0 2 (1 / 2) 0 r) =
        fun r : ℝ => wallGPlusAtWall (-1 / 2) (-1) r := by
    funext r
    simp [wallGPlus, wallADividedDiff, wallGPlusAtWall, wallB, wallC]
    ring
  rw [hfun]
  exact wallGPlus_base_deriv_ne

/-- A local smooth positive-root model at the fixed base wall height `β = 1/2`. -/
theorem exists_forwardBranchR_germ :
    ∃ (V : Set ((ℝ × ℝ) × ℝ)) (rPlus : ((ℝ × ℝ) × ℝ) → ℝ),
      IsOpen V ∧
      ((0, 2), 0) ∈ V ∧
      ContDiffOn ℝ ⊤ rPlus V ∧
      rPlus ((0, 2), 0) = Real.sqrt 2 ∧
      (∀ p ∈ V, wallGPlus p.1.1 p.1.2 (1 / 2) p.2 (rPlus p) = 0) ∧
      (∀ p ∈ V, rPlus p ≠ 0) := by
  let f : (((ℝ × ℝ) × ℝ) × ℝ) → ℝ := fun p =>
    wallGPlus p.1.1.1 p.1.1.2 (1 / 2) p.1.2 p.2
  let u : (((ℝ × ℝ) × ℝ) × ℝ) := (((0, 2), 0), Real.sqrt 2)
  have hf : ContDiffAt ℝ ω f u := by
    unfold f wallGPlus wallADividedDiff wallB wallC
    fun_prop
  have hpartial :
      (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ).IsInvertible := by
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
    have hraw : HasDerivAt (fun r : ℝ => (1 / 2) * r ^ 3 - r) 2 (Real.sqrt 2) := by
      convert (((hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2)).pow 3).const_mul
        (1 / 2)).sub (hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2)) using 1
      all_goals try rfl
      norm_num [hsqrt]
    have hderiv : HasDerivAt (fun r : ℝ => f (((0, 2), 0), r)) 2 (Real.sqrt 2) := by
      convert hraw using 1 <;> norm_num [f, wallGPlus, wallADividedDiff, wallB, wallC] <;>
        ring
    have hline : HasFDerivAt (fun r : ℝ => (((0, 2), 0), r))
        (ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ) (Real.sqrt 2) := by
      fun_prop
    have hcomp :
        fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ =
          (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
      have hderiv' : HasFDerivAt (f ∘ fun r : ℝ => (((0, 2), 0), r))
          ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (Real.sqrt 2) := by
        apply hderiv.hasFDerivAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro x
        simp
        ring
      exact (((hf.differentiableAt (by simp)).hasFDerivAt.comp (Real.sqrt 2) hline).unique
        hderiv')
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) (by norm_num)), by
      apply ContinuousLinearMap.ext
      intro x
      simp⟩
  let rPlus : ((ℝ × ℝ) × ℝ) → ℝ := hf.implicitFunction (by simp) hpartial
  have hrbase : rPlus ((0, 2), 0) = Real.sqrt 2 := by
    exact hf.implicitFunction_apply_self (by simp) hpartial
  have hranalytic : AnalyticAt ℝ rPlus ((0, 2), 0) := by
    exact (hf.contDiffAt_implicitFunction (by simp) hpartial).analyticAt
  have hroot : ∀ᶠ p in 𝓝 ((0, 2), 0),
      wallGPlus p.1.1 p.1.2 (1 / 2) p.2 (rPlus p) = 0 := by
    filter_upwards [hf.eventually_apply_implicitFunction (by simp) hpartial] with p hp
    change wallGPlus p.1.1 p.1.2 (1 / 2) p.2 (rPlus p) =
      wallGPlus 0 2 (1 / 2) 0 (Real.sqrt 2) at hp
    simpa only [wallGPlus_base] using hp
  have hrcont : ContinuousAt rPlus ((0, 2), 0) := hranalytic.continuousAt
  have hrne : ∀ᶠ p in 𝓝 ((0, 2), 0), rPlus p ≠ 0 := by
    apply hrcont.eventually_ne
    rw [hrbase]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  let good : Set ((ℝ × ℝ) × ℝ) :=
    {p | wallGPlus p.1.1 p.1.2 (1 / 2) p.2 (rPlus p) = 0 ∧ rPlus p ≠ 0}
  let V : Set ((ℝ × ℝ) × ℝ) := interior good ∩ {p | AnalyticAt ℝ rPlus p}
  have hgood : ∀ᶠ p in 𝓝 ((0, 2), 0), p ∈ good := by
    filter_upwards [hroot, hrne] with p hp hnp
    exact ⟨hp, hnp⟩
  refine ⟨V, rPlus, ?_, ?_, ?_, hrbase, ?_, ?_⟩
  · exact isOpen_interior.inter (isOpen_analyticAt ℝ rPlus)
  · exact ⟨mem_interior_iff_mem_nhds.2 hgood, hranalytic⟩
  · intro p hp
    exact hp.2.contDiffAt.contDiffWithinAt
  · intro p hp
    exact (interior_subset hp.1).1
  · intro p hp
    exact (interior_subset hp.1).2

/-- The local varying-wall forward branch through `((0,2),0,√2)`. -/
structure ForwardBranchGerm where
  U : Set (ℝ × ℝ)
  isOpen_U : IsOpen U
  base_mem : (0, 2) ∈ U
  β : ℝ × ℝ → ℝ
  contDiff_β : ContDiffOn ℝ ⊤ β U
  β_base : β (0, 2) = 1 / 2
  wall_eq : ∀ p ∈ U, wallA p.1 (β p) p.2 = 0
  wallADeriv_ne : ∀ p ∈ U, wallADerivS p.1 (β p) p.2 ≠ 0
  V : Set ((ℝ × ℝ) × ℝ)
  isOpen_V : IsOpen V
  base_tau_mem : ((0, 2), 0) ∈ V
  rPlus : ((ℝ × ℝ) × ℝ) → ℝ
  contDiff_rPlus : ContDiffOn ℝ ⊤ rPlus V
  rPlus_base : rPlus ((0, 2), 0) = Real.sqrt 2
  proj_mem : ∀ p ∈ V, p.1 ∈ U
  G_eq : ∀ p ∈ V, wallGPlus p.1.1 p.1.2 (β p.1) p.2 (rPlus p) = 0
  rPlus_ne : ∀ p ∈ V, rPlus p ≠ 0

/-- The smooth forward-wall germ and the root IFT compose to give a local
varying-`β` forward branch. -/
theorem exists_forwardBranchGerm : Nonempty ForwardBranchGerm := by
  obtain ⟨U, β, hU, hbase, hβ, hβbase, hwall, hwallDeriv⟩ :=
    exists_forwardWallBeta_germ
  let f : (((ℝ × ℝ) × ℝ) × ℝ) → ℝ := fun p =>
    wallGPlus p.1.1.1 p.1.1.2 (β p.1.1) p.1.2 p.2
  let u : (((ℝ × ℝ) × ℝ) × ℝ) := (((0, 2), 0), Real.sqrt 2)
  have hβat : ContDiffAt ℝ ⊤ β (0, 2) := hβ.contDiffAt (hU.mem_nhds hbase)
  have hf : ContDiffAt ℝ ω f u := by
    unfold f wallGPlus wallADividedDiff wallB wallC
    fun_prop
  have hpartial :
      (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ).IsInvertible := by
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
    have hraw : HasDerivAt (fun r : ℝ => (1 / 2) * r ^ 3 - r) 2 (Real.sqrt 2) := by
      convert (((hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2)).pow 3).const_mul
        (1 / 2)).sub (hasDerivAt_id (𝕜 := ℝ) (Real.sqrt 2)) using 1
      all_goals try rfl
      norm_num [hsqrt]
    have hderiv : HasDerivAt (fun r : ℝ => f (((0, 2), 0), r)) 2
        (Real.sqrt 2) := by
      convert hraw using 1 <;>
        norm_num [f, hβbase, wallGPlus, wallADividedDiff, wallB, wallC] <;> ring
    have hline : HasFDerivAt (fun r : ℝ => (((0, 2), 0), r))
        (ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ) (Real.sqrt 2) := by
      fun_prop
    have hcomp :
        fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ ((ℝ × ℝ) × ℝ) ℝ =
          (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
      have hderiv' : HasFDerivAt (f ∘ fun r : ℝ => (((0, 2), 0), r))
          ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (Real.sqrt 2) := by
        apply hderiv.hasFDerivAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro x
        simp
        ring
      exact (((hf.differentiableAt (by simp)).hasFDerivAt.comp (Real.sqrt 2) hline).unique
        hderiv')
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) (by norm_num)), by
      apply ContinuousLinearMap.ext
      intro x
      simp⟩
  let rPlus : ((ℝ × ℝ) × ℝ) → ℝ := hf.implicitFunction (by simp) hpartial
  have hrbase : rPlus ((0, 2), 0) = Real.sqrt 2 := by
    exact hf.implicitFunction_apply_self (by simp) hpartial
  have hranalytic : AnalyticAt ℝ rPlus ((0, 2), 0) := by
    exact (hf.contDiffAt_implicitFunction (by simp) hpartial).analyticAt
  have hroot : ∀ᶠ p in 𝓝 ((0, 2), 0),
      wallGPlus p.1.1 p.1.2 (β p.1) p.2 (rPlus p) = 0 := by
    filter_upwards [hf.eventually_apply_implicitFunction (by simp) hpartial] with p hp
    change wallGPlus p.1.1 p.1.2 (β p.1) p.2 (rPlus p) =
      wallGPlus 0 2 (β (0, 2)) 0 (Real.sqrt 2) at hp
    simpa only [hβbase, wallGPlus_base] using hp
  have hrcont : ContinuousAt rPlus ((0, 2), 0) := hranalytic.continuousAt
  have hrne : ∀ᶠ p in 𝓝 ((0, 2), 0), rPlus p ≠ 0 := by
    apply hrcont.eventually_ne
    rw [hrbase]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hproj : ∀ᶠ p in 𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ), p.1 ∈ U := by
    have ht : Filter.Tendsto (fun p : (ℝ × ℝ) × ℝ => p.1)
        (𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ)) (𝓝 ((0, 2) : ℝ × ℝ)) :=
      continuousAt_fst
    exact ht.eventually (hU.mem_nhds hbase)
  let good : Set ((ℝ × ℝ) × ℝ) :=
    {p | wallGPlus p.1.1 p.1.2 (β p.1) p.2 (rPlus p) = 0 ∧
      rPlus p ≠ 0 ∧ p.1 ∈ U}
  let V : Set ((ℝ × ℝ) × ℝ) := interior good ∩ {p | AnalyticAt ℝ rPlus p}
  have hgood : ∀ᶠ p in 𝓝 ((0, 2), 0), p ∈ good := by
    filter_upwards [hroot, hrne, hproj] with p hp hnp hpu
    exact ⟨hp, hnp, hpu⟩
  refine ⟨⟨U, hU, hbase, β, hβ, hβbase, hwall, hwallDeriv,
    V, ?_, ?_, rPlus, ?_, hrbase, ?_, ?_, ?_⟩⟩
  · exact isOpen_interior.inter (isOpen_analyticAt ℝ rPlus)
  · exact ⟨mem_interior_iff_mem_nhds.2 hgood, hranalytic⟩
  · intro p hp
    exact hp.2.contDiffAt.contDiffWithinAt
  · intro p hp
    exact (interior_subset hp.1).2.2
  · intro p hp
    exact (interior_subset hp.1).1
  · intro p hp
    exact (interior_subset hp.1).2.1

/-- A nonzero extended root on the wall gives a root of the original reconstruction cubic. -/
theorem wallCubic_of_wallGPlus {a β c τ r : ℝ} (hτ : τ ≠ 0)
    (hwall : wallA a β c = 0) (hG : wallGPlus a c β τ r = 0) :
    wallCubic a (β - τ ^ 2) c (r / τ) = 0 := by
  have hA := wallA_sub_eq_tau2_mul_dividedDiff a β c τ
  rw [hwall, sub_zero] at hA
  unfold wallGPlus at hG
  unfold wallCubic
  rw [hA]
  field_simp [hτ] at ⊢
  nlinarith

/-- A nonzero point of an extended-root branch reconstructs a preimage whenever
the wall and displayed denominator hypotheses hold. -/
theorem evalMap_F_wallReconstruction_of_wallGPlus
    {a β c τ r : ℝ} (hτ : τ ≠ 0) (hr : r ≠ 0)
    (hwall : wallA a β c = 0) (hG : wallGPlus a c β τ r = 0)
    (hden : wallReconstructionDenom (β - τ ^ 2) c (r / τ) ≠ 0) :
    evalMap (F ℝ) (wallReconstruction a (β - τ ^ 2) c (r / τ)) =
      ![a, β - τ ^ 2, c] := by
  apply evalMap_F_wallReconstruction (div_ne_zero hr hτ) hden
  exact wallCubic_of_wallGPlus hτ hwall hG

/-- The reconstruction conclusion specialized to a nonzero-`τ` point of the
fixed-height local branch model. -/
theorem evalMap_F_wallReconstruction_on_forwardBranch
    {V : Set ((ℝ × ℝ) × ℝ)} {rPlus : ((ℝ × ℝ) × ℝ) → ℝ}
    {p : (ℝ × ℝ) × ℝ}
    (hbranch : ∀ q ∈ V, wallGPlus q.1.1 q.1.2 (1 / 2) q.2 (rPlus q) = 0)
    (hrne : ∀ q ∈ V, rPlus q ≠ 0) (hp : p ∈ V) (hτ : p.2 ≠ 0)
    (hwall : wallA p.1.1 (1 / 2) p.1.2 = 0)
    (hden : wallReconstructionDenom ((1 / 2) - p.2 ^ 2) p.1.2
      (rPlus p / p.2) ≠ 0) :
    evalMap (F ℝ) (wallReconstruction p.1.1 ((1 / 2) - p.2 ^ 2) p.1.2
      (rPlus p / p.2)) = ![p.1.1, (1 / 2) - p.2 ^ 2, p.1.2] := by
  exact evalMap_F_wallReconstruction_of_wallGPlus hτ (hrne p hp) hwall
    (hbranch p hp) hden

/-- The target `s` coordinate along a varying-wall forward branch. -/
def ForwardBranchGerm.sCoord (G : ForwardBranchGerm) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  G.β p.1 - p.2 ^ 2

/-- The first reconstruction coordinate away from `τ = 0`. -/
def ForwardBranchGerm.q0 (G : ForwardBranchGerm) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  G.rPlus p / p.2

/-- The explicit local reconstruction map away from its displayed denominators. -/
def ForwardBranchGerm.branchMap (G : ForwardBranchGerm)
    (p : (ℝ × ℝ) × ℝ) : Fin 3 → ℝ :=
  wallReconstruction p.1.1 (G.sCoord p) p.1.2 (G.q0 p)

/-- A punctured point of the local branch reconstructs its varying-wall target
whenever the explicit reconstruction denominator is nonzero. -/
theorem ForwardBranchGerm.evalMap_branch
    (G : ForwardBranchGerm) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ G.V) (hτ : p.2 ≠ 0)
    (hden : wallReconstructionDenom (G.sCoord p) p.1.2 (G.q0 p) ≠ 0) :
    evalMap (F ℝ) (G.branchMap p) = ![p.1.1, G.sCoord p, p.1.2] := by
  exact evalMap_F_wallReconstruction_of_wallGPlus hτ (G.rPlus_ne p hp)
    (G.wall_eq p.1 (G.proj_mem p hp)) (G.G_eq p hp) hden

/-- Sufficiently near the base, every punctured point of the branch domain has
nonzero reconstruction denominator. -/
theorem ForwardBranchGerm.eventually_den_ne (G : ForwardBranchGerm) :
    ∀ᶠ p in 𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ), p ∈ G.V → p.2 ≠ 0 →
      wallReconstructionDenom (G.sCoord p) p.1.2 (G.q0 p) ≠ 0 := by
  let k : ((ℝ × ℝ) × ℝ) → ℝ := fun p =>
    wallB (G.sCoord p) p.1.2 * G.rPlus p + 3 * p.1.2 * p.2
  have hβat : ContDiffAt ℝ ⊤ G.β (0, 2) :=
    G.contDiff_β.contDiffAt (G.isOpen_U.mem_nhds G.base_mem)
  have hrat : ContDiffAt ℝ ⊤ G.rPlus ((0, 2), 0) :=
    G.contDiff_rPlus.contDiffAt (G.isOpen_V.mem_nhds G.base_tau_mem)
  have hkcont : ContinuousAt k ((0, 2), 0) := by
    unfold k ForwardBranchGerm.sCoord wallB
    fun_prop
  have hkbase : k ((0, 2), 0) ≠ 0 := by
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    norm_num [k, ForwardBranchGerm.sCoord, G.β_base, G.rPlus_base, wallB, hsqrt]
  filter_upwards [hkcont.eventually_ne hkbase] with p hkp hp hτ
  have hx : G.q0 p ≠ 0 := div_ne_zero (G.rPlus_ne p hp) hτ
  have hkrel :
      k p = p.2 * (wallB (G.sCoord p) p.1.2 * G.q0 p + 3 * p.1.2) := by
    simp [k, ForwardBranchGerm.q0]
    field_simp [hτ]
  have hfactor : wallB (G.sCoord p) p.1.2 * G.q0 p + 3 * p.1.2 ≠ 0 := by
    intro hz
    apply hkp
    rw [hkrel, hz, mul_zero]
  exact mul_ne_zero hx hfactor

end ExoticCCR
