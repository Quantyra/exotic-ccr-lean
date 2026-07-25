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

open Filter MvPolynomial Set
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

/-- An open punctured domain on which the forward reconstruction formulas are
defined, together with the fact that it accumulates at the wall base. -/
structure ForwardBranchOpen where
  germ : ForwardBranchGerm
  W : Set ((ℝ × ℝ) × ℝ)
  isOpen_W : IsOpen W
  subset_V : W ⊆ germ.V
  tau_ne : ∀ p ∈ W, p.2 ≠ 0
  den_ne : ∀ p ∈ W,
    wallReconstructionDenom (germ.sCoord p) p.1.2 (germ.q0 p) ≠ 0
  nonempty_W : W.Nonempty
  nonempty_Wpos : (W ∩ {p | 0 < p.2}).Nonempty
  accumulates_base : ∀ U ∈ 𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ), (U ∩ W).Nonempty

/-- The forward branch germ admits an open positive punctured domain accumulating
at the wall base. -/
theorem exists_forwardBranchOpen : Nonempty ForwardBranchOpen := by
  obtain ⟨G⟩ := exists_forwardBranchGerm
  have hden := G.eventually_den_ne
  have hdenMem : {p : (ℝ × ℝ) × ℝ | p ∈ G.V → p.2 ≠ 0 →
      wallReconstructionDenom (G.sCoord p) p.1.2 (G.q0 p) ≠ 0} ∈
      𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ) := hden
  obtain ⟨N, hNsub, hNopen, hbaseN⟩ := mem_nhds_iff.mp hdenMem
  let W : Set ((ℝ × ℝ) × ℝ) := G.V ∩ N ∩ {p | 0 < p.2}
  have hWopen : IsOpen W := by
    exact (G.isOpen_V.inter hNopen).inter (isOpen_lt continuous_const continuous_snd)
  have hacc : ∀ U ∈ 𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ), (U ∩ W).Nonempty := by
    intro U hU
    have hnbhd : U ∩ (G.V ∩ N) ∈ 𝓝 (((0, 2), 0) : (ℝ × ℝ) × ℝ) :=
      inter_mem hU ((G.isOpen_V.inter hNopen).mem_nhds ⟨G.base_tau_mem, hbaseN⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
    let p : (ℝ × ℝ) × ℝ := ((0, 2), ε / 2)
    have hpball : p ∈ Metric.ball (((0, 2), 0) : (ℝ × ℝ) × ℝ) ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp [p, abs_of_pos hε]
      linarith
    have hpUN : p ∈ U ∩ (G.V ∩ N) := hball hpball
    refine ⟨p, hpUN.1, hpUN.2, ?_⟩
    dsimp [p]
    linarith
  refine ⟨⟨G, W, hWopen, ?_, ?_, ?_, ?_, ?_, hacc⟩⟩
  · intro p hp
    exact hp.1.1
  · intro p hp
    exact ne_of_gt hp.2
  · intro p hp
    exact hNsub hp.1.2 hp.1.1 (ne_of_gt hp.2)
  · exact hacc Set.univ univ_mem |>.mono fun _ hp ↦ hp.2
  · exact hacc Set.univ univ_mem |>.mono fun _ hp ↦ ⟨hp.2, hp.2.2⟩

/-- The branch reconstruction is smooth on its open punctured domain. -/
theorem ForwardBranchOpen.contDiff_branchMap (O : ForwardBranchOpen) :
    ContDiffOn ℝ ⊤ (fun p => O.germ.branchMap p) O.W := by
  intro p hp
  have hpV := O.subset_V hp
  have hpU := O.germ.proj_mem p hpV
  have hβ : ContDiffAt ℝ ⊤ O.germ.β p.1 :=
    O.germ.contDiff_β.contDiffAt (O.germ.isOpen_U.mem_nhds hpU)
  have hr : ContDiffAt ℝ ⊤ O.germ.rPlus p :=
    O.germ.contDiff_rPlus.contDiffAt (O.germ.isOpen_V.mem_nhds hpV)
  have hτ := O.tau_ne p hp
  have hden := O.den_ne p hp
  have hq0 : O.germ.q0 p ≠ 0 := div_ne_zero (O.germ.rPlus_ne p hpV) hτ
  have hs : ContDiffAt ℝ ⊤ (fun p => O.germ.sCoord p) p := by
    unfold ForwardBranchGerm.sCoord
    fun_prop
  have hq : ContDiffAt ℝ ⊤ (fun p => O.germ.q0 p) p := by
    unfold ForwardBranchGerm.q0
    fun_prop
  have hq1 : ContDiffAt ℝ ⊤ (fun p => wallReconstructQ1 p.1.1
      (O.germ.sCoord p) p.1.2 (O.germ.q0 p)) p := by
    have hden' : O.germ.q0 p *
        ((3 * p.1.2 * O.germ.sCoord p - 4) * O.germ.q0 p + 3 * p.1.2) ≠ 0 := by
      simpa [wallReconstructionDenom, wallB] using hden
    unfold wallReconstructQ1 wallReconstructionDenom wallB
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact hden'
  have hq2 : ContDiffAt ℝ ⊤ (fun p => wallReconstructQ2 p.1.1
      (O.germ.sCoord p) p.1.2 (O.germ.q0 p)) p := by
    unfold wallReconstructQ2
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero 3 hq0
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · simpa [ForwardBranchGerm.branchMap, wallReconstruction] using hq
  · simpa [ForwardBranchGerm.branchMap, wallReconstruction] using hq1
  · simpa [ForwardBranchGerm.branchMap, wallReconstruction] using hq2

/-- Evaluation of the polynomial anchor recovers the branch target coordinates. -/
theorem ForwardBranchOpen.evalMap_branch (O : ForwardBranchOpen)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ O.W) :
    evalMap (F ℝ) (O.germ.branchMap p) =
      ![p.1.1, O.germ.sCoord p, p.1.2] :=
  O.germ.evalMap_branch (O.subset_V hp) (O.tau_ne p hp) (O.den_ne p hp)

/-- The positive part of a punctured branch domain. -/
def ForwardBranchOpen.Wpos (O : ForwardBranchOpen) : Set ((ℝ × ℝ) × ℝ) :=
  O.W ∩ {p | 0 < p.2}

/-- The first coordinate of the reconstruction is the divided branch root. -/
theorem ForwardBranchOpen.branchMap_coord0_eq_q0 (O : ForwardBranchOpen)
    (p : (ℝ × ℝ) × ℝ) : O.germ.branchMap p 0 = O.germ.q0 p := by
  rfl

/-- The forward reconstruction is injective on the positive punctured sheet. -/
theorem ForwardBranchOpen.branchMap_injOn_Wpos (O : ForwardBranchOpen) :
    Set.InjOn O.germ.branchMap O.Wpos := by
  intro p hp q hq hpq
  have htargets := congrArg (evalMap (F ℝ)) hpq
  rw [O.evalMap_branch hp.1, O.evalMap_branch hq.1] at htargets
  have ha : p.1.1 = q.1.1 := by
    simpa using congrFun htargets (0 : Fin 3)
  have hs : O.germ.sCoord p = O.germ.sCoord q := by
    simpa using congrFun htargets (1 : Fin 3)
  have hc : p.1.2 = q.1.2 := by
    simpa using congrFun htargets (2 : Fin 3)
  have hpq1 : p.1 = q.1 := Prod.ext ha hc
  have hτ : p.2 = q.2 := by
    have hppos : 0 < p.2 := hp.2
    have hqpos : 0 < q.2 := hq.2
    unfold ForwardBranchGerm.sCoord at hs
    rw [hpq1] at hs
    have hsq : p.2 ^ 2 = q.2 ^ 2 := by linarith
    have hfac : (p.2 - q.2) * (p.2 + q.2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · nlinarith [hppos, hqpos]
  exact Prod.ext hpq1 hτ

/-- Along the positive sheet, the first reconstruction coordinate diverges as
the wall base is approached. -/
theorem ForwardBranchOpen.tendsto_q0_atTop (O : ForwardBranchOpen) :
    Tendsto O.germ.q0 (𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ)) atTop := by
  have hτ0 : Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2)
      (𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ)) (𝓝 0) :=
    continuousAt_snd.tendsto.mono_left inf_le_left
  have hτpos : ∀ᶠ p in 𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ), 0 < p.2 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.2
  have hτGT : Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2)
      (𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ)) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hτ0, hτpos⟩
  have hinv : Tendsto (fun p : (ℝ × ℝ) × ℝ => (p.2)⁻¹)
      (𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ)) atTop :=
    hτGT.inv_tendsto_nhdsGT_zero
  have hr : Tendsto O.germ.rPlus
      (𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ)) (𝓝 (Real.sqrt 2)) := by
    simpa [O.germ.rPlus_base] using
      (O.germ.contDiff_rPlus.contDiffAt
        (O.germ.isOpen_V.mem_nhds O.germ.base_tau_mem)).continuousAt.tendsto.mono_left
          (show 𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ) ≤ 𝓝 ((0, 2), 0) from inf_le_left)
  have hrge : ∀ᶠ p in 𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ), 1 ≤ O.germ.rPlus p := by
    have hsqrt : 1 < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    apply hr
    exact Ici_mem_nhds hsqrt
  apply tendsto_atTop_mono' _ _ hinv
  filter_upwards [hτpos, hrge] with p hp hpr
  rw [ForwardBranchGerm.q0, div_eq_mul_inv]
  have hi : 0 ≤ (p.2)⁻¹ := le_of_lt (inv_pos.2 hp)
  nlinarith

/-- The absolute first coordinate also diverges on approach to the wall. -/
theorem ForwardBranchOpen.tendsto_abs_q0_atTop (O : ForwardBranchOpen) :
    Tendsto (fun p => |O.germ.q0 p|)
      (𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ)) atTop := by
  apply tendsto_atTop_mono' _ _ O.tendsto_q0_atTop
  filter_upwards with p
  exact le_abs_self (O.germ.q0 p)

/-- The reconstructed branch escapes every norm ball at the wall base. -/
theorem ForwardBranchOpen.tendsto_norm_branchMap_at_base (O : ForwardBranchOpen) :
    Tendsto (fun p => ‖O.germ.branchMap p‖)
      (𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ)) atTop := by
  apply tendsto_atTop_mono' _ _ O.tendsto_abs_q0_atTop
  filter_upwards with p
  rw [← O.branchMap_coord0_eq_q0 p, Pi.norm_def]
  exact_mod_cast Finset.le_sup (f := fun b ↦ ‖O.germ.branchMap p b‖₊)
    (Finset.mem_univ (0 : Fin 3))

/-- Near the wall base within the positive sheet, the escaping reconstruction
eventually avoids every compact subset of the ambient space. -/
theorem ForwardBranchOpen.eventually_branchMap_not_mem_compact
    (O : ForwardBranchOpen) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    ∀ᶠ p in 𝓝[O.Wpos] (((0, 2), 0) : (ℝ × ℝ) × ℝ),
      O.germ.branchMap p ∉ K := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  filter_upwards [O.tendsto_norm_branchMap_at_base (Ioi_mem_atTop C)] with p hp
  intro hpK
  exact (not_le_of_gt hp) (hC _ hpK)

end ExoticCCR
