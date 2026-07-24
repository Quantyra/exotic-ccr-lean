/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.AnchorF
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Algebraic base point for the A001 forward wall

This module records the cubic and its base-point identities, constructs the
local smooth forward-wall germ, and proves the algebraic wall reconstruction.
It does not construct a deficiency vector.
-/

noncomputable section

open MvPolynomial
open scoped ContDiff Topology

namespace ExoticCCR

/-- The forward-wall cubic from the A001 calculation. -/
def wallA (a s c : ℝ) : ℝ :=
  -c * s ^ 3 + s ^ 2 + 18 * a * c * s - 27 * a ^ 2 * c ^ 2 - 16 * a

/-- The formal partial derivative of `wallA` in its `s` variable. -/
def wallADerivS (a s c : ℝ) : ℝ :=
  -3 * c * s ^ 2 + 2 * s + 18 * a * c

/-- The linear coefficient in the reconstruction cubic. -/
def wallB (s c : ℝ) : ℝ :=
  3 * c * s - 4

/-- The constant coefficient in the reconstruction cubic. -/
def wallC (c : ℝ) : ℝ :=
  2 * c

/-- The cubic equation obeyed by the first reconstruction coordinate. -/
def wallCubic (a s c x : ℝ) : ℝ :=
  wallA a s c * x ^ 3 + wallB s c * x + wallC c

/-- The denominator in the formula for the second reconstruction coordinate. -/
def wallReconstructionDenom (s c x : ℝ) : ℝ :=
  x * (wallB s c * x + 3 * c)

/-- The second coordinate in the algebraic reconstruction of a preimage of `(a,s,c)`. -/
def wallReconstructQ1 (a s c x : ℝ) : ℝ :=
  (9 * a * c * x ^ 2 - 3 * c * s * x - 3 * c - s * x ^ 2 + 6 * x) /
    wallReconstructionDenom s c x

/-- The third coordinate in the algebraic reconstruction of a preimage of `(a,s,c)`. -/
def wallReconstructQ2 (a s c x : ℝ) : ℝ :=
  (2 * x - 3 * x ^ 2 * wallReconstructQ1 a s c x - c) / x ^ 3

/-- The reconstructed preimage of `(a,s,c)` associated to a cubic root `x`. -/
def wallReconstruction (a s c x : ℝ) : Fin 3 → ℝ :=
  ![x, wallReconstructQ1 a s c x, wallReconstructQ2 a s c x]

/-- The proposed forward-wall base point lies on the cubic. -/
theorem wallA_basePoint : wallA 0 (1 / 2) 2 = 0 := by
  norm_num [wallA]

/-- The `s`-derivative expression has value `-1/2` at the base point. -/
theorem wallADerivS_basePoint : wallADerivS 0 (1 / 2) 2 = -(1 / 2) := by
  norm_num [wallADerivS]

/-- The `s`-derivative expression is nonzero at the base point. -/
theorem wallADerivS_basePoint_ne_zero : wallADerivS 0 (1 / 2) 2 ≠ 0 := by
  rw [wallADerivS_basePoint]
  norm_num

/-- The forward-wall polynomial is smooth in all three variables. -/
theorem contDiff_wallA :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ℝ => wallA p.1.1 p.2 p.1.2) := by
  unfold wallA
  fun_prop

/-- Local smooth wall function near `(0, 2)`. -/
theorem exists_forwardWallBeta_germ :
    ∃ (U : Set (ℝ × ℝ)) (β : ℝ × ℝ → ℝ),
      IsOpen U ∧
      (0, 2) ∈ U ∧
      ContDiffOn ℝ ⊤ β U ∧
      β (0, 2) = (1 / 2 : ℝ) ∧
      (∀ p ∈ U, wallA p.1 (β p) p.2 = 0) ∧
      (∀ p ∈ U, wallADerivS p.1 (β p) p.2 ≠ 0) := by
  let f : (ℝ × ℝ) × ℝ → ℝ := fun p => wallA p.1.1 p.2 p.1.2
  let u : (ℝ × ℝ) × ℝ := ((0, 2), 1 / 2)
  have hf : ContDiffAt ℝ ω f u := by
    apply contDiff_wallA.contDiffAt
  have hpartial : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    have hpoly : HasDerivAt (fun s : ℝ => -2 * s ^ 3 + s ^ 2) (-(1 / 2)) (1 / 2) := by
      convert (((hasDerivAt_id (𝕜 := ℝ) (1 / 2)).pow 3).const_mul (-2)).add
        ((hasDerivAt_id (𝕜 := ℝ) (1 / 2)).pow 2) using 1 <;> try rfl
      norm_num
    have hderiv : HasDerivAt (fun s : ℝ => f ((0, 2), s)) (-(1 / 2)) (1 / 2) := by
      simpa [f, wallA] using hpoly
    have hcomp :
        fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ =
          (-(1 / 2 : ℝ)) • ContinuousLinearMap.id ℝ ℝ := by
      have hline : HasFDerivAt (fun s : ℝ => ((0, 2), s))
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) (1 / 2) := by
        fun_prop
      have hderiv' : HasFDerivAt (f ∘ fun s : ℝ => ((0, 2), s))
          ((-(1 / 2 : ℝ)) • ContinuousLinearMap.id ℝ ℝ) (1 / 2) := by
        apply hderiv.hasFDerivAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro x
        simp
        ring
      exact (((hf.differentiableAt (by simp)).hasFDerivAt.comp (1 / 2) hline).unique
        hderiv')
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 (-(1 / 2 : ℝ)) (by norm_num)), by
      apply ContinuousLinearMap.ext
      intro x
      simp⟩
  let β : ℝ × ℝ → ℝ := hf.implicitFunction (by simp) hpartial
  have hβbase : β (0, 2) = (1 / 2 : ℝ) := by
    exact hf.implicitFunction_apply_self (by simp) hpartial
  have hβanalytic : AnalyticAt ℝ β (0, 2) := by
    exact (hf.contDiffAt_implicitFunction (by simp) hpartial).analyticAt
  have hwall : ∀ᶠ p in 𝓝 (0, 2), wallA p.1 (β p) p.2 = 0 := by
    filter_upwards [hf.eventually_apply_implicitFunction (by simp) hpartial] with p hp
    change wallA p.1 (β p) p.2 = wallA 0 (1 / 2) 2 at hp
    simpa only [wallA_basePoint] using hp
  have hderivCont : ContinuousAt (fun p => wallADerivS p.1 (β p) p.2) (0, 2) := by
    unfold wallADerivS
    fun_prop
  have hderiv : ∀ᶠ p in 𝓝 (0, 2), wallADerivS p.1 (β p) p.2 ≠ 0 := by
    apply hderivCont.eventually_ne
    simpa [hβbase] using wallADerivS_basePoint_ne_zero
  let good : Set (ℝ × ℝ) :=
    {p | wallA p.1 (β p) p.2 = 0 ∧ wallADerivS p.1 (β p) p.2 ≠ 0}
  let U : Set (ℝ × ℝ) := interior good ∩ {p | AnalyticAt ℝ β p}
  have hgood : ∀ᶠ p in 𝓝 (0, 2), p ∈ good := by
    filter_upwards [hwall, hderiv] with p hp hdp
    exact ⟨hp, hdp⟩
  refine ⟨U, β, ?_, ?_, ?_, hβbase, ?_, ?_⟩
  · exact isOpen_interior.inter (isOpen_analyticAt ℝ β)
  · refine ⟨mem_interior_iff_mem_nhds.2 ?_, hβanalytic⟩
    exact hgood
  · intro p hp
    exact hp.2.contDiffAt.contDiffWithinAt
  · intro p hp
    exact (interior_subset hp.1).1
  · intro p hp
    exact (interior_subset hp.1).2

/-- The linear cubic coefficient has value `-1` at the base point. -/
theorem wallB_basePoint : wallB (1 / 2) 2 = -1 := by
  norm_num [wallB]

/-- The linear cubic coefficient is nonzero at the base point. -/
theorem wallB_basePoint_ne_zero : wallB (1 / 2) 2 ≠ 0 := by
  rw [wallB_basePoint]
  norm_num

/-- The constant cubic coefficient has value `4` at the base point. -/
theorem wallC_basePoint : wallC 2 = 4 := by
  norm_num [wallC]

/-- The paper reconstruction formulas give a preimage under the anchor map whenever
their displayed denominators are nonzero and `x` satisfies the wall cubic. -/
theorem evalMap_F_wallReconstruction
    {a s c x : ℝ} (hx : x ≠ 0) (hden : wallReconstructionDenom s c x ≠ 0)
    (hcubic : wallCubic a s c x = 0) :
    evalMap (F ℝ) (wallReconstruction a s c x) = ![a, s, c] := by
  let q1 := wallReconstructQ1 a s c x
  let q2 := wallReconstructQ2 a s c x
  let u := x * q1
  let v := x ^ 3 * q2
  let K := wallB s c * x + 3 * c
  let N := 9 * a * c * x ^ 2 - 3 * c * s * x - 3 * c - s * x ^ 2 + 6 * x
  have hfactor : wallB s c * x + 3 * c ≠ 0 := by
    have : x * (wallB s c * x + 3 * c) ≠ 0 := by
      simpa [wallReconstructionDenom] using hden
    exact (mul_ne_zero_iff.mp this).2
  have hK : K ≠ 0 := by simpa [K] using hfactor
  have hu : K * u = N := by
    dsimp [K, u, q1, N, wallReconstructQ1, wallReconstructionDenom]
    field_simp [hx, hfactor]
  have hv : v = 2 * x - 3 * x * u - c := by
    dsimp [v, q2, wallReconstructQ2, u, q1]
    field_simp [hx]
  have hE1 : -3 * c * u ^ 2 - 6 * c * u - 3 * c - s * x ^ 2 +
      4 * x * u + 6 * x = 0 := by
    have hscaled : K ^ 2 * (-3 * c * u ^ 2 - 6 * c * u - 3 * c - s * x ^ 2 +
        4 * x * u + 6 * x) = 0 := by
      calc
        _ = -3 * c * (K * u) ^ 2 - 6 * c * K * (K * u) - 3 * c * K ^ 2 -
              s * x ^ 2 * K ^ 2 + 4 * x * K * (K * u) + 6 * x * K ^ 2 := by ring
        _ = -3 * c * N ^ 2 - 6 * c * K * N - 3 * c * K ^ 2 -
              s * x ^ 2 * K ^ 2 + 4 * x * K * N + 6 * x * K ^ 2 := by rw [hu]
        _ = 9 * c * x * wallCubic a s c x := by
          simp [K, N, wallCubic, wallA, wallB, wallC]
          ring
        _ = 0 := by rw [hcubic]; ring
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hK)
  have hE0 : -a * x ^ 3 - c * u ^ 3 - 3 * c * u ^ 2 - 3 * c * u - c +
      x * u ^ 2 + 3 * x * u + 2 * x = 0 := by
    have hscaled : K ^ 3 * (-a * x ^ 3 - c * u ^ 3 - 3 * c * u ^ 2 - 3 * c * u - c +
        x * u ^ 2 + 3 * x * u + 2 * x) = 0 := by
      calc
        _ = -a * x ^ 3 * K ^ 3 - c * (K * u) ^ 3 - 3 * c * K * (K * u) ^ 2 -
              3 * c * K ^ 2 * (K * u) - c * K ^ 3 + x * K * (K * u) ^ 2 +
              3 * x * K ^ 2 * (K * u) + 2 * x * K ^ 3 := by ring
        _ = -a * x ^ 3 * K ^ 3 - c * N ^ 3 - 3 * c * K * N ^ 2 -
              3 * c * K ^ 2 * N - c * K ^ 3 + x * K * N ^ 2 +
              3 * x * K ^ 2 * N + 2 * x * K ^ 3 := by rw [hu]
        _ = x ^ 2 * (27 * a * c ^ 2 * x + 9 * c - 4 * x) * wallCubic a s c x := by
          simp [K, N, wallCubic, wallA, wallB, wallC]
          ring
        _ = 0 := by rw [hcubic]; ring
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hK)
  funext i
  fin_cases i
  · simp [evalMap, F, wallReconstruction]
    change (1 + x * q1) ^ 3 * q2 + q1 ^ 2 * (1 + x * q1) * (4 + 3 * (x * q1)) = a
    apply sub_eq_zero.mp
    have hscaled : x ^ 3 * ((1 + x * q1) ^ 3 * q2 +
        q1 ^ 2 * (1 + x * q1) * (4 + 3 * (x * q1)) - a) = 0 := by
      calc
        _ = -a * x ^ 3 + (1 + u) ^ 3 * v +
              x * u ^ 2 * (1 + u) * (4 + 3 * u) := by
          dsimp [u, v]
          ring
        _ = -a * x ^ 3 - c * u ^ 3 - 3 * c * u ^ 2 - 3 * c * u - c +
              x * u ^ 2 + 3 * x * u + 2 * x := by
          rw [hv]
          ring
        _ = 0 := hE0
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hx)
  · simp [evalMap, F, wallReconstruction]
    change q1 + 3 * x * (1 + x * q1) ^ 2 * q2 +
      3 * x * q1 ^ 2 * (4 + 3 * (x * q1)) = s
    apply sub_eq_zero.mp
    have hscaled : x ^ 2 * (q1 + 3 * x * (1 + x * q1) ^ 2 * q2 +
        3 * x * q1 ^ 2 * (4 + 3 * (x * q1)) - s) = 0 := by
      calc
        _ = x * u + 3 * (1 + u) ^ 2 * v + 3 * x * u ^ 2 * (4 + 3 * u) -
              s * x ^ 2 := by
          dsimp [u, v]
          ring
        _ = -3 * c * u ^ 2 - 6 * c * u - 3 * c - s * x ^ 2 +
              4 * x * u + 6 * x := by
          rw [hv]
          ring
        _ = 0 := hE1
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hx)
  · simp [evalMap, F, wallReconstruction]
    change 2 * x - 3 * x ^ 2 * q1 - x ^ 3 * q2 = c
    dsimp [v, u] at hv
    linarith

end ExoticCCR
