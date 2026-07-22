/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# One-dimensional polynomial diffeomorphism algebra

This file formalizes the elementary real-polynomial and triangular-map cores used in the
historical B5 discussion.  It does not formalize the analytic or operator-algebraic parts of
Program B.
-/

noncomputable section

open Filter Function Matrix Polynomial Set

namespace ExoticCCR

namespace PolyDiffeo1D

/-- A real polynomial whose algebraic derivative never vanishes is either strictly increasing
or strictly decreasing.  The disjunction records the orientation. -/
theorem strictMono_or_strictAnti (p : ℝ[X])
    (hderiv : ∀ x : ℝ, p.derivative.eval x ≠ 0) :
    StrictMono p.eval ∨ StrictAnti p.eval := by
  have hsign :
      (∀ x ∈ (Set.univ : Set ℝ), p.derivative.eval x < 0) ∨
        ∀ x ∈ (Set.univ : Set ℝ), 0 < p.derivative.eval x :=
    hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne convex_univ
      (fun x _ ↦ (p.hasDerivAt x).hasDerivWithinAt) (fun x _ ↦ hderiv x)
  rcases hsign with hneg | hpos
  · exact Or.inr <| strictAnti_of_hasDerivAt_neg p.hasDerivAt (fun x ↦ hneg x trivial)
  · exact Or.inl <| strictMono_of_hasDerivAt_pos p.hasDerivAt (fun x ↦ hpos x trivial)

/-- In particular, a real polynomial whose derivative never vanishes is injective. -/
theorem injective_eval (p : ℝ[X]) (hderiv : ∀ x : ℝ, p.derivative.eval x ≠ 0) :
    Function.Injective p.eval := by
  rcases strictMono_or_strictAnti p hderiv with hmono | hanti
  · exact hmono.injective
  · exact hanti.injective

private theorem tendsto_atTop_of_monotone_of_abs {f : ℝ → ℝ} (hf : Monotone f)
    (habs : Tendsto (fun x ↦ |f x|) atTop atTop) : Tendsto f atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards
    [habs.eventually (eventually_ge_atTop (max |b| (|f 0| + 1))), eventually_ge_atTop 0]
    with x hx hx0
  have hfx : f 0 ≤ f x := hf hx0
  by_cases h0 : 0 ≤ f x
  · rw [abs_of_nonneg h0] at hx
    exact le_trans (le_abs_self b) (le_trans (le_max_left _ _) hx)
  · rw [abs_of_neg (lt_of_not_ge h0)] at hx
    have : -f x ≤ |f 0| := by linarith [neg_le_abs (f 0)]
    linarith [le_max_right |b| (|f 0| + 1)]

private theorem tendsto_atBot_of_monotone_of_abs {f : ℝ → ℝ} (hf : Monotone f)
    (habs : Tendsto (fun x ↦ |f x|) atBot atTop) : Tendsto f atBot atBot := by
  refine tendsto_atBot.2 fun b ↦ ?_
  filter_upwards
    [habs.eventually (eventually_ge_atTop (max |b| (|f 0| + 1))), eventually_le_atBot 0]
    with x hx hx0
  have hfx : f x ≤ f 0 := hf hx0
  by_cases h0 : f x ≤ 0
  · rw [abs_of_nonpos h0] at hx
    linarith [neg_le_abs b, le_max_left |b| (|f 0| + 1)]
  · rw [abs_of_pos (lt_of_not_ge h0)] at hx
    have : f x ≤ |f 0| := hfx.trans (le_abs_self (f 0))
    linarith [le_max_right |b| (|f 0| + 1)]

private theorem tendsto_atBot_of_antitone_of_abs {f : ℝ → ℝ} (hf : Antitone f)
    (habs : Tendsto (fun x ↦ |f x|) atTop atTop) : Tendsto f atTop atBot := by
  refine tendsto_atBot.2 fun b ↦ ?_
  filter_upwards
    [habs.eventually (eventually_ge_atTop (max |b| (|f 0| + 1))), eventually_ge_atTop 0]
    with x hx hx0
  have hfx : f x ≤ f 0 := hf hx0
  by_cases h0 : f x ≤ 0
  · rw [abs_of_nonpos h0] at hx
    linarith [neg_le_abs b, le_max_left |b| (|f 0| + 1)]
  · rw [abs_of_pos (lt_of_not_ge h0)] at hx
    have : f x ≤ |f 0| := hfx.trans (le_abs_self (f 0))
    linarith [le_max_right |b| (|f 0| + 1)]

private theorem tendsto_atTop_of_antitone_of_abs {f : ℝ → ℝ} (hf : Antitone f)
    (habs : Tendsto (fun x ↦ |f x|) atBot atTop) : Tendsto f atBot atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards
    [habs.eventually (eventually_ge_atTop (max |b| (|f 0| + 1))), eventually_le_atBot 0]
    with x hx hx0
  have hfx : f 0 ≤ f x := hf hx0
  by_cases h0 : 0 ≤ f x
  · rw [abs_of_nonneg h0] at hx
    exact le_trans (le_abs_self b) (le_trans (le_max_left _ _) hx)
  · rw [abs_of_neg (lt_of_not_ge h0)] at hx
    have : -f x ≤ |f 0| := by linarith [neg_le_abs (f 0)]
    linarith [le_max_right |b| (|f 0| + 1)]

/-- A real polynomial whose derivative never vanishes is surjective onto `ℝ`. -/
theorem surjective_eval (p : ℝ[X]) (hderiv : ∀ x : ℝ, p.derivative.eval x ≠ 0) :
    Function.Surjective p.eval := by
  have hp0 : p.natDegree ≠ 0 := by
    apply (Polynomial.derivative_ne_zero (p := p)).mp
    intro hp
    exact hderiv 0 (by simp [hp])
  have hdeg : 0 < p.degree :=
    natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hp0)
  have hcont : Continuous p.eval := Polynomial.continuous p
  rcases strictMono_or_strictAnti p hderiv with hmono | hanti
  · exact hcont.surjective
      (tendsto_atTop_of_monotone_of_abs hmono.monotone (p.abs_tendsto_atTop hdeg))
      (tendsto_atBot_of_monotone_of_abs hmono.monotone (p.abs_tendsto_atBot hdeg))
  · exact hcont.surjective'
      (tendsto_atTop_of_antitone_of_abs hanti.antitone (p.abs_tendsto_atBot hdeg))
      (tendsto_atBot_of_antitone_of_abs hanti.antitone (p.abs_tendsto_atTop hdeg))

/-- A real polynomial whose derivative never vanishes is a bijection of the real line. -/
theorem bijective_eval (p : ℝ[X]) (hderiv : ∀ x : ℝ, p.derivative.eval x ≠ 0) :
    Function.Bijective p.eval :=
  ⟨injective_eval p hderiv, surjective_eval p hderiv⟩

/-- Coordinatewise product of two maps. -/
def productMap {α β γ δ : Type*} (f : α → β) (g : γ → δ) : α × γ → β × δ :=
  Prod.map f g

/-- A coordinatewise product of bijections is bijective. -/
theorem productMap_bijective {α β γ δ : Type*} {f : α → β} {g : γ → δ}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (productMap f g) := by
  constructor
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
    exact Prod.ext (hf.1 <| congrArg Prod.fst h) (hg.1 <| congrArg Prod.snd h)
  · rintro ⟨x, y⟩
    obtain ⟨x', hx'⟩ := hf.2 x
    obtain ⟨y', hy'⟩ := hg.2 y
    exact ⟨(x', y'), by simp [productMap, hx', hy']⟩

/-- The Fréchet derivative of the coordinatewise polynomial map is the product of the two
one-dimensional derivative maps. -/
theorem hasFDerivAt_productMap (p q : ℝ[X]) (z : ℝ × ℝ) :
    HasFDerivAt (productMap p.eval q.eval)
      ((ContinuousLinearMap.toSpanSingleton ℝ (p.derivative.eval z.1)).prodMap
        (ContinuousLinearMap.toSpanSingleton ℝ (q.derivative.eval z.2))) z := by
  simpa [productMap] using
    ((p.hasDerivAt z.1).hasFDerivAt.prodMap (p := z) (q.hasDerivAt z.2).hasFDerivAt)

/-- The diagonal Jacobian matrix of the coordinatewise polynomial map `(p(x), q(y))`. -/
def productJacobian (p q : ℝ[X]) (z : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![p.derivative.eval z.1, q.derivative.eval z.2]

/-- Determinant of the diagonal product-map Jacobian. -/
theorem det_productJacobian (p q : ℝ[X]) (z : ℝ × ℝ) :
    (productJacobian p q z).det = p.derivative.eval z.1 * q.derivative.eval z.2 := by
  simp [productJacobian]

/-- The product-map Jacobian determinant is nonzero when both univariate derivatives are. -/
theorem det_productJacobian_ne_zero (p q : ℝ[X])
    (hp : ∀ x : ℝ, p.derivative.eval x ≠ 0)
    (hq : ∀ y : ℝ, q.derivative.eval y ≠ 0) (z : ℝ × ℝ) :
    (productJacobian p q z).det ≠ 0 := by
  rw [det_productJacobian]
  exact mul_ne_zero (hp z.1) (hq z.2)

/-- The product of two real polynomials with nowhere-zero derivatives is bijective. -/
theorem polynomial_productMap_bijective (p q : ℝ[X])
    (hp : ∀ x : ℝ, p.derivative.eval x ≠ 0)
    (hq : ∀ y : ℝ, q.derivative.eval y ≠ 0) :
    Function.Bijective (productMap p.eval q.eval) :=
  productMap_bijective (bijective_eval p hp) (bijective_eval q hq)

section Shears

variable {R : Type*} [CommRing R]

/-- Vertical elementary polynomial shear `(x,y) ↦ (x,y+p(x))`. -/
def verticalShear (p : R[X]) : R × R → R × R :=
  fun z ↦ (z.1, z.2 + p.eval z.1)

/-- Explicit polynomial inverse of the vertical shear. -/
def verticalShearInv (p : R[X]) : R × R → R × R :=
  fun z ↦ (z.1, z.2 - p.eval z.1)

@[simp] theorem verticalShearInv_verticalShear (p : R[X]) (z : R × R) :
    verticalShearInv p (verticalShear p z) = z := by
  simp [verticalShear, verticalShearInv]

@[simp] theorem verticalShear_verticalShearInv (p : R[X]) (z : R × R) :
    verticalShear p (verticalShearInv p z) = z := by
  simp [verticalShear, verticalShearInv]

/-- Every vertical elementary polynomial shear is bijective. -/
theorem verticalShear_bijective (p : R[X]) : Function.Bijective (verticalShear p) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨verticalShearInv p, verticalShearInv_verticalShear p, verticalShear_verticalShearInv p⟩

/-- Horizontal elementary polynomial shear `(x,y) ↦ (x+p(y),y)`. -/
def horizontalShear (p : R[X]) : R × R → R × R :=
  fun z ↦ (z.1 + p.eval z.2, z.2)

/-- Explicit polynomial inverse of the horizontal shear. -/
def horizontalShearInv (p : R[X]) : R × R → R × R :=
  fun z ↦ (z.1 - p.eval z.2, z.2)

@[simp] theorem horizontalShearInv_horizontalShear (p : R[X]) (z : R × R) :
    horizontalShearInv p (horizontalShear p z) = z := by
  simp [horizontalShear, horizontalShearInv]

@[simp] theorem horizontalShear_horizontalShearInv (p : R[X]) (z : R × R) :
    horizontalShear p (horizontalShearInv p z) = z := by
  simp [horizontalShear, horizontalShearInv]

/-- Every horizontal elementary polynomial shear is bijective. -/
theorem horizontalShear_bijective (p : R[X]) : Function.Bijective (horizontalShear p) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨horizontalShearInv p, horizontalShearInv_horizontalShear p,
      horizontalShear_horizontalShearInv p⟩

end Shears

end PolyDiffeo1D

end ExoticCCR
