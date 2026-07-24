/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremCWeyl

/-!
# Polynomial Poisson brackets for the cotangent lift

We model the six phase-space coordinates by `Fin 3 ⊕ Fin 3`: the left copy is
`q₀,q₁,q₂`, and the right copy is `p₀,p₁,p₂`.  The standard polynomial Poisson
bracket is then used to verify the coordinate brackets of the anchor's
cotangent lift.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- Polynomials on the six algebraic phase-space coordinates `(q,p)`. -/
abbrev PhasePolynomial := MvPolynomial (Fin 3 ⊕ Fin 3) K

/-- Include a polynomial in the configuration variables into phase space. -/
def configurationLift (f : MvPolynomial (Fin 3) K) : PhasePolynomial K :=
  rename Sum.inl f

/-- The standard Poisson bracket `Σₖ (∂qₖ f ∂pₖ g - ∂pₖ f ∂qₖ g)`. -/
def poissonBracket (f g : PhasePolynomial K) : PhasePolynomial K :=
  ∑ k : Fin 3, (pderiv (Sum.inl k) f * pderiv (Sum.inr k) g -
    pderiv (Sum.inr k) f * pderiv (Sum.inl k) g)

/-- The transformed configuration coordinate `Qᵢ = Fᵢ(q)`. -/
def phaseQ (i : Fin 3) : PhasePolynomial K := configurationLift K (F K i)

/-- The transformed momentum coordinate `Pⱼ = Σₖ Bⱼₖ(q) pₖ`. -/
def phaseP (j : Fin 3) : PhasePolynomial K :=
  ∑ k : Fin 3, configurationLift K (dualMatrixF K j k) * X (Sum.inr k)

variable {K}

@[simp] theorem pderiv_configurationLift_q (i : Fin 3)
    (f : MvPolynomial (Fin 3) K) :
    pderiv (Sum.inl i) (configurationLift K f) =
      configurationLift K (pderiv i f) := by
  exact pderiv_rename Sum.inl_injective i f

@[simp] theorem pderiv_configurationLift_p (i : Fin 3)
    (f : MvPolynomial (Fin 3) K) :
    pderiv (Sum.inr i) (configurationLift K f) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨j, _, hji⟩ := mem_vars_rename Sum.inl f h
  cases hji

@[simp] theorem pderiv_phaseQ_q (i j : Fin 3) :
    pderiv (Sum.inl i) (phaseQ K j) =
      configurationLift K (pderiv i (F K j)) := by
  simp [phaseQ]

@[simp] theorem pderiv_phaseQ_p (i j : Fin 3) :
    pderiv (Sum.inr i) (phaseQ K j) = 0 := by
  simp [phaseQ]

@[simp] theorem pderiv_phaseP_q (i j : Fin 3) :
    pderiv (Sum.inl i) (phaseP K j) =
      ∑ k : Fin 3, configurationLift K (pderiv i (dualMatrixF K j k)) *
        X (Sum.inr k) := by
  simp [phaseP, mul_comm]

@[simp] theorem pderiv_phaseP_p (i j : Fin 3) :
    pderiv (Sum.inr i) (phaseP K j) =
      configurationLift K (dualMatrixF K j i) := by
  classical
  simp [phaseP, Pi.single_apply]

/-- T0.B.4a: transformed configuration coordinates Poisson-commute. -/
theorem poissonBracket_phaseQ_phaseQ (i j : Fin 3) :
    poissonBracket K (phaseQ K i) (phaseQ K j) = 0 := by
  simp [poissonBracket, phaseQ]

/-- T0.B.4b: `{Qᵢ,Pⱼ} = δᵢⱼ`, from `J Bᵀ = I`. -/
theorem poissonBracket_phaseQ_phaseP (h2 : (2 : K) ≠ 0) (i j : Fin 3) :
    poissonBracket K (phaseQ K i) (phaseP K j) = if i = j then 1 else 0 := by
  rw [show poissonBracket K (phaseQ K i) (phaseP K j) =
      configurationLift K (dualField K j (F K i)) by
    simp [poissonBracket, dualField, configurationLift, mul_comm]]
  rw [dualField_F h2]
  split_ifs <;> simp [configurationLift]

/-- Coefficient form of the vanishing bracket of the dual fields. -/
theorem dualMatrixF_lieCoefficient (h2 : (2 : K) ≠ 0) (i j k : Fin 3) :
    ∑ l : Fin 3, (dualMatrixF K i l * pderiv l (dualMatrixF K j k) -
      dualMatrixF K j l * pderiv l (dualMatrixF K i k)) = 0 := by
  simpa [dualField, Finset.sum_sub_distrib] using
    dualMatrixF_field_bracket (K := K) h2 i j k

/-- T0.B.4c: the lifted momentum coordinates Poisson-commute. -/
theorem poissonBracket_phaseP_phaseP (h2 : (2 : K) ≠ 0) (i j : Fin 3) :
    poissonBracket K (phaseP K i) (phaseP K j) = 0 := by
  rw [show poissonBracket K (phaseP K i) (phaseP K j) =
      -∑ k : Fin 3, configurationLift K
        (∑ l : Fin 3, (dualMatrixF K i l * pderiv l (dualMatrixF K j k) -
          dualMatrixF K j l * pderiv l (dualMatrixF K i k))) * X (Sum.inr k) by
    simp [poissonBracket, configurationLift, Fin.sum_univ_three]
    ring]
  simp [dualMatrixF_lieCoefficient h2, configurationLift]

/-- T0.B.4: the cotangent lift preserves the canonical Poisson brackets on
the polynomial phase-space generators. -/
theorem theoremB_poisson (h2 : (2 : K) ≠ 0) (i j : Fin 3) :
    poissonBracket K (phaseQ K i) (phaseQ K j) = 0 ∧
      poissonBracket K (phaseP K i) (phaseP K j) = 0 ∧
      poissonBracket K (phaseQ K i) (phaseP K j) = if i = j then 1 else 0 := by
  exact ⟨poissonBracket_phaseQ_phaseQ i j,
    poissonBracket_phaseP_phaseP h2 i j, poissonBracket_phaseQ_phaseP h2 i j⟩

end ExoticCCR
