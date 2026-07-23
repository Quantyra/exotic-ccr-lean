/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.PolynomialWeylAlgebra
import ExoticCCR.TheoremC

/-!
# Theorem C: algebraic Weyl endomorphism

The anchor polynomial map and its dual matrix define a unital algebra
endomorphism of the abstract polynomial Weyl algebra.
-/

noncomputable section

open Matrix MvPolynomial

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- The three-variable polynomial Weyl algebra used by the anchor. -/
abbrev AnchorWeyl := PolynomialWeylAlgebra K (Fin 3)

/-- The proposed image of a position generator. -/
def theoremCPsiQ (i : Fin 3) : AnchorWeyl K := qPolynomial K (Fin 3) (F K i)

/-- A left-coefficient polynomial momentum. -/
def polynomialMomentum (a : Fin 3 → MvPolynomial (Fin 3) K) : AnchorWeyl K :=
  ∑ k : Fin 3, qPolynomial K (Fin 3) (a k) * p K (Fin 3) k

/-- The proposed image of a momentum generator, with coefficients on the left. -/
def theoremCPsiP (j : Fin 3) : AnchorWeyl K :=
  polynomialMomentum K (dualMatrixF K j)

@[simp] theorem dualField_X (j l : Fin 3) :
    dualField K j (X l) = dualMatrixF K j l := by
  classical
  simp [dualField, Pi.single_apply]

/-- Coordinate form of the vanishing bracket of the dual fields. -/
theorem dualMatrixF_field_bracket (h2 : (2 : K) ≠ 0) (i j l : Fin 3) :
    dualField K i (dualMatrixF K j l) -
      dualField K j (dualMatrixF K i l) = 0 := by
  simpa using dualField_bracket_eq_zero (K := K) h2 i j (X l)

private theorem qPolynomial_commute (f g : MvPolynomial (Fin 3) K) :
    qPolynomial K (Fin 3) f * qPolynomial K (Fin 3) g =
      qPolynomial K (Fin 3) g * qPolynomial K (Fin 3) f := by
  rw [← map_mul, ← map_mul, mul_comm]

/-- Commuting a polynomial position coefficient through a polynomial momentum
computes the corresponding directional derivative. -/
theorem qPolynomial_polynomialMomentum_sub (f : MvPolynomial (Fin 3) K)
    (a : Fin 3 → MvPolynomial (Fin 3) K) :
    qPolynomial K (Fin 3) f * polynomialMomentum K a -
      polynomialMomentum K a * qPolynomial K (Fin 3) f =
      qPolynomial K (Fin 3) (∑ k : Fin 3, a k * pderiv k f) := by
  simp only [polynomialMomentum, Finset.mul_sum, Finset.sum_mul, map_sum, map_mul,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hd := qPolynomial_mul_p_sub K (Fin 3) f k
  have hc := qPolynomial_commute K f (a k)
  calc
    qPolynomial K (Fin 3) f *
          (qPolynomial K (Fin 3) (a k) * p K (Fin 3) k) -
        (qPolynomial K (Fin 3) (a k) * p K (Fin 3) k) *
          qPolynomial K (Fin 3) f =
        qPolynomial K (Fin 3) (a k) *
          (qPolynomial K (Fin 3) f * p K (Fin 3) k) -
        qPolynomial K (Fin 3) (a k) *
          (p K (Fin 3) k * qPolynomial K (Fin 3) f) := by
      rw [mul_assoc (qPolynomial K (Fin 3) (a k))]
      rw [← mul_assoc, hc, mul_assoc]
    _ = qPolynomial K (Fin 3) (a k) *
        (qPolynomial K (Fin 3) f * p K (Fin 3) k -
          p K (Fin 3) k * qPolynomial K (Fin 3) f) := by rw [mul_sub]
    _ = _ := by rw [hd]

/-- The proposed position images commute. -/
theorem theoremCPsi_qq (i j : Fin 3) :
    theoremCPsiQ K i * theoremCPsiQ K j =
      theoremCPsiQ K j * theoremCPsiQ K i :=
  qPolynomial_commute K _ _

/-- The proposed position and momentum images have the canonical commutator. -/
theorem theoremCPsi_qp (h2 : (2 : K) ≠ 0) (i j : Fin 3) :
    theoremCPsiQ K i * theoremCPsiP K j -
      theoremCPsiP K j * theoremCPsiQ K i =
      algebraMap K _ (if i = j then 1 else 0) := by
  rw [theoremCPsiQ, theoremCPsiP, qPolynomial_polynomialMomentum_sub]
  change qPolynomial K (Fin 3) (dualField K j (F K i)) = _
  rw [dualField_F h2]
  split_ifs <;> simp

private theorem momentum_term_commutator
    (a b : Fin 3 → MvPolynomial (Fin 3) K) (k l : Fin 3) :
    (qPolynomial K (Fin 3) (a k) * p K (Fin 3) k) *
        (qPolynomial K (Fin 3) (b l) * p K (Fin 3) l) -
      (qPolynomial K (Fin 3) (b l) * p K (Fin 3) l) *
        (qPolynomial K (Fin 3) (a k) * p K (Fin 3) k) =
      -(qPolynomial K (Fin 3) (a k) *
          qPolynomial K (Fin 3) (pderiv k (b l)) * p K (Fin 3) l) +
        qPolynomial K (Fin 3) (b l) *
          qPolynomial K (Fin 3) (pderiv l (a k)) * p K (Fin 3) k := by
  have hkb := qPolynomial_mul_p_sub K (Fin 3) (b l) k
  have hla := qPolynomial_mul_p_sub K (Fin 3) (a k) l
  have hkb' : p K (Fin 3) k * qPolynomial K (Fin 3) (b l) =
      qPolynomial K (Fin 3) (b l) * p K (Fin 3) k -
        qPolynomial K (Fin 3) (pderiv k (b l)) :=
    eq_sub_iff_add_eq.mpr (sub_eq_iff_eq_add'.mp hkb).symm
  have hla' : p K (Fin 3) l * qPolynomial K (Fin 3) (a k) =
      qPolynomial K (Fin 3) (a k) * p K (Fin 3) l -
        qPolynomial K (Fin 3) (pderiv l (a k)) :=
    eq_sub_iff_add_eq.mpr (sub_eq_iff_eq_add'.mp hla).symm
  have hab := qPolynomial_commute K (a k) (b l)
  have hpp := p_mul_p K (Fin 3) k l
  rw [mul_assoc (qPolynomial K (Fin 3) (a k)),
    ← mul_assoc (p K (Fin 3) k), hkb',
    mul_assoc (qPolynomial K (Fin 3) (b l)),
    ← mul_assoc (p K (Fin 3) l), hla']
  simp only [sub_mul, mul_sub, mul_assoc]
  rw [hpp]
  rw [← mul_assoc (qPolynomial K (Fin 3) (a k)) (qPolynomial K (Fin 3) (b l)),
    hab, mul_assoc (qPolynomial K (Fin 3) (b l)) (qPolynomial K (Fin 3) (a k))]
  noncomm_ring

/-- Commutator formula for two left-coefficient polynomial momenta. -/
theorem polynomialMomentum_commutator
    (a b : Fin 3 → MvPolynomial (Fin 3) K) :
    polynomialMomentum K a * polynomialMomentum K b -
      polynomialMomentum K b * polynomialMomentum K a =
      ∑ l : Fin 3, qPolynomial K (Fin 3)
        ((∑ k : Fin 3, b k * pderiv k (a l)) -
          (∑ k : Fin 3, a k * pderiv k (b l))) * p K (Fin 3) l := by
  simp only [polynomialMomentum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun x i : Fin 3 ↦
    (qPolynomial K (Fin 3) (b i) * p K (Fin 3) i) *
      (qPolynomial K (Fin 3) (a x) * p K (Fin 3) x))]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  simp_rw [momentum_term_commutator K]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun l k : Fin 3 ↦
    qPolynomial K (Fin 3) (b l) * qPolynomial K (Fin 3) (pderiv l (a k)) *
      p K (Fin 3) k)]
  simp only [map_sub, map_sum, map_mul]
  simp only [Finset.sum_mul, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sub_mul]
  noncomm_ring

/-- The proposed momentum images commute. -/
theorem theoremCPsi_pp (h2 : (2 : K) ≠ 0) (i j : Fin 3) :
    theoremCPsiP K i * theoremCPsiP K j =
      theoremCPsiP K j * theoremCPsiP K i := by
  apply sub_eq_zero.mp
  rw [theoremCPsiP, theoremCPsiP, polynomialMomentum_commutator]
  apply Finset.sum_eq_zero
  intro l _
  have hb := dualMatrixF_field_bracket (K := K) h2 i j l
  change qPolynomial K (Fin 3)
      (dualField K j (dualMatrixF K i l) - dualField K i (dualMatrixF K j l)) *
      p K (Fin 3) l = 0
  rw [show dualField K j (dualMatrixF K i l) - dualField K i (dualMatrixF K j l) = 0 by
    exact sub_eq_zero.mpr (sub_eq_zero.mp hb).symm]
  simp

private def theoremCFreeLift (h2 : (2 : K) ≠ 0) :
    FreeAlgebra K (WeylGen (Fin 3)) →ₐ[K] AnchorWeyl K :=
  FreeAlgebra.lift K (Sum.elim (theoremCPsiQ K) (theoremCPsiP K))

private theorem theoremCFreeLift_respects (h2 : (2 : K) ≠ 0)
    {x y : FreeAlgebra K (WeylGen (Fin 3))}
    (h : WeylRel K (Fin 3) x y) :
    theoremCFreeLift K h2 x = theoremCFreeLift K h2 y := by
  cases h with
  | qq i j => simpa [theoremCFreeLift, qFree] using theoremCPsi_qq K i j
  | pp i j => simpa [theoremCFreeLift, pFree] using theoremCPsi_pp K h2 i j
  | qp i j => simpa [theoremCFreeLift, qFree, pFree] using theoremCPsi_qp K h2 i j

/-- T0.C.4: the anchor formulas define a unital algebra endomorphism of the
abstract polynomial Weyl algebra. -/
def theoremCPsi (h2 : (2 : K) ≠ 0) : AnchorWeyl K →ₐ[K] AnchorWeyl K :=
  RingQuot.liftAlgHom K ⟨theoremCFreeLift K h2,
    fun {x y} h ↦ theoremCFreeLift_respects K h2 (x := x) (y := y) h⟩

@[simp] theorem theoremCPsi_q (h2 : (2 : K) ≠ 0) (i : Fin 3) :
    theoremCPsi K h2 (q K (Fin 3) i) = theoremCPsiQ K i := by
  simp [theoremCPsi, q, theoremCFreeLift, qFree]

@[simp] theorem theoremCPsi_p (h2 : (2 : K) ≠ 0) (j : Fin 3) :
    theoremCPsi K h2 (p K (Fin 3) j) = theoremCPsiP K j := by
  simp [theoremCPsi, p, theoremCFreeLift, pFree]

/-- The Weyl endomorphism is uniquely determined by its values on generators. -/
theorem theoremCPsi_unique (h2 : (2 : K) ≠ 0) (φ : AnchorWeyl K →ₐ[K] AnchorWeyl K)
    (hq : ∀ i, φ (q K (Fin 3) i) = theoremCPsiQ K i)
    (hp : ∀ j, φ (p K (Fin 3) j) = theoremCPsiP K j) :
    φ = theoremCPsi K h2 := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | inl i =>
      change φ (q K (Fin 3) i) = theoremCPsi K h2 (q K (Fin 3) i)
      rw [hq, theoremCPsi_q]
  | inr j =>
      change φ (p K (Fin 3) j) = theoremCPsi K h2 (p K (Fin 3) j)
      rw [hp, theoremCPsi_p]

end ExoticCCR
