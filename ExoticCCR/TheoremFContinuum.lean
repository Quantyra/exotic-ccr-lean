import ExoticCCR.TheoremFExtensionMultiplicity
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Cardinality

noncomputable section
namespace ExoticCCR

/-- The parameter circle has continuum cardinality. -/
theorem mk_circle_eq_continuum : Cardinal.mk Circle = Cardinal.continuum := by
  exact (Cardinal.mk_congr Circle.argEquiv).trans
    (Cardinal.mk_Ioc_real (by linarith [Real.pi_pos]))

/-- A circle point, with its unchanged complex value, is a unitary phase. -/
def circleToUnitary (z : Circle) : unitary ℂ :=
  ⟨(z : ℂ), by
    simp [Unitary.mem_iff, RCLike.star_def, Complex.conj_mul',
      Complex.mul_conj', Circle.norm_coe]⟩

/-- The passage from circle points to unitary phases does not identify points. -/
theorem circleToUnitary_injective : Function.Injective circleToUnitary := by
  intro z w h
  apply Circle.coe_injective
  exact congrArg (fun u : unitary ℂ => (u : ℂ)) h

/-- The precise cardinality of the phase parameter type. -/
theorem mk_unitary_complex_eq_continuum :
    Cardinal.mk (unitary ℂ) = Cardinal.continuum := by
  apply le_antisymm
  · simpa only [Cardinal.mk_complex] using
      (Cardinal.mk_le_of_injective
        (Subtype.val_injective : Function.Injective (fun u : unitary ℂ => (u : ℂ))))
  · rw [← mk_circle_eq_continuum]
    exact Cardinal.mk_le_of_injective circleToUnitary_injective

/-- There are at least continuum many self-adjoint extension witnesses of
    the specific canonical minimal operator. No upper bound is asserted. -/
theorem theoremF_continuum_le_selfAdjointExtensions :
    Cardinal.continuum ≤ Cardinal.mk (SelfAdjointExtension H_X1_min) := by
  rw [← mk_unitary_complex_eq_continuum]
  exact Cardinal.mk_le_of_injective theoremFUnitPhaseExtension_injective

end ExoticCCR
