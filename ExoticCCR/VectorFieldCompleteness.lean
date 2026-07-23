/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Completeness of autonomous vector fields

This file records the extension formulation of completeness and the standard
finite-escape obstruction.  It is deliberately independent of the A001
coordinates.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace ExoticCCR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An autonomous vector field is complete when each of its integral curves on
an open interval extends to a global integral curve. -/
def IsCompleteVectorField (X : E → E) : Prop :=
  ∀ ⦃a b : ℝ⦄ (γ : ℝ → E),
    (∀ t ∈ Ioo a b, HasDerivAt γ (X (γ t)) t) →
      ∃ Γ : ℝ → E, (∀ t, HasDerivAt Γ (X (Γ t)) t) ∧ EqOn Γ γ (Ioo a b)

/-- A smooth vector field which is not complete. -/
def IsIncompleteSmoothVectorField (X : E → E) : Prop :=
  ContDiff ℝ ⊤ X ∧ ¬ IsCompleteVectorField X

/-- A finite-time integral curve escaping every norm ball obstructs completeness. -/
theorem not_isCompleteVectorField_of_finite_escape
    {X : E → E} {γ : ℝ → E} {a b : ℝ}
    (_hX : ContDiff ℝ 1 X) (hab : a < b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (X (γ t)) t)
    (h_escape : Tendsto (fun t ↦ ‖γ t‖) (𝓝[<] b) atTop) :
    ¬ IsCompleteVectorField X := by
  intro hcomplete
  obtain ⟨Γ, hΓ, heq⟩ := hcomplete γ hγ
  have hΓ_cont : Continuous Γ := continuous_iff_continuousAt.2 fun t ↦ (hΓ t).continuousAt
  have hfinite : Tendsto (fun t ↦ ‖Γ t‖) (𝓝[<] b) (𝓝 ‖Γ b‖) :=
    ((continuous_norm.comp hΓ_cont).continuousAt.tendsto).mono_left inf_le_left
  have hevent_eq : (fun t ↦ ‖Γ t‖) =ᶠ[𝓝[<] b] (fun t ↦ ‖γ t‖) :=
    Filter.EventuallyEq.fun_comp (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab) heq) norm
  have hlarge : ∀ᶠ t in 𝓝[<] b, ‖Γ b‖ + 1 ≤ ‖γ t‖ :=
    h_escape.eventually_ge_atTop (‖Γ b‖ + 1)
  have hsmall : ∀ᶠ t in 𝓝[<] b, ‖Γ t‖ < ‖Γ b‖ + 1 :=
    hfinite (Iio_mem_nhds (by linarith))
  obtain ⟨t, ht_large, ht_small, ht_eq⟩ :=
    (hlarge.and (hsmall.and hevent_eq)).exists
  change ‖Γ t‖ = ‖γ t‖ at ht_eq
  rw [← ht_eq] at ht_large
  linarith

end ExoticCCR
