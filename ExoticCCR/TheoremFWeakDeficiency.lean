/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremEForwardIBP

/-!
# Cutoff-parametric forward weak deficiency

This module exports the maximal-sheet weak `-i` construction for every nonzero
continuous compactly supported transverse cutoff supported inside the sheet.
It does not assert a global sheet, a deficiency-index value, or full Theorem F.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ExoticCCR

/-- Every nonzero continuous compactly supported cutoff inside a maximal
forward sheet produces a concrete nonzero weak `-i` adjoint eigenvector for the
canonical minimal transport core of `X1`. -/
theorem ForwardMaximalSheet.nonzero_weakAdjointEigenvector_uMinus
    (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχW : tsupport χ ⊆ M.W) (hχ0 : χ ≠ 0) :
    let u := (M.memLp_uMinus χ hχ hχc hχW).toLp (M.uMinus χ)
    u ≠ 0 ∧ WeakAdjointEigenvector H_X1_min (-Complex.I) u := by
  dsimp only
  have hχpoint : ∃ x, χ x ≠ 0 := by
    by_contra h
    apply hχ0
    funext x
    by_contra hχx
    exact h ⟨x, hχx⟩
  obtain ⟨x, hχx⟩ := hχpoint
  have hx : x ∈ M.W :=
    hχW (subset_tsupport _ (Function.mem_support.mpr hχx))
  let hu := M.memLp_uMinus χ hχ hχc hχW
  have himage := M.lintegral_sq_norm_uMinus_image_pos χ hχ hx hχx
  have hu_ne : hu.toLp (M.uMinus χ) ≠ 0 := by
    intro hzero
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero] at hzero
    have huae : M.uMinus χ =ᵐ[volume] 0 := hu.coeFn_toLp.symm.trans hzero
    have hamb : ∫⁻ q : Fin 3 → ℝ,
        ENNReal.ofReal (‖M.uMinus χ q‖ ^ 2) ∂volume = 0 := by
      rw [← lintegral_zero]
      apply lintegral_congr_ae
      filter_upwards [huae] with q hq
      simp [hq]
    have hz : ∫⁻ q in M.PsiFin3 '' M.Dfin3,
        ENNReal.ofReal (‖M.uMinus χ q‖ ^ 2) ∂volume = 0 := by
      apply le_zero_iff.mp
      exact (setLIntegral_le_lintegral _ _).trans_eq hamb
    exact (ne_of_gt himage) hz
  refine ⟨hu_ne, ?_⟩
  apply weakAdjoint_negI_of_representative_integrals
    (M.memLp_uMinus χ hχ hχc hχW)
  intro φ
  exact representative_integral_identity M χ hχ hχc hχW φ

end ExoticCCR
