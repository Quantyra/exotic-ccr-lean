/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardPuncturedOpen
import ExoticCCR.TheoremFSaturatedSheet

/-!
# Local flow seed from the backward wall reconstruction

This module combines one point of the local positive-`tau` backward
reconstruction with generic local existence for the ambient vector field `X1`.
It makes no assertion that the resulting integral curve follows the backward
reconstruction branch.
-/

noncomputable section

open MvPolynomial Set

namespace ExoticCCR

/-- A guarded point of the local backward reconstruction seeds an ambient
local integral curve of `X1`. -/
theorem exists_backwardFlowSeed :
    ∃ (W Wp : Set ((ℝ × ℝ) × ℝ)) (alpha : ℝ × ℝ → ℝ)
      (rMinusW : ((ℝ × ℝ) × ℝ) → ℝ) (p : (ℝ × ℝ) × ℝ)
      (q : R3) (gamma : ℝ → R3) (I : Set ℝ),
      IsOpen W ∧
      (((1 / 54), 2), 0) ∈ W ∧
      IsOpen Wp ∧
      Wp ⊆ W ∧
      p ∈ Wp ∧
      0 < p.2 ∧
      q = wallReconstruction p.1.1 (alpha p.1 + p.2 ^ 2) p.1.2
        (rMinusW p / p.2) ∧
      wallReconstructionDenom
        (alpha p.1 + p.2 ^ 2) p.1.2 (rMinusW p / p.2) ≠ 0 ∧
      evalMap (F ℝ) q = ![p.1.1, alpha p.1 + p.2 ^ 2, p.1.2] ∧
      isIntegralCurveFrom q gamma I := by
  obtain ⟨W, Wp, alpha, rMinusW, hWOpen, hWBase, hWpOpen, hWpNonempty,
      hWpW, hReconstruction⟩ := exists_backwardPuncturedOpen
  obtain ⟨p, hp⟩ := hWpNonempty
  obtain ⟨hpPos, hpDen, hpEval⟩ := hReconstruction p hp
  let q : R3 := wallReconstruction p.1.1 (alpha p.1 + p.2 ^ 2) p.1.2
    (rMinusW p / p.2)
  obtain ⟨gamma, I, hgamma⟩ := exists_isIntegralCurveFrom q
  refine ⟨W, Wp, alpha, rMinusW, p, q, gamma, I, hWOpen, hWBase,
    hWpOpen, hWpW, hp, hpPos, rfl, hpDen, ?_, hgamma⟩
  simpa only [q] using hpEval

end ExoticCCR
