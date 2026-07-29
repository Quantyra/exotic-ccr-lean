/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardReconstruction

/-!
# Backward characteristic prerequisite for Theorem F

This file records the smallest honest next step toward a backward characteristic:
the explicit reconstruction map is smooth at any point where its displayed
denominators are nonzero.

The actual characteristic theorem would still need a separate API identifying the
reconstructed curve with `X1`; that link is not present in the current source,
so this file stops at the derivative-compatible prerequisite.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- Smallest backward-characteristic prerequisite: the explicit reconstruction
map is `ContDiffAt` in the root variable whenever the two displayed denominators
are nonzero. This does not yet assert that the map is a characteristic curve. -/
theorem contDiffAt_wallReconstruction
    {a s c x : ℝ} (hx : x ≠ 0) (hden : wallReconstructionDenom s c x ≠ 0) :
    ContDiffAt ℝ ⊤ (wallReconstruction a s c) x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · change ContDiffAt ℝ ⊤ (fun y : ℝ => y) x
    fun_prop
  · have hq1 : ContDiffAt ℝ ⊤ (fun y : ℝ => wallReconstructQ1 a s c y) x := by
      unfold wallReconstructQ1 wallReconstructionDenom wallB
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa [wallReconstructionDenom, wallB] using hden
    simpa [wallReconstruction] using hq1
  · have hq1 : ContDiffAt ℝ ⊤ (fun y : ℝ => wallReconstructQ1 a s c y) x := by
      unfold wallReconstructQ1 wallReconstructionDenom wallB
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa [wallReconstructionDenom, wallB] using hden
    have hq2 : ContDiffAt ℝ ⊤ (fun y : ℝ => wallReconstructQ2 a s c y) x := by
      unfold wallReconstructQ2
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · exact pow_ne_zero 3 hx
    simpa [wallReconstruction] using hq2

end ExoticCCR
