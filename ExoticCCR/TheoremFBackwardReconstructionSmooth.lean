/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardWall

/-!
# Smooth local backward reconstruction prerequisite for Theorem F

This file isolates the smallest local smoothness statement for the explicit
backward reconstruction map at a point where its displayed denominators are
nonzero.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- The explicit backward reconstruction map is `ContDiffAt` at any point where
the root variable and reconstruction denominator are nonzero. -/
theorem contDiffAt_wallReconstruction_pair
    {a c : ℝ} {z : ℝ × ℝ} (hz : z.2 ≠ 0)
    (hden : wallReconstructionDenom z.1 c z.2 ≠ 0) :
    ContDiffAt ℝ ⊤ (fun w : ℝ × ℝ => wallReconstruction a w.1 c w.2) z := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · change ContDiffAt ℝ ⊤ (fun w : ℝ × ℝ => w.2) z
    fun_prop
  · have hq1 : ContDiffAt ℝ ⊤ (fun w : ℝ × ℝ => wallReconstructQ1 a w.1 c w.2) z := by
      unfold wallReconstructQ1 wallReconstructionDenom wallB
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa [wallReconstructionDenom, wallB] using hden
    simpa [wallReconstruction] using hq1
  · have hq1 : ContDiffAt ℝ ⊤ (fun w : ℝ × ℝ => wallReconstructQ1 a w.1 c w.2) z := by
      unfold wallReconstructQ1 wallReconstructionDenom wallB
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa [wallReconstructionDenom, wallB] using hden
    have hq2 : ContDiffAt ℝ ⊤ (fun w : ℝ × ℝ => wallReconstructQ2 a w.1 c w.2) z := by
      unfold wallReconstructQ2
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · exact pow_ne_zero 3 hz
    simpa [wallReconstruction] using hq2

end ExoticCCR
