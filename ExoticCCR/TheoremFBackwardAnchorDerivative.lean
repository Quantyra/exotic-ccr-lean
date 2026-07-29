/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TransportOperator
import ExoticCCR.TheoremFBackwardSmoothOpen
import ExoticCCR.TheoremFBackwardReconstructionSmooth

/-!
# Anchor derivative for the backward reconstruction line

This file isolates the local derivative statement for the backward reconstruction
line on an open punctured domain. The proof uses only local openness plus the
guarded reconstruction identity.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- The backward reconstruction line has the expected anchor derivative at any
point of the open punctured domain with positive `tau`. -/
theorem hasDerivAt_backwardAnchorDerivative
    (W Wp : Set ((ℝ × ℝ) × ℝ)) (alpha : ℝ × ℝ → ℝ)
    (rMinusW : ((ℝ × ℝ) × ℝ) → ℝ)
    (hWpOpen : IsOpen Wp) (_hWpSub : Wp ⊆ W)
    (_hR : ContDiffOn ℝ ⊤ rMinusW W)
    (hRecon : ∀ q ∈ Wp,
    evalMap (F ℝ)
        (wallReconstruction q.1.1 (alpha q.1 + q.2 ^ 2) q.1.2
          (rMinusW q / q.2)) =
      (![q.1.1, alpha q.1 + q.2 ^ 2, q.1.2] : R3))
    {p : ((ℝ × ℝ) × ℝ)} (hp : p ∈ Wp) (_hp2 : 0 < p.2)
    (_hden : wallReconstructionDenom
      (alpha p.1 + p.2 ^ 2) p.1.2 (rMinusW p / p.2) ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        evalMap (F ℝ)
          (wallReconstruction p.1.1 (alpha p.1 + t ^ 2) p.1.2
            (rMinusW (p.1, t) / t)))
      (![0, 2 * p.2, 0] : R3) p.2 := by
  have hlineOpen : IsOpen {t : ℝ | (p.1, t) ∈ Wp} :=
    hWpOpen.preimage (continuous_const.prodMk continuous_id)
  have hline : {t : ℝ | (p.1, t) ∈ Wp} ∈ 𝓝 p.2 :=
    hlineOpen.mem_nhds (by simpa using hp)
  have heq :
      (fun t : ℝ =>
        evalMap (F ℝ)
          (wallReconstruction p.1.1 (alpha p.1 + t ^ 2) p.1.2
            (rMinusW (p.1, t) / t))) =ᶠ[𝓝 p.2]
      (fun t : ℝ => (![p.1.1, alpha p.1 + t ^ 2, p.1.2] : R3)) := by
    filter_upwards [hline] with t ht
    simpa using hRecon (p.1, t) ht
  have htarget :
    HasDerivAt (fun t : ℝ => (![p.1.1, alpha p.1 + t ^ 2, p.1.2] : R3))
        (![0, 2 * p.2, 0] : R3) p.2 := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using (hasDerivAt_const p.2 (p.1.1 : ℝ))
    · have hsq0 : HasDerivAt (fun t : ℝ => t * t) (p.2 + p.2) p.2 := by
        change HasDerivAt (id * id) (p.2 + p.2) p.2
        have hprod : HasDerivAt (id * id) (1 * id p.2 + id p.2 * 1) p.2 :=
          (hasDerivAt_id p.2).mul (hasDerivAt_id p.2)
        simpa using hprod
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * p.2) p.2 := by
        simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using hsq0
      simpa [add_comm, add_left_comm, add_assoc] using
        hsq.add_const (alpha p.1)
    · simpa using (hasDerivAt_const p.2 (p.1.2 : ℝ))
  exact htarget.congr_of_eventuallyEq heq

end ExoticCCR
