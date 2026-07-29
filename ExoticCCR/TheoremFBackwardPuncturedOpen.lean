/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardPunctured

/-!
# Open punctured local reconstruction for the A001 backward wall

This module extracts a nonempty open positive-`tau` subdomain from the local
backward reconstruction germ. The result remains entirely local to the wall.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped Topology

namespace ExoticCCR

/-- The local backward reconstruction germ contains a nonempty open positive-`tau`
subdomain on which the guarded reconstruction formula is valid. -/
theorem exists_backwardPuncturedOpen :
    ∃ (W Wp : Set ((ℝ × ℝ) × ℝ)) (alpha : ℝ × ℝ → ℝ)
      (rMinusW : ((ℝ × ℝ) × ℝ) → ℝ),
      IsOpen W ∧
      (((1 / 54), 2), 0) ∈ W ∧
      IsOpen Wp ∧
      Wp.Nonempty ∧
      Wp ⊆ W ∧
      ∀ p ∈ Wp,
        0 < p.2 ∧
        wallReconstructionDenom
          (alpha p.1 + p.2 ^ 2) p.1.2 (rMinusW p / p.2) ≠ 0 ∧
        evalMap (F ℝ)
            (wallReconstruction p.1.1 (alpha p.1 + p.2 ^ 2) p.1.2
              (rMinusW p / p.2)) =
          ![p.1.1, alpha p.1 + p.2 ^ 2, p.1.2] := by
  obtain ⟨W, alpha, rMinusW, hWOpen, hWBase, _, _, hWall, hRoot,
      hRMinusWNe, hDenEventually⟩ :=
    exists_backwardReconstruction_den_eventually
  have hDenMem :
      {p : (ℝ × ℝ) × ℝ | p ∈ W → p.2 ≠ 0 →
        wallReconstructionDenom
          (alpha p.1 + p.2 ^ 2) p.1.2 (rMinusW p / p.2) ≠ 0} ∈
        𝓝 ((((1 / 54), 2), 0) : (ℝ × ℝ) × ℝ) :=
    hDenEventually
  obtain ⟨N, hNSub, hNOpen, hBaseN⟩ := mem_nhds_iff.mp hDenMem
  let Wp : Set ((ℝ × ℝ) × ℝ) := W ∩ N ∩ {p | 0 < p.2}
  have hWpOpen : IsOpen Wp := by
    exact (hWOpen.inter hNOpen).inter (isOpen_lt continuous_const continuous_snd)
  have hWN : W ∩ N ∈ 𝓝 ((((1 / 54), 2), 0) : (ℝ × ℝ) × ℝ) :=
    (hWOpen.inter hNOpen).mem_nhds ⟨hWBase, hBaseN⟩
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hWN
  let p : (ℝ × ℝ) × ℝ := (((1 / 54), 2), ε / 2)
  have hpBall : p ∈ Metric.ball ((((1 / 54), 2), 0) : (ℝ × ℝ) × ℝ) ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [p, abs_of_pos hε]
    linarith
  have hpWN : p ∈ W ∩ N := hBall hpBall
  have hWpNonempty : Wp.Nonempty := by
    refine ⟨p, ⟨⟨hpWN.1, hpWN.2⟩, ?_⟩⟩
    dsimp [p]
    linarith
  refine ⟨W, Wp, alpha, rMinusW, hWOpen, hWBase, hWpOpen, hWpNonempty,
    ?_, ?_⟩
  · intro q hq
    exact hq.1.1
  · intro q hq
    have hqW : q ∈ W := hq.1.1
    have hqN : q ∈ N := hq.1.2
    have hqTau : 0 < q.2 := hq.2
    have hqTauNe : q.2 ≠ 0 := ne_of_gt hqTau
    have hqDen := hNSub hqN hqW hqTauNe
    refine ⟨hqTau, hqDen, ?_⟩
    exact evalMap_F_wallReconstruction_of_wallGMinus hqTauNe
      (hRMinusWNe q hqW) (hWall q hqW) (hRoot q hqW) hqDen

end ExoticCCR
