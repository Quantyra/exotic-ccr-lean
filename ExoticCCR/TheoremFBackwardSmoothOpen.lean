/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardPunctured

/-!
# Smooth open punctured reconstruction for the A001 backward wall

This module packages the local backward reconstruction germ on a nonempty open
positive-`tau` domain, retaining the exact smoothness data available from the
existing local germs.

The theorem stops at the reconstruction identity and does not claim any global
sheet, flow alignment, endpoint behavior, deficiency-space result, or release
status.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- Smallest smooth backward reconstruction package on a nonempty open positive-`tau` domain.

The theorem returns an open neighborhood `W` with smooth transverse wall data,
an open nonempty punctured subdomain `Wp ⊆ W`, and the guarded reconstruction
identity on `Wp`.
-/
theorem exists_backwardSmoothPuncturedOpen :
    ∃ (W Wp : Set ((ℝ × ℝ) × ℝ)) (alpha : ℝ × ℝ → ℝ)
      (rMinusW : ((ℝ × ℝ) × ℝ) → ℝ),
      IsOpen W ∧
      (((1 / 54), 2), 0) ∈ W ∧
      ContDiffOn ℝ ⊤ alpha (Prod.fst '' W) ∧
      ContDiffOn ℝ ⊤ rMinusW W ∧
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
  obtain ⟨W, alpha, rMinusW, hWOpen, hWBase, hAlpha, hRMinusW, hWall, hRoot,
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
  refine ⟨W, Wp, alpha, rMinusW, hWOpen, hWBase, hAlpha, hRMinusW,
    hWpOpen, hWpNonempty, ?_, ?_⟩
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
