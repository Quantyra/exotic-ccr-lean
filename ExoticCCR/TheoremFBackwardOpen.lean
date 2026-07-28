/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardWallAlpha

/-!
# Open local reconstruction germ for the A001 backward wall

This module pulls the varying-alpha root germ back along the local wall-alpha
function. It makes only a local statement on an open neighborhood of the
distinguished backward wall point.
-/

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- The local wall-alpha function and varying-alpha root germ compose to give
an open local root germ over `(a, c, tau)`. -/
theorem exists_backwardReconstructionGerm :
    ∃ (W : Set ((ℝ × ℝ) × ℝ)) (alpha : ℝ × ℝ → ℝ)
      (rMinusW : ((ℝ × ℝ) × ℝ) → ℝ),
      IsOpen W ∧
      (((1 / 54), 2), 0) ∈ W ∧
      ContDiffOn ℝ ⊤ alpha (Prod.fst '' W) ∧
      ContDiffOn ℝ ⊤ rMinusW W ∧
      (∀ p ∈ W, wallA p.1.1 (alpha p.1) p.1.2 = 0) ∧
      (∀ p ∈ W, wallGMinus p.1.1 p.1.2 (alpha p.1) p.2 (rMinusW p) = 0) ∧
      (∀ p ∈ W, rMinusW p ≠ 0) := by
  obtain ⟨U, alpha, hUOpen, hUBase, hAlpha, hAlphaBase, hWall, _⟩ :=
    exists_backwardWallAlpha_germ
  obtain ⟨V, rMinus, hVOpen, hVBase, hRMinus, _, hRoot, hRMinusNe⟩ :=
    exists_backwardBranchR_germ_varying_alpha
  let D : Set ((ℝ × ℝ) × ℝ) := Prod.fst ⁻¹' U
  let lift : ((ℝ × ℝ) × ℝ) → (((ℝ × ℝ) × ℝ) × ℝ) := fun p =>
    ((p.1, alpha p.1), p.2)
  let W : Set ((ℝ × ℝ) × ℝ) := D ∩ lift ⁻¹' V
  let rMinusW : ((ℝ × ℝ) × ℝ) → ℝ := fun p => rMinus (lift p)
  have hDOpen : IsOpen D := hUOpen.preimage continuous_fst
  have hLift : ContDiffOn ℝ ⊤ lift D := by
    intro p hp
    have hFst : ContDiffWithinAt ℝ ⊤
        (fun q : ((ℝ × ℝ) × ℝ) => q.1) D p :=
      contDiffAt_fst.contDiffWithinAt
    have hAlphaAt : ContDiffWithinAt ℝ ⊤
        (fun q : ((ℝ × ℝ) × ℝ) => alpha q.1) D p :=
      (hAlpha p.1 hp).comp p hFst fun _ hq => hq
    dsimp [lift]
    exact (hFst.prodMk hAlphaAt).prodMk contDiffAt_snd.contDiffWithinAt
  have hWOpen : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpreimage : lift ⁻¹' V ∈ 𝓝 p := by
      have hpreimageWithin : lift ⁻¹' V ∈ 𝓝[D] p :=
        hLift.continuousOn p hp.1 (hVOpen.mem_nhds hp.2)
      rwa [hDOpen.nhdsWithin_eq hp.1] at hpreimageWithin
    exact inter_mem (hDOpen.mem_nhds hp.1) hpreimage
  have hWBase : (((1 / 54), 2), 0) ∈ W := by
    refine ⟨hUBase, ?_⟩
    change ((((1 / 54), 2), alpha ((1 / 54), 2)), 0) ∈ V
    rw [hAlphaBase]
    exact hVBase
  refine ⟨W, alpha, rMinusW, hWOpen, hWBase, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hAlpha.mono (by
      rintro _ ⟨p, hp, rfl⟩
      exact hp.1) q hq
  · exact hRMinus.comp (hLift.mono inter_subset_left) fun _ hp => hp.2
  · intro p hp
    exact hWall p.1 hp.1
  · intro p hp
    exact hRoot (lift p) hp.2
  · intro p hp
    exact hRMinusNe (lift p) hp.2

end ExoticCCR
