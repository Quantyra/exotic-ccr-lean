/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFBackwardOpen

/-!
# Punctured local reconstruction for the A001 backward wall

This module records local denominator control near the distinguished backward
wall point. The statement is confined to the local reconstruction germ.
-/

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace ExoticCCR

/-- There is a backward reconstruction germ whose explicit reconstruction
denominator is nonzero at all sufficiently near punctured points of its domain. -/
theorem exists_backwardReconstruction_den_eventually :
    ∃ (W : Set ((ℝ × ℝ) × ℝ)) (alpha : ℝ × ℝ → ℝ)
      (rMinusW : ((ℝ × ℝ) × ℝ) → ℝ),
      IsOpen W ∧
      (((1 / 54), 2), 0) ∈ W ∧
      ContDiffOn ℝ ⊤ alpha (Prod.fst '' W) ∧
      ContDiffOn ℝ ⊤ rMinusW W ∧
      (∀ p ∈ W, wallA p.1.1 (alpha p.1) p.1.2 = 0) ∧
      (∀ p ∈ W,
        wallGMinus p.1.1 p.1.2 (alpha p.1) p.2 (rMinusW p) = 0) ∧
      (∀ p ∈ W, rMinusW p ≠ 0) ∧
      (∀ᶠ p in 𝓝 ((((1 / 54), 2), 0) : (ℝ × ℝ) × ℝ),
        p ∈ W → p.2 ≠ 0 →
          wallReconstructionDenom
            (alpha p.1 + p.2 ^ 2) p.1.2 (rMinusW p / p.2) ≠ 0) := by
  obtain ⟨W₀, alpha₀, rMinusW₀, hW₀Open, hW₀Base, _⟩ :=
    exists_backwardReconstructionGerm
  obtain ⟨U, alpha, hUOpen, hUBase, hAlpha, hAlphaBase, hWall, _⟩ :=
    exists_backwardWallAlpha_germ
  obtain ⟨V, rMinus, hVOpen, hVBase, hRMinus, hRMinusBase, hRoot, hRMinusNe⟩ :=
    exists_backwardBranchR_germ_varying_alpha
  let D : Set ((ℝ × ℝ) × ℝ) := Prod.fst ⁻¹' U
  let lift : ((ℝ × ℝ) × ℝ) → (((ℝ × ℝ) × ℝ) × ℝ) := fun p =>
    ((p.1, alpha p.1), p.2)
  let W : Set ((ℝ × ℝ) × ℝ) := W₀ ∩ (D ∩ lift ⁻¹' V)
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
  have hPulledOpen : IsOpen (D ∩ lift ⁻¹' V) := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpreimage : lift ⁻¹' V ∈ 𝓝 p := by
      have hpreimageWithin : lift ⁻¹' V ∈ 𝓝[D] p :=
        hLift.continuousOn p hp.1 (hVOpen.mem_nhds hp.2)
      rwa [hDOpen.nhdsWithin_eq hp.1] at hpreimageWithin
    exact inter_mem (hDOpen.mem_nhds hp.1) hpreimage
  have hWOpen : IsOpen W := hW₀Open.inter hPulledOpen
  have hWBase : (((1 / 54), 2), 0) ∈ W := by
    refine ⟨hW₀Base, hUBase, ?_⟩
    change ((((1 / 54), 2), alpha ((1 / 54), 2)), 0) ∈ V
    rw [hAlphaBase]
    exact hVBase
  have hAlphaW : ContDiffOn ℝ ⊤ alpha (Prod.fst '' W) := by
    apply hAlpha.mono
    rintro q ⟨p, hp, rfl⟩
    exact hp.2.1
  have hRMinusW : ContDiffOn ℝ ⊤ rMinusW W := by
    exact hRMinus.comp (hLift.mono fun _ hp => hp.2.1) fun _ hp => hp.2.2
  have hWallW : ∀ p ∈ W, wallA p.1.1 (alpha p.1) p.1.2 = 0 := by
    intro p hp
    exact hWall p.1 hp.2.1
  have hRootW : ∀ p ∈ W,
      wallGMinus p.1.1 p.1.2 (alpha p.1) p.2 (rMinusW p) = 0 := by
    intro p hp
    exact hRoot (lift p) hp.2.2
  have hRMinusWNe : ∀ p ∈ W, rMinusW p ≠ 0 := by
    intro p hp
    exact hRMinusNe (lift p) hp.2.2
  let k : ((ℝ × ℝ) × ℝ) → ℝ := fun p =>
    wallB (alpha p.1 + p.2 ^ 2) p.1.2 * rMinusW p + 3 * p.1.2 * p.2
  have hProjOpen : IsOpen (Prod.fst '' W) := isOpenMap_fst W hWOpen
  have hProjBase : ((1 / 54), 2) ∈ Prod.fst '' W :=
    ⟨(((1 / 54), 2), 0), hWBase, rfl⟩
  have hAlphaAt : ContDiffAt ℝ ⊤ alpha ((1 / 54), 2) :=
    hAlphaW.contDiffAt (hProjOpen.mem_nhds hProjBase)
  have hRMinusAt : ContDiffAt ℝ ⊤ rMinusW (((1 / 54), 2), 0) :=
    hRMinusW.contDiffAt (hWOpen.mem_nhds hWBase)
  have hRMinusWBase : rMinusW (((1 / 54), 2), 0) = Real.sqrt 6 := by
    dsimp [rMinusW, lift]
    rw [hAlphaBase]
    simpa using hRMinusBase
  have hkcont : ContinuousAt k (((1 / 54), 2), 0) := by
    unfold k wallB
    fun_prop
  have hkbase_eq : k (((1 / 54), 2), 0) = -Real.sqrt 6 := by
    norm_num [k, hAlphaBase, hRMinusWBase, wallB]
  have hkbase : k (((1 / 54), 2), 0) ≠ 0 := by
    rw [hkbase_eq]
    exact neg_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hden : ∀ᶠ p in 𝓝 ((((1 / 54), 2), 0) : (ℝ × ℝ) × ℝ),
      p ∈ W → p.2 ≠ 0 →
        wallReconstructionDenom
          (alpha p.1 + p.2 ^ 2) p.1.2 (rMinusW p / p.2) ≠ 0 := by
    filter_upwards [hkcont.eventually_ne hkbase] with p hkp hp hτ
    have hx : rMinusW p / p.2 ≠ 0 := div_ne_zero (hRMinusWNe p hp) hτ
    have hkrel :
        k p = p.2 *
          (wallB (alpha p.1 + p.2 ^ 2) p.1.2 * (rMinusW p / p.2) +
            3 * p.1.2) := by
      simp [k]
      field_simp [hτ]
    have hfactor :
        wallB (alpha p.1 + p.2 ^ 2) p.1.2 * (rMinusW p / p.2) +
          3 * p.1.2 ≠ 0 := by
      intro hz
      apply hkp
      rw [hkrel, hz, mul_zero]
    exact mul_ne_zero hx hfactor
  exact ⟨W, alpha, rMinusW, hWOpen, hWBase, hAlphaW, hRMinusW,
    hWallW, hRootW, hRMinusWNe, hden⟩

end ExoticCCR
