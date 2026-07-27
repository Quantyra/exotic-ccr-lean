/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFMaximalCoordinate

/-!
# Pointwise maximal extension of the forward branch sheet

The local branch collar can be extended backward, point by point, with the
canonical maximal integral curve through its regular lower face.  This module
records that extension and proves exact agreement at the interface and on the
overlap.  It deliberately does not package the result as a
`ForwardSaturatedSheet`: the present ODE API supplies no joint smoothness (or
even joint measurability) of the selected maximal curves in the transverse
parameter.  Consequently no ambient change of variables is claimed here.
-/

noncomputable section

open Filter Set
open scoped EReal Topology

namespace ExoticCCR

/-- Data for the pointwise maximal backward extension of a vertical branch
collar.  The lower alternative is stated in the original maximal-curve time,
where it follows directly from maximality. -/
structure ForwardMaximalSheet where
  S : ForwardBranchCrossSection
  W : Set (ℝ × ℝ)
  isOpen_W : IsOpen W
  nonempty_W : W.Nonempty
  W_subset : W ⊆ S.W
  vertical : ∀ x ∈ W, S.HasVerticalBranchSegment x
  tMax_eq : ∀ x ∈ W, tMax (S.qSigma x) = (S.ε₀ : EReal)
  escape_upper_branch : ∀ x ∈ W,
    Tendsto (fun t : ℝ => ‖S.branchTimeCurve x t‖) (𝓝[<] S.ε₀) atTop

namespace ForwardMaximalSheet

/-- Anchor `s` coordinate of the branch/maximal-curve interface. -/
def s0 (M : ForwardMaximalSheet) (x : ℝ × ℝ) : ℝ :=
  M.S.O.germ.β x - M.S.ε₀

/-- Lower endpoint in anchor `s` time. -/
def ℓ (M : ForwardMaximalSheet) (x : ℝ × ℝ) : EReal :=
  (M.s0 x : EReal) + tMin (M.S.qSigma x)

/-- Pointwise maximal extension, translated from maximal-curve time to anchor
`s` time. -/
def Psi (M : ForwardMaximalSheet) (p : (ℝ × ℝ) × ℝ) : R3 :=
  maximalIntegralCurve (M.S.qSigma p.1) (p.2 - M.s0 p.1)

/-- The translated maximal extension agrees exactly with the cross-section at
the branch interface. -/
@[simp] theorem Psi_s0 (M : ForwardMaximalSheet) (x : ℝ × ℝ) :
    M.Psi (x, M.s0 x) = M.S.qSigma x := by
  simp [Psi, maximalIntegralCurve_zero, exists_isIntegralCurveFrom]

/-- Every point of the translated maximal domain remains an `X1` integral
curve.  This is pointwise in the transverse parameter. -/
theorem hasDerivAt_Psi_s (M : ForwardMaximalSheet) {x : ℝ × ℝ} {s : ℝ}
    (hs : tMin (M.S.qSigma x) < ((s - M.s0 x : ℝ) : EReal) ∧
      ((s - M.s0 x : ℝ) : EReal) < tMax (M.S.qSigma x)) :
    HasDerivAt (fun u : ℝ => M.Psi (x, u)) (X1 (M.Psi (x, s))) s := by
  have h := hasDerivAt_maximalIntegralCurve hs
  simpa only [Psi, sub_eq_add_neg] using h.comp_add_const s (-(M.s0 x))

/-- On the forward overlap, the maximal extension is exactly the explicit
square-root branch reparameterization.  This is the interface cancellation
identity needed before splitting a characteristic integral. -/
theorem Psi_eq_branchTimeCurve (M : ForwardMaximalSheet) {x : ℝ × ℝ}
    (hx : x ∈ M.W) {s : ℝ} (hs : s ∈ Ioo (M.s0 x) (M.S.O.germ.β x)) :
    M.Psi (x, s) = M.S.branchTimeCurve x (s - M.s0 x) := by
  obtain ⟨η, hη, hcurve⟩ :=
    M.S.exists_branch_isIntegralCurveFrom (M.W_subset hx) (M.vertical x hx)
  apply maximalIntegralCurve_eq_of_mem hcurve
  change -η < s - M.s0 x ∧ s - M.s0 x < M.S.ε₀
  constructor
  · have : 0 < s - M.s0 x := sub_pos.mpr hs.1
    linarith
  · dsimp [s0] at hs ⊢
    calc
      s - (M.S.O.germ.β x - M.S.ε₀) <
          M.S.O.germ.β x - (M.S.O.germ.β x - M.S.ε₀) :=
        sub_lt_sub_right hs.2 _
      _ = M.S.ε₀ := by ring

/-- The two descriptions have the same trace at the regular interface.  The
identity is explicit so adjacent finite-interval IBP formulas can cancel this
trace rather than silently discard it. -/
theorem interface_trace_eq (M : ForwardMaximalSheet) (χ : ℝ × ℝ → ℂ)
    (φ : R3 → ℂ) (x : ℝ × ℝ) :
    inner ℂ (χ x) (φ (M.Psi (x, M.s0 x))) =
      inner ℂ (χ x) (φ (M.S.qSigma x)) := by
  rw [M.Psi_s0]

/-- The backward endpoint has only the two honest maximal alternatives:
negative infinity, or finite-time norm escape.  There is no regular third
face after extending through the cross-section. -/
theorem lower_eq_bot_or_exists_escape (M : ForwardMaximalSheet) (x : ℝ × ℝ) :
    tMin (M.S.qSigma x) = ⊥ ∨
      ∃ T : ℝ, tMin (M.S.qSigma x) = (T : EReal) ∧
        Tendsto (fun t : ℝ => ‖M.Psi (x, M.s0 x + t)‖) (𝓝[>] T) atTop := by
  rcases tMin_eq_bot_or_exists_escape (M.S.qSigma x) with h | ⟨T, hT, hesc⟩
  · exact Or.inl h
  · right
    refine ⟨T, hT, ?_⟩
    simpa [Psi] using hesc

end ForwardMaximalSheet

/-- Every forward branch contains a nonempty pointwise maximal sheet.  This is
not promoted to `ForwardSaturatedSheet` because joint transverse regularity of
`maximalIntegralCurve (qSigma x)` has not been established. -/
theorem ForwardBranchOpen.exists_forwardMaximalSheet (O : ForwardBranchOpen) :
    Nonempty ForwardMaximalSheet := by
  obtain ⟨S, hSO, W, hWopen, hWne, hWsub, hcollar⟩ :=
    O.exists_crossSection_with_verticalCollar_and_rPlus
  refine ⟨⟨S, W, hWopen, hWne, hWsub, fun x hx => (hcollar x hx).1, ?_, ?_⟩⟩
  · intro x hx
    apply S.tMax_qSigma_eq_ε₀_of_escape (hWsub hx) (hcollar x hx).1
    apply S.tendsto_norm_branchTimeCurve_of_one_le_rPlus x
    simpa [hSO] using (hcollar x hx).2
  · intro x hx
    apply S.tendsto_norm_branchTimeCurve_of_one_le_rPlus x
    simpa [hSO] using (hcollar x hx).2

end ExoticCCR
