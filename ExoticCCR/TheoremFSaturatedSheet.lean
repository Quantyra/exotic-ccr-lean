/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFForwardBranch
import ExoticCCR.TheoremEDeficiency
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.EReal.Basic

/-!
# Forward saturated sheets

This module first extracts an honest positive cross-section from the local
forward branch, and records the geometric data that a full forward sheet would
have to provide before an integration-by-parts argument can be attempted.  In
particular, both ends of every flow interval are explicit: the upper end
escapes, while the lower end is either `-∞` or a finite escaping end.

`ForwardBranchOpen` does not presently give an inhabitant of this structure.
It is a local `s = β - τ²` collar whose parameter domain need not contain a
whole interval in `s`, and only its wall-end escape has been proved.  Thus this
module deliberately proves no weak-adjoint statement and no Theorem E.
-/

noncomputable section

open Filter MvPolynomial Set
open scoped ContDiff EReal Topology

namespace ExoticCCR

/-- A positive constant-`τ` cross-section cut out of a local forward branch.

Its transverse set is the slice on which `(x, τ₀)` remains in the branch
domain.  The associated positive number `ε₀ = τ₀²` is the distance in the
anchor `s` coordinate from the wall. -/
structure ForwardBranchCrossSection where
  O : ForwardBranchOpen
  τ₀ : ℝ
  τ₀_pos : 0 < τ₀
  W : Set (ℝ × ℝ)
  W_eq : W = {x | (x, τ₀) ∈ O.W}
  isOpen_W : IsOpen W
  nonempty_W : W.Nonempty

namespace ForwardBranchCrossSection

/-- The positive wall offset of a branch cross-section. -/
def ε₀ (S : ForwardBranchCrossSection) : ℝ := S.τ₀ ^ 2

/-- The branch point over a transverse cross-section parameter. -/
def qSigma (S : ForwardBranchCrossSection) (x : ℝ × ℝ) : R3 :=
  S.O.germ.branchMap (x, S.τ₀)

/-- The cross-section offset is strictly positive. -/
theorem ε₀_pos (S : ForwardBranchCrossSection) : 0 < S.ε₀ := by
  exact sq_pos_of_pos S.τ₀_pos

/-- The chosen positive branch parameter is the square root of its offset. -/
theorem sqrt_ε₀ (S : ForwardBranchCrossSection) : Real.sqrt S.ε₀ = S.τ₀ := by
  rw [ε₀, Real.sqrt_sq_eq_abs, abs_of_pos S.τ₀_pos]

/-- The anchor map takes the cross-section to `s = β - ε₀`. -/
theorem evalMap_qSigma (S : ForwardBranchCrossSection) {x : ℝ × ℝ}
    (hx : x ∈ S.W) :
    evalMap (F ℝ) (S.qSigma x) =
      ![x.1, S.O.germ.β x - S.ε₀, x.2] := by
  have hx' : (x, S.τ₀) ∈ S.O.W := by simpa [S.W_eq] using hx
  simpa [qSigma, ε₀, ForwardBranchGerm.sCoord] using S.O.evalMap_branch hx'

/-- The cross-section map is smooth on its transverse open set. -/
theorem contDiffOn_qSigma (S : ForwardBranchCrossSection) :
    ContDiffOn ℝ ⊤ S.qSigma S.W := by
  intro x hx
  have hx' : (x, S.τ₀) ∈ S.O.W := by simpa [S.W_eq] using hx
  have hb : ContDiffAt ℝ ⊤ S.O.germ.branchMap (x, S.τ₀) :=
    (S.O.contDiff_branchMap (x, S.τ₀) hx').contDiffAt
      (S.O.isOpen_W.mem_nhds hx')
  have hi : ContDiffAt ℝ ⊤ (fun y : ℝ × ℝ => (y, S.τ₀)) x := by fun_prop
  exact (hb.comp x hi).contDiffWithinAt

/-- Distinct transverse parameters give distinct cross-section points. -/
theorem injOn_qSigma (S : ForwardBranchCrossSection) :
    Set.InjOn S.qSigma S.W := by
  intro x hx y hy hxy
  have hx' : (x, S.τ₀) ∈ S.O.W := by simpa [S.W_eq] using hx
  have hy' : (y, S.τ₀) ∈ S.O.W := by simpa [S.W_eq] using hy
  have hp := S.O.branchMap_injOn_Wpos
    (show (x, S.τ₀) ∈ S.O.Wpos from ⟨hx', S.τ₀_pos⟩)
    (show (y, S.τ₀) ∈ S.O.Wpos from ⟨hy', S.τ₀_pos⟩) hxy
  exact congrArg Prod.fst hp

end ForwardBranchCrossSection

/-- Every local forward branch contains a nonempty positive constant-`τ`
cross-section.  This is the rigorous cross-section step; it does not assert a
maximal flow extension or either lower-end alternative. -/
theorem ForwardBranchOpen.exists_crossSection (O : ForwardBranchOpen) :
    Nonempty ForwardBranchCrossSection := by
  obtain ⟨p, hpW, hpτ⟩ := O.nonempty_Wpos
  let W : Set (ℝ × ℝ) := {x | (x, p.2) ∈ O.W}
  have hWopen : IsOpen W := by
    exact O.isOpen_W.preimage (by fun_prop : Continuous fun x : ℝ × ℝ => (x, p.2))
  have hp1 : p.1 ∈ W := by simpa [W] using hpW
  exact ⟨⟨O, p.2, hpτ, W, rfl, hWopen, ⟨p.1, hp1⟩⟩⟩

/-- Picard--Lindelöf gives a two-sided local `X1` trajectory through every
point of the extracted cross-section.  The interval radius may depend on the
transverse parameter; this theorem is therefore local-flow existence, not a
uniform product collar and not a maximal saturated sheet. -/
theorem ForwardBranchCrossSection.exists_localFlowLine
    (S : ForwardBranchCrossSection) (x : ℝ × ℝ) (_hx : x ∈ S.W) :
    ∃ α : ℝ → R3, α 0 = S.qSigma x ∧ ∃ δ > 0,
      ∀ t ∈ Ioo (-δ) δ, HasDerivAt α (X1 (α t)) t := by
  have hX : ContDiffAt ℝ 1 X1 (S.qSigma x) :=
    (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
  simpa only [zero_sub, zero_add] using
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0

/-- A compact transverse core carrying one common local existence time.

This is the uniform local collar that follows directly from the cross-section.
The Picard--Lindelöf construction gives one jointly continuous flow map on the
compact transverse core and a common open time interval. -/
structure UniformLocalFlowCollar where
  S : ForwardBranchCrossSection
  x₀ : ℝ × ℝ
  ρ : ℝ
  ρ_pos : 0 < ρ
  W₀ : Set (ℝ × ℝ)
  W₀_eq : W₀ = Metric.closedBall x₀ ρ
  isCompact_W₀ : IsCompact W₀
  W₀_subset : W₀ ⊆ S.W
  δ : ℝ
  δ_pos : 0 < δ
  flowMap : (ℝ × ℝ) × ℝ → R3
  flowMap_zero : ∀ x ∈ W₀, flowMap (x, 0) = S.qSigma x
  continuousOn_flowMap : ContinuousOn flowMap (W₀ ×ˢ Ioo (-δ) δ)
  hasDerivAt_flowMap : ∀ x ∈ W₀, ∀ t ∈ Ioo (-δ) δ,
    HasDerivAt (fun u => flowMap (x, u)) (X1 (flowMap (x, t))) t

namespace UniformLocalFlowCollar

/-- Each transverse point in a uniform collar has the corresponding local
integral curve.  Unlike the earlier pointwise selection, all these curves are
slices of the same jointly continuous map. -/
theorem exists_flowLine (C : UniformLocalFlowCollar) (x : ℝ × ℝ) (hx : x ∈ C.W₀) :
    ∃ α : ℝ → R3, α 0 = C.S.qSigma x ∧
      ∀ t ∈ Ioo (-C.δ) C.δ, HasDerivAt α (X1 (α t)) t := by
  exact ⟨fun t => C.flowMap (x, t), C.flowMap_zero x hx,
    fun t ht => C.hasDerivAt_flowMap x hx t ht⟩

end UniformLocalFlowCollar

/-- Every positive branch cross-section contains a compact transverse ball on
which Picard--Lindelöf gives a uniform local lifetime. -/
theorem ForwardBranchCrossSection.exists_uniformLocalFlowCollar
    (S : ForwardBranchCrossSection) : Nonempty UniformLocalFlowCollar := by
  obtain ⟨x₀, hx₀⟩ := S.nonempty_W
  have hX : ContDiffAt ℝ 1 X1 (S.qSigma x₀) :=
    (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
  obtain ⟨δ, hδ, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hX
  obtain ⟨flow, hflow, hflow_cont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hqcd : ContDiffAt ℝ ⊤ S.qSigma x₀ :=
    (S.contDiffOn_qSigma x₀ hx₀).contDiffAt (S.isOpen_W.mem_nhds hx₀)
  have hq : ContinuousAt S.qSigma x₀ := hqcd.continuousAt
  have hpre : S.qSigma ⁻¹' Metric.ball (S.qSigma x₀) r ∈ 𝓝 x₀ :=
    hq (Metric.ball_mem_nhds _ hr)
  have hgood : S.W ∩ S.qSigma ⁻¹' Metric.ball (S.qSigma x₀) r ∈ 𝓝 x₀ :=
    inter_mem (S.isOpen_W.mem_nhds hx₀) hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let ρ := ε / 2
  let W₀ : Set (ℝ × ℝ) := Metric.closedBall x₀ ρ
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hWsub : W₀ ⊆ S.W ∩ S.qSigma ⁻¹' Metric.ball (S.qSigma x₀) r := by
    intro x hx
    apply hball
    rw [Metric.mem_ball]
    have hx' : dist x x₀ ≤ ρ := by
      simpa [W₀, dist_comm] using hx
    dsimp [ρ] at hx'
    linarith
  let flowMap : (ℝ × ℝ) × ℝ → R3 := fun p => flow (S.qSigma p.1, p.2)
  refine ⟨⟨S, x₀, ρ, hρ, W₀, rfl, ?_, ?_, δ, hδ, flowMap, ?_, ?_, ?_⟩⟩
  · simpa [W₀] using (isCompact_closedBall x₀ ρ)
  · intro x hx
    exact (hWsub hx).1
  · intro x hx
    apply (hflow (S.qSigma x) (Metric.ball_subset_closedBall (hWsub hx).2)).1
  · have hqcont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => S.qSigma p.1)
        (W₀ ×ˢ Ioo (-δ) δ) :=
      S.contDiffOn_qSigma.continuousOn.comp continuousOn_fst
        (fun p hp => (hWsub hp.1).1)
    apply hflow_cont.comp (hqcont.prodMk continuousOn_snd)
    intro p hp
    exact ⟨Metric.ball_subset_closedBall (hWsub hp.1).2,
      by simpa only [zero_sub, zero_add] using Ioo_subset_Icc_self hp.2⟩
  · intro x hx t ht
    have ht' : t ∈ Ioo (0 - δ) (0 + δ) := by
      simpa only [zero_sub, zero_add] using ht
    exact (hflow (S.qSigma x) (Metric.ball_subset_closedBall (hWsub hx).2)).2 t
      (Ioo_subset_Icc_self ht') |>.hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

/-- Every local forward branch therefore carries a compact uniform local flow
collar.  This still makes no maximal-time or endpoint-escape assertion. -/
theorem ForwardBranchOpen.exists_uniformLocalFlowCollar (O : ForwardBranchOpen) :
    Nonempty UniformLocalFlowCollar := by
  obtain ⟨S⟩ := O.exists_crossSection
  exact S.exists_uniformLocalFlowCollar

/-- A full forward flow sheet, including the endpoint data needed to account
for every boundary term in a future integration-by-parts proof.

The maps are total only for Lean convenience.  Their asserted geometric and
differential properties are restricted to `D`. -/
structure ForwardSaturatedSheet where
  /-- Transverse `(a,c)` parameters. -/
  W : Set (ℝ × ℝ)
  isOpen_W : IsOpen W
  nonempty_W : W.Nonempty
  /-- Finite upper flow time. -/
  β : ℝ × ℝ → ℝ
  contDiff_β : ContDiffOn ℝ ⊤ β W
  /-- Possibly infinite lower flow time. -/
  ℓ : ℝ × ℝ → EReal
  lower_lt_upper : ∀ x ∈ W, ℓ x < (β x : EReal)
  /-- The full open interval bundle over `W`. -/
  D : Set ((ℝ × ℝ) × ℝ)
  D_eq : D = {p | p.1 ∈ W ∧ ℓ p.1 < (p.2 : EReal) ∧ p.2 < β p.1}
  isOpen_D : IsOpen D
  /-- Flow-sheet parameterization. -/
  Psi : ((ℝ × ℝ) × ℝ) → R3
  contDiffOn_Psi : ContDiffOn ℝ ⊤ Psi D
  injOn_Psi : Set.InjOn Psi D
  /-- The anchor map reads off `(a,s,c)` on the sheet. -/
  evalMap_Psi : ∀ p ∈ D, evalMap (F ℝ) (Psi p) = ![p.1.1, p.2, p.1.2]
  /-- The `s`-lines are integral curves of `X1` throughout the sheet. -/
  hasDerivAt_Psi_s : ∀ x s, (x, s) ∈ D →
    HasDerivAt (fun t : ℝ => Psi (x, t)) (X1 (Psi (x, s))) s
  /-- Every upper endpoint escapes all compact norm balls. -/
  escape_upper : ∀ x ∈ W,
    Tendsto (fun s : ℝ => ‖Psi (x, s)‖) (𝓝[<] β x) atTop
  /-- A lower endpoint is either `-∞`, or finite and escaping from the right.
  This disjunction prevents a finite lower boundary from being silently
  discarded in integration by parts. -/
  lower_ok : ∀ x ∈ W,
    ℓ x = ⊥ ∨ ∃ L : ℝ, ℓ x = (L : EReal) ∧
      Tendsto (fun s : ℝ => ‖Psi (x, s)‖) (𝓝[>] L) atTop

namespace ForwardSaturatedSheet

/-- Membership in a saturated-sheet domain is exactly membership in its full
open interval bundle. -/
theorem mem_D_iff (S : ForwardSaturatedSheet) (x : ℝ × ℝ) (s : ℝ) :
    (x, s) ∈ S.D ↔ x ∈ S.W ∧ S.ℓ x < (s : EReal) ∧ s < S.β x := by
  rw [S.D_eq]
  rfl

end ForwardSaturatedSheet

end ExoticCCR
