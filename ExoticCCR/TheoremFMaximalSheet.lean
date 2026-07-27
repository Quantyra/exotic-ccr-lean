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
overlap.  The local Picard collar in `TheoremFSaturatedSheet` now identifies
the selected maximal curves with a jointly continuous flow on a nonempty open
product collar, and `TheoremFSaturatedSheet` proves general compact-base,
compact-time joint continuity for the ambient maximal flow.  This file still
does not package the translated variable-domain extension as a
`ForwardSaturatedSheet`; the needed global measurable/change-of-variables
infrastructure is not claimed here.
-/

noncomputable section

open Filter MvPolynomial Set
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

/-- The translated total domain of the maximal sheet. -/
def D (M : ForwardMaximalSheet) : Set ((ℝ × ℝ) × ℝ) :=
  {p | p.1 ∈ M.W ∧ p.2 - M.s0 p.1 ∈ integralCurveDomain (M.S.qSigma p.1)}

theorem continuousAt_s0 (M : ForwardMaximalSheet) {x : ℝ × ℝ} (hx : x ∈ M.W) :
    ContinuousAt M.s0 x := by
  have hxS : x ∈ M.S.W := M.W_subset hx
  have hxBranch : (x, M.S.τ₀) ∈ M.S.O.W := by
    simpa [M.S.W_eq] using hxS
  have hxU : x ∈ M.S.O.germ.U :=
    M.S.O.germ.proj_mem _ (M.S.O.subset_V hxBranch)
  exact ((M.S.O.germ.contDiff_β.contDiffAt
    (M.S.O.germ.isOpen_U.mem_nhds hxU)).continuousAt).sub continuousAt_const

/-- The translated maximal sheet has an open variable domain. -/
theorem isOpen_D (M : ForwardMaximalSheet) : IsOpen M.D := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hq : ContinuousAt M.S.qSigma p.1 :=
    (M.S.contDiffOn_qSigma p.1 (M.W_subset hp.1)).contDiffAt
      (M.S.isOpen_W.mem_nhds (M.W_subset hp.1)) |>.continuousAt
  have hmap : ContinuousAt (fun q : (ℝ × ℝ) × ℝ =>
      (M.S.qSigma q.1, q.2 - M.s0 q.1)) p :=
    (hq.comp continuousAt_fst).prodMk
      (continuousAt_snd.sub ((M.continuousAt_s0 hp.1).comp continuousAt_fst))
  have hflowDomain :
      {q : R3 × ℝ | q.2 ∈ integralCurveDomain q.1} ∈
        𝓝 (M.S.qSigma p.1, p.2 - M.s0 p.1) :=
    isOpen_maximalIntegralCurve_domain_bundle.mem_nhds hp.2
  have hbase : {q : (ℝ × ℝ) × ℝ | q.1 ∈ M.W} ∈ 𝓝 p :=
    (M.isOpen_W.preimage continuous_fst).mem_nhds hp.1
  apply mem_of_superset (inter_mem hbase (hmap hflowDomain))
  rintro q ⟨hqW, hqDom⟩
  exact ⟨hqW, hqDom⟩

/-- The translated maximal sheet is jointly continuous on its full open
variable domain. -/
theorem continuousOn_Psi (M : ForwardMaximalSheet) : ContinuousOn M.Psi M.D := by
  intro p hp
  have hq : ContinuousAt M.S.qSigma p.1 :=
    (M.S.contDiffOn_qSigma p.1 (M.W_subset hp.1)).contDiffAt
      (M.S.isOpen_W.mem_nhds (M.W_subset hp.1)) |>.continuousAt
  have hmap : ContinuousAt (fun q : (ℝ × ℝ) × ℝ =>
      (M.S.qSigma q.1, q.2 - M.s0 q.1)) p :=
    (hq.comp continuousAt_fst).prodMk
      (continuousAt_snd.sub ((M.continuousAt_s0 hp.1).comp continuousAt_fst))
  exact (continuousAt_maximalIntegralCurve_of_mem hp.2).comp_of_eq hmap rfl
    |>.continuousWithinAt

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

/-- The maximal sheet is a right inverse of the anchor map on its translated
maximal domain.  Thus the two transverse anchor coordinates stay fixed and
the middle anchor coordinate is exactly the sheet time. -/
theorem evalMap_Psi (M : ForwardMaximalSheet) {x : ℝ × ℝ} (hx : x ∈ M.W)
    {s : ℝ}
    (hs : tMin (M.S.qSigma x) < ((s - M.s0 x : ℝ) : EReal) ∧
      ((s - M.s0 x : ℝ) : EReal) < tMax (M.S.qSigma x)) :
    evalMap (F ℝ) (M.Psi (x, s)) = ![x.1, s, x.2] := by
  have ht : s - M.s0 x ∈ integralCurveDomain (M.S.qSigma x) :=
    (mem_integralCurveDomain_iff _ _).2 hs
  rw [Psi, evalMap_maximalIntegralCurve ht, M.S.evalMap_qSigma (M.W_subset hx)]
  ext i
  fin_cases i <;> simp [s0] <;> ring

/-- Anchor coordinates make the maximal sheet injective on its full domain. -/
theorem injOn_Psi (M : ForwardMaximalSheet) : Set.InjOn M.Psi M.D := by
  intro p hp q hq hpq
  have hpEval := M.evalMap_Psi hp.1
    ((mem_integralCurveDomain_iff _ _).1 hp.2)
  have hqEval := M.evalMap_Psi hq.1
    ((mem_integralCurveDomain_iff _ _).1 hq.2)
  have hcoords : (![p.1.1, p.2, p.1.2] : R3) = ![q.1.1, q.2, q.1.2] := by
    rw [← hpEval, ← hqEval, hpq]
  apply Prod.ext
  · apply Prod.ext
    · simpa using congrFun hcoords (0 : Fin 3)
    · simpa using congrFun hcoords (2 : Fin 3)
  · simpa using congrFun hcoords (1 : Fin 3)

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
not promoted to `ForwardSaturatedSheet`: although compact-subdomain joint
continuity of the ambient maximal flow is available, the translated variable
domain has not yet been supplied with all fields required by that structure. -/
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
