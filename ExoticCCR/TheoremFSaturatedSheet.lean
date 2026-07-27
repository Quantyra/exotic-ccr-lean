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

This module extracts an honest positive cross-section from the local forward
branch and records the geometric data of a forward sheet.  In
`TheoremFMaximalCoordinate` the sheet is inhabited directly by the smooth local
branch after square-root reparameterization; no abstract joint smoothness of a
maximal flow is used.

The lower face of that sheet is the regular cross-section, not an escaping end.
It must therefore be retained in any future integration-by-parts argument and
handled by support or an estimate.  This module deliberately proves no
integration-by-parts, weak-adjoint, or Theorem E statement.
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

/-- A connected open integral curve of `X1` through `x₀` at time zero. -/
def isIntegralCurveFrom (x₀ : R3) (α : ℝ → R3) (I : Set ℝ) : Prop :=
  0 ∈ I ∧ IsOpen I ∧ IsConnected I ∧ α 0 = x₀ ∧
    ∀ t ∈ I, HasDerivAt α (X1 (α t)) t

/-- The union of the domains of all connected open integral curves through
`x₀`.  This is the natural domain of the maximal integral curve. -/
def integralCurveDomain (x₀ : R3) : Set ℝ :=
  {t | ∃ α I, isIntegralCurveFrom x₀ α I ∧ t ∈ I}

/-- Nonnegative times reached by some connected integral curve through `x₀`. -/
def forwardReachableTimes (x₀ : R3) : Set ℝ :=
  {t | 0 ≤ t ∧ ∃ α I, isIntegralCurveFrom x₀ α I ∧ t ∈ I}

/-- Nonpositive times reached by some connected integral curve through `x₀`. -/
def backwardReachableTimes (x₀ : R3) : Set ℝ :=
  {t | t ≤ 0 ∧ ∃ α I, isIntegralCurveFrom x₀ α I ∧ t ∈ I}

/-- The extended-real supremum of forward times reached by local solutions. -/
def tMax (x₀ : R3) : EReal :=
  sSup ((fun t : ℝ => (t : EReal)) '' integralCurveDomain x₀)

/-- The extended-real infimum of backward times reached by local solutions. -/
def tMin (x₀ : R3) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' integralCurveDomain x₀)

/-- A local flow line supplies an honest connected-open partial trajectory. -/
theorem ForwardBranchCrossSection.exists_isIntegralCurveFrom
    (S : ForwardBranchCrossSection) (x : ℝ × ℝ) (hx : x ∈ S.W) :
    ∃ α I, isIntegralCurveFrom (S.qSigma x) α I := by
  obtain ⟨α, hα0, δ, hδ, hα⟩ := S.exists_localFlowLine x hx
  refine ⟨α, Ioo (-δ) δ, ?_⟩
  exact ⟨by simp [hδ], isOpen_Ioo, isConnected_Ioo (by linarith), hα0, hα⟩

/-- Smoothness of `X1` supplies a connected open integral curve through every
ambient point. -/
theorem exists_isIntegralCurveFrom (x₀ : R3) :
    ∃ α I, isIntegralCurveFrom x₀ α I := by
  have hX : ContDiffAt ℝ 1 X1 x₀ :=
    (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
  obtain ⟨α, hα0, δ, hδ, hα⟩ :=
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  exact ⟨α, Ioo (-δ) δ,
    ⟨by simp [hδ], isOpen_Ioo, isConnected_Ioo (by linarith), hα0,
      by simpa only [zero_sub, zero_add] using hα⟩⟩

/-- Smoothness of `X1` gives the local ODE uniqueness needed when two partial
curves are glued.  The conclusion is deliberately local; connected-interval
propagation and construction of a maximal representative remain separate. -/
theorem isIntegralCurveFrom.eventuallyEq_of_eq
    {x₀ : R3} {α γ : ℝ → R3} {I J : Set ℝ} {t₀ : ℝ}
    (hα : isIntegralCurveFrom x₀ α I) (hγ : isIntegralCurveFrom x₀ γ J)
    (htI : t₀ ∈ I) (htJ : t₀ ∈ J) (heq : α t₀ = γ t₀) :
    α =ᶠ[𝓝 t₀] γ := by
  obtain ⟨K, U, hU, hLip⟩ :=
    (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
      |>.exists_lipschitzOnWith
  have hαI : ∀ᶠ t in 𝓝 t₀, t ∈ I := hα.2.1.mem_nhds htI
  have hγJ : ∀ᶠ t in 𝓝 t₀, t ∈ J := hγ.2.1.mem_nhds htJ
  have hαU : ∀ᶠ t in 𝓝 t₀, α t ∈ U :=
    (hα.2.2.2.2 t₀ htI).continuousAt hU
  have hγU : ∀ᶠ t in 𝓝 t₀, γ t ∈ U := by
    have hU' : U ∈ 𝓝 (γ t₀) := by simpa [heq] using hU
    exact (hγ.2.2.2.2 t₀ htJ).continuousAt hU'
  apply ODE_solution_unique_of_eventually
      (v := fun _ => X1) (s := fun _ => U) (K := K)
  · exact Filter.Eventually.of_forall fun _ => hLip
  · filter_upwards [hαI, hαU] with t ht htu
    exact ⟨hα.2.2.2.2 t ht, htu⟩
  · filter_upwards [hγJ, hγU] with t ht htu
    exact ⟨hγ.2.2.2.2 t ht, htu⟩
  · exact heq

/-- Two connected partial trajectories through the same initial point agree
wherever both are defined.  Local Picard--Lindelöf uniqueness propagates over
the connected overlap. -/
theorem isIntegralCurveFrom.eqOn_inter
    {x₀ : R3} {α γ : ℝ → R3} {I J : Set ℝ}
    (hα : isIntegralCurveFrom x₀ α I) (hγ : isIntegralCurveFrom x₀ γ J) :
    Set.EqOn α γ (I ∩ J) := by
  let K : Set ℝ := I ∩ J
  have hKpre : IsPreconnected K := by
    rw [isPreconnected_iff_ordConnected]
    exact hα.2.2.1.2.ordConnected.inter hγ.2.2.1.2.ordConnected
  let P : ℝ → ℝ → Prop := fun s t => (α s = γ s ↔ α t = γ t)
  have hlocal : ∀ t ∈ K, ∀ᶠ u in 𝓝[K] t, P t u := by
    intro t ht
    by_cases heq : α t = γ t
    · have huv := hα.eventuallyEq_of_eq hγ ht.1 ht.2 heq
      filter_upwards [huv.filter_mono inf_le_left] with u hu
      exact ⟨fun _ => hu, fun _ => heq⟩
    · have hαc := (hα.2.2.2.2 t ht.1).continuousAt
      have hγc := (hγ.2.2.2.2 t ht.2).continuousAt
      have hne : ∀ᶠ u in 𝓝 t, α u - γ u ≠ 0 :=
        (hαc.sub hγc).eventually_ne (sub_ne_zero.mpr heq)
      filter_upwards [hne.filter_mono inf_le_left] with u hu
      exact ⟨fun h => (heq h).elim, fun h => (hu (sub_eq_zero.mpr h)).elim⟩
  have hprop : ∀ s t, s ∈ K → t ∈ K → P s t := by
    intro s t hs ht
    apply hKpre.induction₂ P hlocal
    · intro a b c _ _ _ hab hbc
      exact hab.trans hbc
    · intro a b _ _ hab
      exact hab.symm
    · exact hs
    · exact ht
  intro t ht
  have h0 : (0 : ℝ) ∈ K := ⟨hα.1, hγ.1⟩
  exact (hprop 0 t h0 ht).mp (hα.2.2.2.1.trans hγ.2.2.2.1.symm)

/-- Two integral curves of `X1` agree on their connected overlap if they agree
at one point of that overlap.  Unlike `isIntegralCurveFrom.eqOn_inter`, this
version does not require the curves to use the same time-zero base point. -/
theorem integralCurve_eqOn_inter_of_eq
    {α γ : ℝ → R3} {I J : Set ℝ} {t₀ : ℝ}
    (hIopen : IsOpen I) (hIconn : IsConnected I)
    (hJopen : IsOpen J) (hJconn : IsConnected J)
    (hα : ∀ t ∈ I, HasDerivAt α (X1 (α t)) t)
    (hγ : ∀ t ∈ J, HasDerivAt γ (X1 (γ t)) t)
    (htI : t₀ ∈ I) (htJ : t₀ ∈ J) (heq : α t₀ = γ t₀) :
    Set.EqOn α γ (I ∩ J) := by
  let K : Set ℝ := I ∩ J
  have hKpre : IsPreconnected K := by
    rw [isPreconnected_iff_ordConnected]
    exact hIconn.2.ordConnected.inter hJconn.2.ordConnected
  let P : ℝ → ℝ → Prop := fun s t => (α s = γ s ↔ α t = γ t)
  have hlocal : ∀ t ∈ K, ∀ᶠ u in 𝓝[K] t, P t u := by
    intro t ht
    by_cases hEq : α t = γ t
    · obtain ⟨L, U, hU, hLip⟩ :=
        (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
          |>.exists_lipschitzOnWith
      have hαI : ∀ᶠ u in 𝓝 t, u ∈ I := hIopen.mem_nhds ht.1
      have hγJ : ∀ᶠ u in 𝓝 t, u ∈ J := hJopen.mem_nhds ht.2
      have hαU : ∀ᶠ u in 𝓝 t, α u ∈ U := (hα t ht.1).continuousAt hU
      have hγU : ∀ᶠ u in 𝓝 t, γ u ∈ U := by
        have hU' : U ∈ 𝓝 (γ t) := by simpa [hEq] using hU
        exact (hγ t ht.2).continuousAt hU'
      have huv : α =ᶠ[𝓝 t] γ := by
        apply ODE_solution_unique_of_eventually
            (v := fun _ => X1) (s := fun _ => U) (K := L)
        · exact Filter.Eventually.of_forall fun _ => hLip
        · filter_upwards [hαI, hαU] with u huI huU
          exact ⟨hα u huI, huU⟩
        · filter_upwards [hγJ, hγU] with u huJ huU
          exact ⟨hγ u huJ, huU⟩
        · exact hEq
      filter_upwards [huv.filter_mono inf_le_left] with u hu
      exact ⟨fun _ => hu, fun _ => hEq⟩
    · have hαc := (hα t ht.1).continuousAt
      have hγc := (hγ t ht.2).continuousAt
      have hne : ∀ᶠ u in 𝓝 t, α u - γ u ≠ 0 :=
        (hαc.sub hγc).eventually_ne (sub_ne_zero.mpr hEq)
      filter_upwards [hne.filter_mono inf_le_left] with u hu
      exact ⟨fun h => (hEq h).elim, fun h => (hu (sub_eq_zero.mpr h)).elim⟩
  have hprop : ∀ s t, s ∈ K → t ∈ K → P s t := by
    intro s t hs ht
    apply hKpre.induction₂ P hlocal
    · intro a b c _ _ _ hab hbc
      exact hab.trans hbc
    · intro a b _ _ hab
      exact hab.symm
    · exact hs
    · exact ht
  intro t ht
  exact (hprop t₀ t ⟨htI, htJ⟩ ht).mp heq

/-- The pointwise gluing used to extend an integral curve. -/
def gluedIntegralCurve (I : Set ℝ) (α γ : ℝ → R3) : ℝ → R3 := by
  classical
  exact I.piecewise α γ

/-- Patch a connected open integral curve with an overlapping local extension. -/
theorem isIntegralCurveFrom.extend
    {x₀ : R3} {α γ : ℝ → R3} {I J : Set ℝ} {t₀ : ℝ}
    (hα : isIntegralCurveFrom x₀ α I)
    (hJopen : IsOpen J) (hJconn : IsConnected J)
    (hγ : ∀ t ∈ J, HasDerivAt γ (X1 (γ t)) t)
    (htI : t₀ ∈ I) (htJ : t₀ ∈ J) (heq : α t₀ = γ t₀) :
    isIntegralCurveFrom x₀ (gluedIntegralCurve I α γ) (I ∪ J) := by
  classical
  have hagree := integralCurve_eqOn_inter_of_eq hα.2.1 hα.2.2.1 hJopen hJconn
    hα.2.2.2.2 hγ htI htJ heq
  refine ⟨Or.inl hα.1, hα.2.1.union hJopen,
    IsConnected.union ⟨t₀, htI, htJ⟩ hα.2.2.1 hJconn, ?_, ?_⟩
  · simp [gluedIntegralCurve, hα.1, hα.2.2.2.1]
  · intro t ht
    by_cases htI' : t ∈ I
    · have hevent : gluedIntegralCurve I α γ =ᶠ[𝓝 t] α := by
        filter_upwards [hα.2.1.mem_nhds htI'] with u hu
        simp [gluedIntegralCurve, hu]
      exact ((hα.2.2.2.2 t htI').congr_of_eventuallyEq hevent).congr_deriv
        (congrArg X1 hevent.self_of_nhds.symm)
    · have htJ' : t ∈ J := ht.resolve_left htI'
      have hevent : gluedIntegralCurve I α γ =ᶠ[𝓝 t] γ := by
        filter_upwards [hJopen.mem_nhds htJ'] with u huJ
        by_cases huI : u ∈ I
        · simp only [gluedIntegralCurve, Set.piecewise, if_pos huI]
          exact hagree ⟨huI, huJ⟩
        · simp [gluedIntegralCurve, huI]
      exact ((hγ t htJ').congr_of_eventuallyEq hevent).congr_deriv
        (congrArg X1 hevent.self_of_nhds.symm)

/-- The union of all partial-trajectory domains is open. -/
theorem isOpen_integralCurveDomain (x₀ : R3) :
    IsOpen (integralCurveDomain x₀) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨α, I, hα, htI⟩ := ht
  filter_upwards [hα.2.1.mem_nhds htI] with u hu
  exact ⟨α, I, hα, hu⟩

/-- The union of all partial-trajectory domains is an interval. -/
theorem isPreconnected_integralCurveDomain (x₀ : R3) :
    IsPreconnected (integralCurveDomain x₀) := by
  rw [isPreconnected_iff_ordConnected]
  refine ⟨?_⟩
  intro a ha b hb t ht
  obtain ⟨α, I, hα, haI⟩ := ha
  obtain ⟨γ, J, hγ, hbJ⟩ := hb
  by_cases ht0 : t ≤ 0
  · exact ⟨α, I, hα, hα.2.2.1.2.ordConnected.out' haI hα.1 ⟨ht.1, ht0⟩⟩
  · exact ⟨γ, J, hγ, hγ.2.2.1.2.ordConnected.out' hγ.1 hbJ
      ⟨le_of_not_ge ht0, ht.2⟩⟩

/-- A point lies in the maximal trajectory domain exactly when it lies strictly
between the extended-real endpoint times. -/
theorem mem_integralCurveDomain_iff (x₀ : R3) (t : ℝ) :
    t ∈ integralCurveDomain x₀ ↔ tMin x₀ < (t : EReal) ∧ (t : EReal) < tMax x₀ := by
  constructor
  · intro ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_integralCurveDomain x₀) t ht
    have hlo : t - ε / 2 ∈ integralCurveDomain x₀ := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show t - ε / 2 - t = -(ε / 2) by ring, abs_neg,
        abs_of_pos (half_pos hε)]
      linarith
    have hhi : t + ε / 2 ∈ integralCurveDomain x₀ := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show t + ε / 2 - t = ε / 2 by ring, abs_of_pos (half_pos hε)]
      linarith
    constructor
    · apply sInf_lt_iff.mpr
      exact ⟨(t - ε / 2 : ℝ), ⟨_, hlo, rfl⟩, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
    · apply lt_sSup_iff.mpr
      exact ⟨(t + ε / 2 : ℝ), ⟨_, hhi, rfl⟩, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  · rintro ⟨hlo, hhi⟩
    obtain ⟨l, ⟨l', hl', rfl⟩, hlt⟩ := sInf_lt_iff.mp hlo
    obtain ⟨u, ⟨u', hu', rfl⟩, htu⟩ := lt_sSup_iff.mp hhi
    have hlt' : l' < t := EReal.coe_lt_coe_iff.mp hlt
    have htu' : t < u' := EReal.coe_lt_coe_iff.mp htu
    exact (isPreconnected_integralCurveDomain x₀).ordConnected.out' hl' hu'
      ⟨hlt'.le, htu'.le⟩

/-- The canonical maximal representative, obtained by choosing any partial
trajectory through each reachable time.  Overlap uniqueness makes the value
independent of the choices. -/
def maximalIntegralCurve (x₀ : R3) (t : ℝ) : R3 :=
  by
    classical
    exact if h : t ∈ integralCurveDomain x₀ then Classical.choose h t else x₀

/-- On the domain of any partial trajectory, the maximal representative agrees
with that trajectory. -/
theorem maximalIntegralCurve_eq_of_mem
    {x₀ : R3} {α : ℝ → R3} {I : Set ℝ}
    (hα : isIntegralCurveFrom x₀ α I) {t : ℝ} (ht : t ∈ I) :
    maximalIntegralCurve x₀ t = α t := by
  have htd : t ∈ integralCurveDomain x₀ := ⟨α, I, hα, ht⟩
  rw [maximalIntegralCurve, dif_pos htd]
  let γ : ℝ → R3 := Classical.choose htd
  let J : Set ℝ := Classical.choose htd.choose_spec
  have hγ : isIntegralCurveFrom x₀ γ J := htd.choose_spec.choose_spec.1
  have htJ : t ∈ J := htd.choose_spec.choose_spec.2
  exact (hγ.eqOn_inter hα) ⟨htJ, ht⟩

/-- The canonical representative is the unique maximal integral curve on the
open interval `(tMin x₀, tMax x₀)`. -/
theorem hasDerivAt_maximalIntegralCurve {x₀ : R3} {t : ℝ}
    (ht : tMin x₀ < (t : EReal) ∧ (t : EReal) < tMax x₀) :
    HasDerivAt (maximalIntegralCurve x₀)
      (X1 (maximalIntegralCurve x₀ t)) t := by
  have htd := (mem_integralCurveDomain_iff x₀ t).2 ht
  obtain ⟨α, I, hα, htI⟩ := htd
  have heq : maximalIntegralCurve x₀ =ᶠ[𝓝 t] α := by
    filter_upwards [hα.2.1.mem_nhds htI] with u hu
    exact maximalIntegralCurve_eq_of_mem hα hu
  exact ((hα.2.2.2.2 t htI).congr_of_eventuallyEq heq).congr_deriv
    (congrArg X1 (heq.self_of_nhds.symm))

@[simp] theorem maximalIntegralCurve_zero (x₀ : R3)
    (h : ∃ α I, isIntegralCurveFrom x₀ α I) :
    maximalIntegralCurve x₀ 0 = x₀ := by
  obtain ⟨α, I, hα⟩ := h
  rw [maximalIntegralCurve_eq_of_mem hα hα.1, hα.2.2.2.1]

/-- The canonical representative is itself an integral curve on the union of
all reachable times. -/
theorem maximalIntegralCurve_isIntegralCurveFrom (x₀ : R3) :
    isIntegralCurveFrom x₀ (maximalIntegralCurve x₀) (integralCurveDomain x₀) := by
  have hex := exists_isIntegralCurveFrom x₀
  have h0 : 0 ∈ integralCurveDomain x₀ := by
    obtain ⟨α, I, hα⟩ := hex
    exact ⟨α, I, hα, hα.1⟩
  refine ⟨h0, isOpen_integralCurveDomain x₀,
    ⟨⟨0, h0⟩, isPreconnected_integralCurveDomain x₀⟩,
    maximalIntegralCurve_zero x₀ hex, ?_⟩
  intro t ht
  exact hasDerivAt_maximalIntegralCurve ((mem_integralCurveDomain_iff x₀ t).1 ht)

/-- Time translation of a maximal trajectory is the maximal trajectory through
the translated point, as long as the two displayed times belong to the
original maximal domain.  This is the cocycle identity needed to continue the
local Picard flow along a compact piece of a trajectory. -/
theorem maximalIntegralCurve_add {x₀ : R3} {t u : ℝ}
    (ht : t ∈ integralCurveDomain x₀) (htu : t + u ∈ integralCurveDomain x₀) :
    maximalIntegralCurve (maximalIntegralCurve x₀ t) u =
      maximalIntegralCurve x₀ (t + u) := by
  let I : Set ℝ := (fun v : ℝ => t + v) ⁻¹' integralCurveDomain x₀
  let α : ℝ → R3 := fun v => maximalIntegralCurve x₀ (t + v)
  have hIopen : IsOpen I :=
    (isOpen_integralCurveDomain x₀).preimage (continuous_const.add continuous_id)
  have hIpre : IsPreconnected I := by
    rw [isPreconnected_iff_ordConnected]
    refine ⟨?_⟩
    intro a ha b hb c hc
    change t + a ∈ integralCurveDomain x₀ at ha
    change t + b ∈ integralCurveDomain x₀ at hb
    change t + c ∈ integralCurveDomain x₀
    apply (isPreconnected_integralCurveDomain x₀).ordConnected.out' ha hb
    constructor <;> linarith [hc.1, hc.2]
  have h0I : (0 : ℝ) ∈ I := by simpa [I] using ht
  have hα : isIntegralCurveFrom (maximalIntegralCurve x₀ t) α I := by
    refine ⟨h0I, hIopen, ⟨⟨0, h0I⟩, hIpre⟩, ?_, ?_⟩
    · simp [α]
    · intro v hv
      change t + v ∈ integralCurveDomain x₀ at hv
      have hd := hasDerivAt_maximalIntegralCurve
        ((mem_integralCurveDomain_iff x₀ (t + v)).1 hv)
      have hd' : HasDerivAt (maximalIntegralCurve x₀)
          (X1 (maximalIntegralCurve x₀ (v + t))) (v + t) := by
        simpa only [add_comm] using hd
      simpa only [α, add_comm] using hd'.comp_add_const v t
  apply maximalIntegralCurve_eq_of_mem hα
  simpa [I] using htu

/-- Around every ambient initial point, the canonical selected maximal curves
are one jointly continuous Picard flow on a common product collar.  Unlike
`UniformLocalFlowCollar`, this statement has no cross-section parameter and is
therefore suitable for repeated continuation along a maximal trajectory. -/
theorem exists_continuousOn_maximalIntegralCurve_ambient_local (x₀ : R3) :
    ∃ r > (0 : ℝ), ∃ δ > (0 : ℝ),
      ContinuousOn (fun p : R3 × ℝ => maximalIntegralCurve p.1 p.2)
        (Metric.closedBall x₀ r ×ˢ Ioo (-δ) δ) := by
  have hX : ContDiffAt ℝ 1 X1 x₀ :=
    (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
  obtain ⟨δ, hδ, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hX
  obtain ⟨flow, hflow, hflow_cont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨r, hr, δ, hδ, ?_⟩
  apply hflow_cont.mono (by
    intro p hp
    have hp2 : p.2 ∈ Ioo (0 - δ) (0 + δ) := by
      simpa only [zero_sub, zero_add] using hp.2
    exact ⟨hp.1, Ioo_subset_Icc_self hp2⟩) |>.congr
  intro p hp
  let α : ℝ → R3 := fun t => flow (p.1, t)
  have hα : isIntegralCurveFrom p.1 α (Ioo (-δ) δ) := by
    refine ⟨by simp [hδ], isOpen_Ioo,
      isConnected_Ioo (by linarith [hδ]), ?_, ?_⟩
    · exact (hflow p.1 hp.1).1
    · intro t ht
      have ht' : t ∈ Ioo (0 - δ) (0 + δ) := by
        simpa only [zero_sub, zero_add] using ht
      exact (hflow p.1 hp.1).2 t (Ioo_subset_Icc_self ht') |>.hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)
  simpa only [α] using maximalIntegralCurve_eq_of_mem hα hp.2

/-- On a compact set of initial points there is one common time collar on
which the canonical maximal curves are jointly continuous.  This is the
compact-base continuation input; extending the collar to an arbitrary compact
time interval can then be done by finitely many cocycle steps. -/
theorem exists_continuousOn_maximalIntegralCurve_ambient_compact_local
    (K : Set R3) (hK : IsCompact K) :
    ∃ δ > (0 : ℝ), ContinuousOn
      (fun p : R3 × ℝ => maximalIntegralCurve p.1 p.2)
      (K ×ˢ Ioo (-δ) δ) := by
  classical
  by_cases hKne : K.Nonempty
  · choose r hr δ hδ hcont using
      fun x : R3 => exists_continuousOn_maximalIntegralCurve_ambient_local x
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun x : R3 => Metric.ball x (r x))
      (fun _ => Metric.isOpen_ball)
      (by
        intro x hx
        exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hr x)⟩)
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      rcases mem_iUnion₂.mp (ht hx) with ⟨y, hyt, _⟩
      exact ⟨y, hyt⟩
    let δ₀ : ℝ := (t.image δ).min' (htne.image δ)
    have hδ₀ : 0 < δ₀ := by
      have hmem := Finset.min'_mem (t.image δ) (htne.image δ)
      rcases Finset.mem_image.mp hmem with ⟨x, hxt, hxδ⟩
      dsimp [δ₀]
      rw [← hxδ]
      exact hδ x
    refine ⟨δ₀, hδ₀, ?_⟩
    intro p hp
    rcases mem_iUnion₂.mp (ht hp.1) with ⟨x, hxt, hpx⟩
    have hδle : δ₀ ≤ δ x := by
      exact Finset.min'_le (t.image δ) (δ x) (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)
    have hpTime : p.2 ∈ Ioo (-(δ x)) (δ x) := by
      constructor <;> linarith [hp.2.1, hp.2.2]
    have hpOpen : p ∈ Metric.ball x (r x) ×ˢ Ioo (-(δ x)) (δ x) :=
      ⟨hpx, hpTime⟩
    have hwithin := (hcont x).mono (prod_mono Metric.ball_subset_closedBall Subset.rfl)
    exact (hwithin p hpOpen).continuousAt
      ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hpOpen) |>.continuousWithinAt
  · refine ⟨1, by norm_num, ?_⟩
    simpa [Set.not_nonempty_iff_eq_empty.mp hKne]

/-- On a compact time interval in the maximal domain, the selected maximal
curve is jointly continuous when the compact initial set is a singleton.  This
is the base case for continuation in the initial point. -/
theorem continuousOn_maximalIntegralCurve_singleton_compact_time
    (y : R3) (a b : ℝ) (_hab : a ≤ b)
    (hdom : tMin y < (a : EReal) ∧ (b : EReal) < tMax y) :
    ContinuousOn (fun p : R3 × ℝ => maximalIntegralCurve p.1 p.2)
      ({y} ×ˢ Icc a b) := by
  have hcurve : ContinuousOn (maximalIntegralCurve y) (Icc a b) := by
    intro t ht
    have htDom : tMin y < (t : EReal) ∧ (t : EReal) < tMax y := by
      constructor
      · exact hdom.1.trans_le (EReal.coe_le_coe_iff.mpr ht.1)
      · exact (EReal.coe_le_coe_iff.mpr ht.2).trans_lt hdom.2
    exact (hasDerivAt_maximalIntegralCurve htDom).continuousAt.continuousWithinAt
  have hcomp : ContinuousOn (fun p : R3 × ℝ => maximalIntegralCurve y p.2)
      ({y} ×ˢ Icc a b) :=
    hcurve.comp continuousOn_snd (fun _ hp => hp.2)
  apply hcomp.congr
  intro p hp
  simpa only [mem_singleton_iff.mp hp.1]

/-- A finite forward maximal time cannot have even a frequently compact tail:
a cluster point supplies a uniform Picard interval, and gluing from a late
point extends the curve past its alleged supremum. -/
theorem not_frequently_mem_compact_of_tMax_eq
    {x₀ : R3} {T : ℝ} {K : Set R3} (hT : tMax x₀ = (T : EReal))
    (hK : IsCompact K) :
    ¬(∃ᶠ t in 𝓝[<] T, maximalIntegralCurve x₀ t ∈ K) := by
  intro hfreqK
  have hmax := maximalIntegralCurve_isIntegralCurveFrom x₀
  have hends := (mem_integralCurveDomain_iff x₀ 0).1 hmax.1
  have hTpos : 0 < T := by
    exact EReal.coe_lt_coe_iff.mp (hends.2.trans_eq hT)
  obtain ⟨y, _hyK, hy⟩ := hK.exists_mapClusterPt_of_frequently hfreqK
  have hX : ContDiffAt ℝ 1 X1 y :=
    (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
  obtain ⟨r, hr, ε, hε, H⟩ :=
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  have hfreqBall : ∃ᶠ t in 𝓝[<] T,
      maximalIntegralCurve x₀ t ∈ Metric.ball y r :=
    mapClusterPt_iff_frequently.mp hy (Metric.ball y r) (Metric.ball_mem_nhds y hr)
  have hnear : ∀ᶠ t in 𝓝[<] T, t ∈ Ioo 0 T := Ioo_mem_nhdsLT hTpos
  have hlate : ∀ᶠ t in 𝓝[<] T, T - ε / 2 < t := by
    filter_upwards [Ioo_mem_nhdsLT (show T - ε / 2 < T by linarith)] with t ht
    exact ht.1
  obtain ⟨t, htBall, htNear, htLate⟩ :=
    (hfreqBall.and_eventually (hnear.and hlate)).exists
  have htDom : t ∈ integralCurveDomain x₀ := by
    apply (mem_integralCurveDomain_iff x₀ t).2
    constructor
    · exact hends.1.trans (EReal.coe_lt_coe_iff.mpr htNear.1)
    · rw [hT]
      exact EReal.coe_lt_coe_iff.mpr htNear.2
  obtain ⟨γ, hγt, hγ⟩ := H (maximalIntegralCurve x₀ t)
    (Metric.ball_subset_closedBall htBall)
  let γ' : ℝ → R3 := fun u => γ (u - t)
  let J : Set ℝ := Ioo (t - ε) (t + ε)
  have htJ : t ∈ J := by simp [J, hε]
  have hγ' : ∀ u ∈ J, HasDerivAt γ' (X1 (γ' u)) u := by
    intro u hu
    change t - ε < u ∧ u < t + ε at hu
    have hu' : u - t ∈ Ioo (0 - ε) (0 + ε) := by
      constructor <;> norm_num <;> linarith [hu.1, hu.2]
    simpa only [γ', sub_eq_add_neg] using
      (hγ (u - t) hu').comp_add_const u (-t)
  have hγ't : γ' t = maximalIntegralCurve x₀ t := by
    change γ (t - t) = maximalIntegralCurve x₀ t
    simpa only [sub_self] using hγt
  have hJconn : IsConnected J :=
    isConnected_Ioo (show t - ε < t + ε by linarith)
  have hpatch := hmax.extend (J := J) isOpen_Ioo hJconn hγ' htDom htJ hγ't.symm
  let u := t + ε / 2
  have huJ : u ∈ J := by dsimp [u, J]; constructor <;> linarith
  have huDom : u ∈ integralCurveDomain x₀ :=
    ⟨gluedIntegralCurve (integralCurveDomain x₀) (maximalIntegralCurve x₀) γ',
      integralCurveDomain x₀ ∪ J, hpatch, Or.inr huJ⟩
  have huUpper := ((mem_integralCurveDomain_iff x₀ u).1 huDom).2
  rw [hT] at huUpper
  have huLT : u < T := EReal.coe_lt_coe_iff.mp huUpper
  dsimp [u] at huLT
  linarith

/-- Eventual containment in a compact set at a finite forward endpoint
contradicts maximality. -/
theorem not_eventually_mem_compact_of_tMax_eq
    {x₀ : R3} {T : ℝ} {K : Set R3} (hT : tMax x₀ = (T : EReal))
    (hK : IsCompact K) :
    ¬(∀ᶠ t in 𝓝[<] T, maximalIntegralCurve x₀ t ∈ K) := by
  intro h
  exact not_frequently_mem_compact_of_tMax_eq hT hK h.frequently

/-- A finite backward maximal time cannot have even a frequently compact tail.
The same Picard gluing argument now extends to a time below the alleged
infimum. -/
theorem not_frequently_mem_compact_of_tMin_eq
    {x₀ : R3} {T : ℝ} {K : Set R3} (hT : tMin x₀ = (T : EReal))
    (hK : IsCompact K) :
    ¬(∃ᶠ t in 𝓝[>] T, maximalIntegralCurve x₀ t ∈ K) := by
  intro hfreqK
  have hmax := maximalIntegralCurve_isIntegralCurveFrom x₀
  have hends := (mem_integralCurveDomain_iff x₀ 0).1 hmax.1
  have hTneg : T < 0 := by
    exact EReal.coe_lt_coe_iff.mp (hT ▸ hends.1)
  obtain ⟨y, _hyK, hy⟩ := hK.exists_mapClusterPt_of_frequently hfreqK
  have hX : ContDiffAt ℝ 1 X1 y :=
    (contDiff_X1.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)).contDiffAt
  obtain ⟨r, hr, ε, hε, H⟩ :=
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  have hfreqBall : ∃ᶠ t in 𝓝[>] T,
      maximalIntegralCurve x₀ t ∈ Metric.ball y r :=
    mapClusterPt_iff_frequently.mp hy (Metric.ball y r) (Metric.ball_mem_nhds y hr)
  have hnear : ∀ᶠ t in 𝓝[>] T, t ∈ Ioo T 0 := Ioo_mem_nhdsGT hTneg
  have hlate : ∀ᶠ t in 𝓝[>] T, t < T + ε / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show T < T + ε / 2 by linarith)] with t ht
    exact ht.2
  obtain ⟨t, htBall, htNear, htLate⟩ :=
    (hfreqBall.and_eventually (hnear.and hlate)).exists
  have htDom : t ∈ integralCurveDomain x₀ := by
    apply (mem_integralCurveDomain_iff x₀ t).2
    constructor
    · rw [hT]
      exact EReal.coe_lt_coe_iff.mpr htNear.1
    · exact (EReal.coe_lt_coe_iff.mpr htNear.2).trans hends.2
  obtain ⟨γ, hγt, hγ⟩ := H (maximalIntegralCurve x₀ t)
    (Metric.ball_subset_closedBall htBall)
  let γ' : ℝ → R3 := fun u => γ (u - t)
  let J : Set ℝ := Ioo (t - ε) (t + ε)
  have htJ : t ∈ J := by simp [J, hε]
  have hγ' : ∀ u ∈ J, HasDerivAt γ' (X1 (γ' u)) u := by
    intro u hu
    change t - ε < u ∧ u < t + ε at hu
    have hu' : u - t ∈ Ioo (0 - ε) (0 + ε) := by
      constructor <;> norm_num <;> linarith [hu.1, hu.2]
    simpa only [γ', sub_eq_add_neg] using
      (hγ (u - t) hu').comp_add_const u (-t)
  have hγ't : γ' t = maximalIntegralCurve x₀ t := by
    change γ (t - t) = maximalIntegralCurve x₀ t
    simpa only [sub_self] using hγt
  have hJconn : IsConnected J :=
    isConnected_Ioo (show t - ε < t + ε by linarith)
  have hpatch := hmax.extend (J := J) isOpen_Ioo hJconn hγ' htDom htJ hγ't.symm
  let u := t - ε / 2
  have huJ : u ∈ J := by dsimp [u, J]; constructor <;> linarith
  have huDom : u ∈ integralCurveDomain x₀ :=
    ⟨gluedIntegralCurve (integralCurveDomain x₀) (maximalIntegralCurve x₀) γ',
      integralCurveDomain x₀ ∪ J, hpatch, Or.inr huJ⟩
  have huLower := ((mem_integralCurveDomain_iff x₀ u).1 huDom).1
  rw [hT] at huLower
  have hTLT : T < u := EReal.coe_lt_coe_iff.mp huLower
  dsimp [u] at hTLT
  linarith

/-- Eventual containment in a compact set at a finite backward endpoint
contradicts maximality. -/
theorem not_eventually_mem_compact_of_tMin_eq
    {x₀ : R3} {T : ℝ} {K : Set R3} (hT : tMin x₀ = (T : EReal))
    (hK : IsCompact K) :
    ¬(∀ᶠ t in 𝓝[>] T, maximalIntegralCurve x₀ t ∈ K) := by
  intro h
  exact not_frequently_mem_compact_of_tMin_eq hT hK h.frequently

/-- Every finite forward endpoint of a maximal `X1` trajectory escapes all
norm balls. -/
theorem tendsto_norm_maximalIntegralCurve_at_tMax
    {x₀ : R3} {T : ℝ} (hT : tMax x₀ = (T : EReal)) :
    Tendsto (fun t => ‖maximalIntegralCurve x₀ t‖) (𝓝[<] T) atTop := by
  apply tendsto_atTop.2
  intro b
  by_contra h
  have hfreq : ∃ᶠ t in 𝓝[<] T, ¬b ≤ ‖maximalIntegralCurve x₀ t‖ :=
    not_eventually.mp h
  have hfreqBall : ∃ᶠ t in 𝓝[<] T,
      maximalIntegralCurve x₀ t ∈ Metric.closedBall 0 |b| := by
    apply hfreq.mono
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (le_of_not_ge ht).trans (le_abs_self b)
  exact not_frequently_mem_compact_of_tMax_eq hT (isCompact_closedBall 0 |b|) hfreqBall

/-- Every finite backward endpoint of a maximal `X1` trajectory escapes all
norm balls. -/
theorem tendsto_norm_maximalIntegralCurve_at_tMin
    {x₀ : R3} {T : ℝ} (hT : tMin x₀ = (T : EReal)) :
    Tendsto (fun t => ‖maximalIntegralCurve x₀ t‖) (𝓝[>] T) atTop := by
  apply tendsto_atTop.2
  intro b
  by_contra h
  have hfreq : ∃ᶠ t in 𝓝[>] T, ¬b ≤ ‖maximalIntegralCurve x₀ t‖ :=
    not_eventually.mp h
  have hfreqBall : ∃ᶠ t in 𝓝[>] T,
      maximalIntegralCurve x₀ t ∈ Metric.closedBall 0 |b| := by
    apply hfreq.mono
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (le_of_not_ge ht).trans (le_abs_self b)
  exact not_frequently_mem_compact_of_tMin_eq hT (isCompact_closedBall 0 |b|) hfreqBall

/-- The lower maximal endpoint is either negative infinity or a finite endpoint
with norm escape from the right.  This is the pointwise lower-end alternative
for the separate maximal-flow construction; the explicit branch sheet below
instead has a regular finite cross-section end. -/
theorem tMin_eq_bot_or_exists_escape (x₀ : R3) :
    tMin x₀ = ⊥ ∨ ∃ T : ℝ, tMin x₀ = (T : EReal) ∧
      Tendsto (fun t : ℝ => ‖maximalIntegralCurve x₀ t‖) (𝓝[>] T) atTop := by
  by_cases hbot : tMin x₀ = ⊥
  · exact Or.inl hbot
  · right
    have hmax := maximalIntegralCurve_isIntegralCurveFrom x₀
    have hlower := ((mem_integralCurveDomain_iff x₀ 0).1 hmax.1).1
    have htop : tMin x₀ ≠ ⊤ := by
      intro h
      rw [h] at hlower
      simpa using hlower
    let T := (tMin x₀).toReal
    have hT : tMin x₀ = (T : EReal) :=
      (EReal.coe_toReal htop hbot).symm
    exact ⟨T, hT, tendsto_norm_maximalIntegralCurve_at_tMin hT⟩

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

/-- The jointly continuous Picard--Lindelöf flow in a uniform collar agrees
with the canonical maximal integral curve wherever the collar is defined. -/
theorem flowMap_eq_maximalIntegralCurve (C : UniformLocalFlowCollar)
    {x : ℝ × ℝ} (hx : x ∈ C.W₀) {t : ℝ} (ht : t ∈ Ioo (-C.δ) C.δ) :
    C.flowMap (x, t) = maximalIntegralCurve (C.S.qSigma x) t := by
  let α : ℝ → R3 := fun u => C.flowMap (x, u)
  have hα : isIntegralCurveFrom (C.S.qSigma x) α (Ioo (-C.δ) C.δ) := by
    refine ⟨by simp [C.δ_pos], isOpen_Ioo,
      isConnected_Ioo (by linarith [C.δ_pos]), C.flowMap_zero x hx, ?_⟩
    intro u hu
    exact C.hasDerivAt_flowMap x hx u hu
  exact (maximalIntegralCurve_eq_of_mem hα ht).symm

/-- Joint continuity of the selected maximal curves on the compact transverse
core and their common Picard time interval. -/
theorem continuousOn_maximalIntegralCurve (C : UniformLocalFlowCollar) :
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      maximalIntegralCurve (C.S.qSigma p.1) p.2)
      (C.W₀ ×ˢ Ioo (-C.δ) C.δ) := by
  apply C.continuousOn_flowMap.congr
  intro p hp
  exact (C.flowMap_eq_maximalIntegralCurve hp.1 hp.2).symm

/-- In particular, the canonical maximal flow is jointly continuous on a
nonempty open product collar.  The smaller open ball is used only to make the
transverse domain open; it remains inside the compact uniform core. -/
theorem continuousOn_maximalIntegralCurve_local (C : UniformLocalFlowCollar) :
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      maximalIntegralCurve (C.S.qSigma p.1) p.2)
      (Metric.ball C.x₀ C.ρ ×ˢ Ioo (-C.δ) C.δ) := by
  apply C.continuousOn_maximalIntegralCurve.mono
  intro p hp
  refine ⟨?_, hp.2⟩
  rw [C.W₀_eq]
  exact Metric.ball_subset_closedBall hp.1

/-- The domain in `continuousOn_maximalIntegralCurve_local` is genuinely a
nonempty open collar. -/
theorem isOpen_nonempty_localFlowDomain (C : UniformLocalFlowCollar) :
    IsOpen (Metric.ball C.x₀ C.ρ ×ˢ Ioo (-C.δ) C.δ) ∧
      (Metric.ball C.x₀ C.ρ ×ˢ Ioo (-C.δ) C.δ).Nonempty := by
  constructor
  · exact (Metric.isOpen_ball.prod isOpen_Ioo)
  · exact ⟨(C.x₀, 0), Metric.mem_ball_self C.ρ_pos, by simp [C.δ_pos]⟩

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
  /-- A lower endpoint is either `-∞`, finite and escaping from the right, or a
  regular finite face with a limit point.  The third case is a genuine
  cross-section boundary: future integration by parts must not discard it, but
  must handle its residual by support or an estimate. -/
  lower_ok : ∀ x ∈ W,
    ℓ x = ⊥ ∨
      (∃ L : ℝ, ℓ x = (L : EReal) ∧
        Tendsto (fun s : ℝ => ‖Psi (x, s)‖) (𝓝[>] L) atTop) ∨
      (∃ L : ℝ, ℓ x = (L : EReal) ∧ ∃ q : R3,
        Tendsto (fun s : ℝ => Psi (x, s)) (𝓝[>] L) (𝓝 q))

namespace ForwardSaturatedSheet

/-- Membership in a saturated-sheet domain is exactly membership in its full
open interval bundle. -/
theorem mem_D_iff (S : ForwardSaturatedSheet) (x : ℝ × ℝ) (s : ℝ) :
    (x, s) ∈ S.D ↔ x ∈ S.W ∧ S.ℓ x < (s : EReal) ∧ s < S.β x := by
  rw [S.D_eq]
  rfl

end ForwardSaturatedSheet

end ExoticCCR
