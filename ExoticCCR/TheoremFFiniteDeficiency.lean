/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFWeakDeficiency

/-!
# Finite families of forward weak deficiency vectors

This module constructs, for every finite cardinality, actual linearly
independent `L²` weak `-i` adjoint eigenvectors for the canonical minimal
transport core of `X1`.  The construction uses transverse bump functions with
pairwise disjoint compact supports inside one maximal forward sheet.

It also packages weak eigenvectors as a submodule and proves that its weak
`-i` eigenspace is not finite-dimensional.  It does not assert a countably
infinite family, a deficiency-index value, the `+i` deficiency space, or full
Theorem F.  The `+i` step is blocked on an explicit sign-correct construction
for the conjugate/dual deficiency space; no such result is currently exported
by the transport-core API.
-/

noncomputable section

open MeasureTheory Set

namespace ExoticCCR

/-- The weak adjoint eigenspace at `z`, expressed without choosing an adjoint
domain representative. -/
def weakAdjointEigenspace (H : L2R3 →ₗ.[ℂ] L2R3) (z : ℂ) : Submodule ℂ L2R3 where
  carrier := {u | WeakAdjointEigenvector H z u}
  zero_mem' := by simp [WeakAdjointEigenvector]
  add_mem' := by
    intro u v hu hv x
    simp only [smul_add, inner_add_left]
    rw [hu x, hv x]
  smul_mem' := by
    intro c u hu x
    change WeakAdjointEigenvector H z u at hu
    simp only [smul_smul, inner_smul_left]
    rw [map_mul]
    have hux : (starRingEnd ℂ z) * inner ℂ u (x : L2R3) =
        inner ℂ u (H x) := by
      simpa [inner_smul_left] using hu x
    calc
      _ = (starRingEnd ℂ c) * ((starRingEnd ℂ z) * inner ℂ u (x : L2R3)) := by ring
      _ = _ := by rw [hux]

private def finiteCutoffRadius (ε : ℝ) (n : ℕ) : ℝ :=
  ε / (16 * ((n : ℝ) + 1))

private def finiteCutoffCenter (x : ℝ × ℝ) (ε : ℝ) (n : ℕ) (i : Fin n) : ℝ × ℝ :=
  (x.1 + 4 * (i : ℝ) * finiteCutoffRadius ε n, x.2)

private theorem finiteCutoffRadius_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < finiteCutoffRadius ε n := by
  unfold finiteCutoffRadius
  positivity

private theorem finiteCutoffRadius_scale {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    16 * ((n : ℝ) + 1) * finiteCutoffRadius ε n = ε := by
  unfold finiteCutoffRadius
  field_simp

private theorem finiteCutoffRadius_add_centerDist_lt {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) (x : ℝ × ℝ) (i : Fin n) :
    finiteCutoffRadius ε n + dist (finiteCutoffCenter x ε n i) x < ε := by
  have hρ := finiteCutoffRadius_pos hε n
  have hi : (i : ℝ) < (n : ℝ) := by exact_mod_cast i.isLt
  have hiρ : (i : ℝ) * finiteCutoffRadius ε n <
      (n : ℝ) * finiteCutoffRadius ε n := mul_lt_mul_of_pos_right hi hρ
  have hscale := finiteCutoffRadius_scale hε n
  rw [Prod.dist_eq]
  simp only [finiteCutoffCenter, Real.dist_eq, dist_self]
  rw [max_eq_left (abs_nonneg _)]
  rw [show x.1 + 4 * (i : ℝ) * finiteCutoffRadius ε n - x.1 =
      4 * (i : ℝ) * finiteCutoffRadius ε n by ring]
  rw [abs_of_nonneg (by positivity)]
  nlinarith

private theorem finiteCutoffCenter_dist_gt {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : ℝ × ℝ) {i j : Fin n} (hij : i ≠ j) :
    2 * finiteCutoffRadius ε n <
      dist (finiteCutoffCenter x ε n i) (finiteCutoffCenter x ε n j) := by
  have hρ := finiteCutoffRadius_pos hε n
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have hcast : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    rw [Prod.dist_eq]
    simp only [finiteCutoffCenter, Real.dist_eq, dist_self]
    rw [max_eq_left (abs_nonneg _)]
    rw [abs_of_nonpos]
    · nlinarith
    · nlinarith
  · have hcast : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hgt)
    rw [Prod.dist_eq]
    simp only [finiteCutoffCenter, Real.dist_eq, dist_self]
    rw [max_eq_left (abs_nonneg _)]
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith

private def finiteCutoffBump {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : ℝ × ℝ) (i : Fin n) : ContDiffBump (finiteCutoffCenter x ε n i) where
  rIn := finiteCutoffRadius ε n / 2
  rOut := finiteCutoffRadius ε n
  rIn_pos := half_pos (finiteCutoffRadius_pos hε n)
  rIn_lt_rOut := half_lt_self (finiteCutoffRadius_pos hε n)

private def finiteCutoff {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : ℝ × ℝ) (i : Fin n) : ℝ × ℝ → ℂ :=
  fun y => (finiteCutoffBump hε n x i y : ℂ)

private theorem finiteCutoff_continuous {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : ℝ × ℝ) (i : Fin n) : Continuous (finiteCutoff hε n x i) :=
  Complex.continuous_ofReal.comp (finiteCutoffBump hε n x i).continuous

private theorem finiteCutoff_hasCompactSupport {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : ℝ × ℝ) (i : Fin n) : HasCompactSupport (finiteCutoff hε n x i) :=
  (finiteCutoffBump hε n x i).hasCompactSupport.comp_left
    (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

private theorem finiteCutoff_tsupport {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : ℝ × ℝ) (i : Fin n) :
    tsupport (finiteCutoff hε n x i) =
      Metric.closedBall (finiteCutoffCenter x ε n i) (finiteCutoffRadius ε n) := by
  have hsupp : Function.support (finiteCutoff hε n x i) =
      Function.support (finiteCutoffBump hε n x i) := by
    ext y
    simp [finiteCutoff]
  rw [tsupport, hsupp, ← tsupport]
  exact (finiteCutoffBump hε n x i).tsupport_eq

private theorem finiteCutoff_center {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : ℝ × ℝ) (i : Fin n) :
    finiteCutoff hε n x i (finiteCutoffCenter x ε n i) = 1 := by
  change ((finiteCutoffBump hε n x i) (finiteCutoffCenter x ε n i) : ℂ) = 1
  rw [(finiteCutoffBump hε n x i).one_of_mem_closedBall
    (Metric.mem_closedBall_self (finiteCutoffBump hε n x i).rIn_pos.le)]
  norm_num

/-- A maximal forward sheet contains an explicit finite family of admissible
transverse cutoffs with pairwise disjoint topological supports.  Their
associated `uMinus` classes are linearly independent weak `-i` adjoint
eigenvectors. -/
theorem ForwardMaximalSheet.exists_finite_weakAdjointEigenvector_negI_family
    (M : ForwardMaximalSheet) (n : ℕ) :
    ∃ (χ : Fin n → ℝ × ℝ → ℂ)
        (hχ : ∀ i, Continuous (χ i))
        (hχc : ∀ i, HasCompactSupport (χ i))
        (hχW : ∀ i, tsupport (χ i) ⊆ M.W),
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      let u : Fin n → L2R3 := fun i =>
        (M.memLp_uMinus (χ i) (hχ i) (hχc i) (hχW i)).toLp (M.uMinus (χ i))
      LinearIndependent ℂ u ∧
        ∀ i, WeakAdjointEigenvector H_X1_min (-Complex.I) (u i) := by
  obtain ⟨x, hx⟩ := M.nonempty_W
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp M.isOpen_W x hx
  let χ : Fin n → ℝ × ℝ → ℂ := fun i => finiteCutoff hε n x i
  have hχ : ∀ i, Continuous (χ i) := fun i => finiteCutoff_continuous hε n x i
  have hχc : ∀ i, HasCompactSupport (χ i) :=
    fun i => finiteCutoff_hasCompactSupport hε n x i
  have hχW : ∀ i, tsupport (χ i) ⊆ M.W := by
    intro i y hy
    apply hball
    rw [Metric.mem_ball]
    rw [finiteCutoff_tsupport hε n x i] at hy
    have hy' : dist y (finiteCutoffCenter x ε n i) ≤ finiteCutoffRadius ε n := hy
    calc
      dist y x ≤ dist y (finiteCutoffCenter x ε n i) +
          dist (finiteCutoffCenter x ε n i) x :=
        dist_triangle y (finiteCutoffCenter x ε n i) x
      _ < ε := by
        nlinarith [finiteCutoffRadius_add_centerDist_lt hε n x i]
  have hdisj : Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
    intro i j hij
    rw [finiteCutoff_tsupport hε n x i, finiteCutoff_tsupport hε n x j]
    exact Metric.closedBall_disjoint_closedBall
      (by simpa [two_mul] using finiteCutoffCenter_dist_gt hε n x hij)
  let u : Fin n → L2R3 := fun i =>
    (M.memLp_uMinus (χ i) (hχ i) (hχc i) (hχW i)).toLp (M.uMinus (χ i))
  have hχ0 : ∀ i, χ i ≠ 0 := by
    intro i hzero
    have hpoint := congrFun hzero (finiteCutoffCenter x ε n i)
    rw [show χ i (finiteCutoffCenter x ε n i) = 1 from finiteCutoff_center hε n x i]
      at hpoint
    exact one_ne_zero hpoint
  have huData : ∀ i, u i ≠ 0 ∧
      WeakAdjointEigenvector H_X1_min (-Complex.I) (u i) := by
    intro i
    exact M.nonzero_weakAdjointEigenvector_uMinus (χ i) (hχ i) (hχc i) (hχW i) (hχ0 i)
  refine ⟨χ, hχ, hχc, hχW, hdisj, ?_, fun i => (huData i).2⟩
  apply linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => (huData i).1)
  intro i j hij
  rw [inner_toLp_toLp_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards with q
  by_cases hq : q ∈ M.PsiFin3 '' M.Dfin3
  · obtain ⟨v, hv, rfl⟩ := hq
    rw [M.uMinus_on_image (χ i) hv, M.uMinus_on_image (χ j) hv]
    have hzero : χ i (v 0, v 2) = 0 ∨ χ j (v 0, v 2) = 0 := by
      by_contra h
      push_neg at h
      exact Set.disjoint_left.mp (hdisj hij)
        (subset_tsupport _ (Function.mem_support.mpr h.1))
        (subset_tsupport _ (Function.mem_support.mpr h.2))
    rcases hzero with hi | hj
    · simp [ForwardMaximalSheet.deficiencyDensityFin3, hi]
    · simp [ForwardMaximalSheet.deficiencyDensityFin3, hj]
  · rw [M.uMinus_off_image (χ i) hq, M.uMinus_off_image (χ j) hq]
    simp

/-- For every finite cardinality there are actual linearly independent `L²`
weak `-i` adjoint eigenvectors for the canonical minimal transport core of
`X1`.  This is a finite-family statement only. -/
theorem exists_finite_weakAdjointEigenvector_negI_family (n : ℕ) :
    ∃ u : Fin n → L2R3,
      LinearIndependent ℂ u ∧
        ∀ i, WeakAdjointEigenvector H_X1_min (-Complex.I) (u i) := by
  obtain ⟨O⟩ := exists_forwardBranchOpen
  obtain ⟨M⟩ := O.exists_forwardMaximalSheet
  obtain ⟨χ, hχ, hχc, hχW, _hdisj, hu⟩ :=
    M.exists_finite_weakAdjointEigenvector_negI_family n
  exact ⟨fun i => (M.memLp_uMinus (χ i) (hχ i) (hχc i) (hχW i)).toLp
    (M.uMinus (χ i)), hu⟩

/-- Arbitrarily large finite linearly independent weak eigenspace families
force the corresponding weak eigenspace not to be finite-dimensional. -/
theorem weakAdjointEigenspace_not_finiteDimensional_of_finite_families
    (H : L2R3 →ₗ.[ℂ] L2R3) (z : ℂ)
    (hfamilies : ∀ n : ℕ, ∃ u : Fin n → L2R3,
      LinearIndependent ℂ u ∧ ∀ i, WeakAdjointEigenvector H z (u i)) :
    ¬ FiniteDimensional ℂ (weakAdjointEigenspace H z) := by
  intro hfinite
  let n := Module.finrank ℂ (weakAdjointEigenspace H z) + 1
  obtain ⟨u, hu, huEig⟩ := hfamilies n
  let v : Fin n → weakAdjointEigenspace H z := fun i => ⟨u i, huEig i⟩
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (weakAdjointEigenspace H z).subtype hu
  letI : FiniteDimensional ℂ (weakAdjointEigenspace H z) := hfinite
  have hle := hv.fintype_card_le_finrank
  simp [n] at hle

/-- The weak `-i` deficiency eigenspace of the canonical minimal transport
core is not finite-dimensional. -/
theorem weakAdjointEigenspace_negI_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (weakAdjointEigenspace H_X1_min (-Complex.I)) := by
  apply weakAdjointEigenspace_not_finiteDimensional_of_finite_families
  exact exists_finite_weakAdjointEigenvector_negI_family

end ExoticCCR
