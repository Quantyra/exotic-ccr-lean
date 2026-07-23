/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremC
import ExoticCCR.VectorFieldCompleteness

/-!
# A001 Theorem D: an incomplete dual field

The algebraic curve is first handled with an independent square-root parameter
`s`, then specialized over `ℝ`.  Its first dual-field trajectory escapes to
infinity at time `1/2`.
-/

noncomputable section

open Filter Matrix MvPolynomial Set
open scoped Topology

namespace ExoticCCR

variable (K : Type*) [Field K]

/-- First coordinate of the algebraic blow-up witness. -/
def blowupQ0 (t s : K) : K := (-2 * t - s + 1) / (t * (2 * t - 1))

/-- Third coordinate of the algebraic blow-up witness. -/
def blowupQ2 (t s : K) : K := t ^ 2 * (2 * t - 3 * s - 1)

/-- The radical-cleared parameterized witness point. -/
def blowupCurve (t s : K) : Fin 3 → K := ![blowupQ0 K t s, t, blowupQ2 K t s]

set_option maxHeartbeats 1000000 in
-- Expanding and normalizing all three anchor coordinates requires a larger budget.
/-- T0.D.1: the parameterized algebraic witness lies over `(0,t,2)`. -/
theorem evalMap_F_blowupCurve {t s : K} (ht : t ≠ 0) (hden : 2 * t - 1 ≠ 0)
    (hs : s ^ 2 = 1 - 2 * t) :
    evalMap (F K) (blowupCurve K t s) = ![0, t, 2] := by
  have hden' : -1 + t * 2 ≠ 0 := by
    intro h
    apply hden
    rw [show 2 * t - 1 = -1 + t * 2 by ring, h]
  have hs3 : s ^ 3 = s * (1 - 2 * t) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 - 2 * t) := by rw [hs]
  have hs4 : s ^ 4 = (1 - 2 * t) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - 2 * t) ^ 2 := by rw [hs]
  funext i
  fin_cases i <;>
    simp [evalMap, F, blowupCurve, blowupQ0, blowupQ2] <;>
    field_simp [ht, hden, hden'] <;>
    ring_nf <;>
    (try rw [hs4]) <;>
    (try rw [hs3]) <;>
    (try rw [hs]) <;>
    field_simp [hden'] <;>
    ring

/-- The original exact rational sample, now a corollary of the parameterized identity. -/
theorem evalMap_F_blowupCurve_sample :
    evalMap (F ℚ) (blowupCurve ℚ (3 / 8) (1 / 2)) = ![0, 3 / 8, 2] := by
  apply evalMap_F_blowupCurve
  all_goals norm_num

/-- The real A001 blow-up trajectory. -/
def gamma (t : ℝ) : Fin 3 → ℝ := blowupCurve ℝ t (Real.sqrt (1 - 2 * t))

/-- Evaluation of a row of the polynomial dual matrix as a real vector field. -/
def dualVectorField (j : Fin 3) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k ↦ eval q (dualMatrixF ℝ j k)

/-- The first escaping dual field (row indexed by `1`). -/
def X1 : (Fin 3 → ℝ) → (Fin 3 → ℝ) := dualVectorField 1

/-- T0.D.2: the real trajectory lies over `(0,t,2)` before the escape time. -/
theorem evalMap_F_gamma {t : ℝ} (ht : t ∈ Ioo 0 (1 / 2 : ℝ)) :
    evalMap (F ℝ) (gamma t) = ![0, t, 2] := by
  apply evalMap_F_blowupCurve
  · exact ne_of_gt ht.1
  · linarith [ht.2]
  · exact Real.sq_sqrt (by linarith [ht.2])

/-- The polynomial vector field `X1` is smooth. -/
theorem contDiff_X1 : ContDiff ℝ ⊤ X1 := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    simp [X1, dualVectorField, dualMatrixF, Matrix.adjugate_fin_three,
      jacobianMatrix, F] <;>
    fun_prop

set_option maxHeartbeats 2000000 in
-- The explicit Jacobian chain rule and evaluated matrix inverse are normalization-heavy.
/-- T0.D.3: `gamma` is an integral curve of `X1` on `(0,1/2)`. -/
theorem hasDerivAt_gamma {t : ℝ} (ht : t ∈ Ioo 0 (1 / 2 : ℝ)) :
    HasDerivAt gamma (X1 (gamma t)) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have hden : 2 * t - 1 ≠ 0 := by linarith [ht.2]
  have hrad_pos : 0 < 1 - 2 * t := by linarith [ht.2]
  have hs0 : Real.sqrt (1 - 2 * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hrad_pos)
  have hs2 : Real.sqrt (1 - 2 * t) ^ 2 = 1 - 2 * t := Real.sq_sqrt hrad_pos.le
  have hs3 : Real.sqrt (1 - 2 * t) ^ 3 = Real.sqrt (1 - 2 * t) * (1 - 2 * t) := by
    calc
      _ = Real.sqrt (1 - 2 * t) * Real.sqrt (1 - 2 * t) ^ 2 := by ring
      _ = _ := by rw [hs2]
  have hs4 : Real.sqrt (1 - 2 * t) ^ 4 = (1 - 2 * t) ^ 2 := by
    calc
      _ = (Real.sqrt (1 - 2 * t) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs2]
  have hs5 : Real.sqrt (1 - 2 * t) ^ 5 = Real.sqrt (1 - 2 * t) * (1 - 2 * t) ^ 2 := by
    calc
      _ = Real.sqrt (1 - 2 * t) * Real.sqrt (1 - 2 * t) ^ 4 := by ring
      _ = _ := by rw [hs4]
  have hs6 : Real.sqrt (1 - 2 * t) ^ 6 = (1 - 2 * t) ^ 3 := by
    calc
      _ = (Real.sqrt (1 - 2 * t) ^ 2) ^ 3 := by ring
      _ = _ := by rw [hs2]
  have hs7 : Real.sqrt (1 - 2 * t) ^ 7 = Real.sqrt (1 - 2 * t) * (1 - 2 * t) ^ 3 := by
    calc
      _ = Real.sqrt (1 - 2 * t) * Real.sqrt (1 - 2 * t) ^ 6 := by ring
      _ = _ := by rw [hs6]
  have hs8 : Real.sqrt (1 - 2 * t) ^ 8 = (1 - 2 * t) ^ 4 := by
    calc
      _ = (Real.sqrt (1 - 2 * t) ^ 2) ^ 4 := by ring
      _ = _ := by rw [hs2]
  have hsqrt : HasDerivAt (fun u : ℝ ↦ Real.sqrt (1 - 2 * u))
      (-1 / Real.sqrt (1 - 2 * t)) t := by
    have hraw : HasDerivAt (fun u : ℝ ↦ Real.sqrt (1 - 2 * u))
        ((1 / (2 * Real.sqrt (1 - 2 * t))) * (-2)) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_sqrt (ne_of_gt hrad_pos)).comp t
          ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul 2))
    convert hraw using 1
    field_simp [hs0]
  let dq0 : ℝ :=
    (((-2 : ℝ) - (-1 / Real.sqrt (1 - 2 * t))) * (t * (2 * t - 1)) -
      (-2 * t - Real.sqrt (1 - 2 * t) + 1) * ((2 * t - 1) + t * 2)) /
        (t * (2 * t - 1)) ^ 2
  have hq0 : HasDerivAt
      (fun u : ℝ ↦ blowupQ0 ℝ u (Real.sqrt (1 - 2 * u))) dq0 t := by
    dsimp [dq0]
    simpa [blowupQ0, Function.comp_def] using!
      (((((hasDerivAt_id t).const_mul (-2)).sub hsqrt).add_const 1).div
        ((hasDerivAt_id t).mul
          (((hasDerivAt_id t).const_mul 2).sub_const 1))
        (mul_ne_zero ht0 hden))
  let dq2 : ℝ :=
    2 * t * (2 * t - 3 * Real.sqrt (1 - 2 * t) - 1) +
      t ^ 2 * (2 - 3 * (-1 / Real.sqrt (1 - 2 * t)))
  have hq2 : HasDerivAt
      (fun u : ℝ ↦ blowupQ2 ℝ u (Real.sqrt (1 - 2 * u))) dq2 t := by
    dsimp [dq2]
    simpa [blowupQ2, Function.comp_def, pow_two] using!
      (((hasDerivAt_id t).pow 2).mul
        ((((hasDerivAt_id t).const_mul 2).sub (hsqrt.const_mul 3)).sub_const 1))
  let v : Fin 3 → ℝ := ![dq0, 1, dq2]
  have hgamma_v : HasDerivAt gamma v t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hq0
    · exact hasDerivAt_id t
    · exact hq2
  let J : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i k ↦ eval (gamma t) (jacobianMatrix (F ℝ) i k)
  let e1 : Fin 3 → ℝ := fun i ↦ if i = 1 then 1 else 0
  have hJv : J *ᵥ v = e1 := by
    funext i
    have hv0 := hasDerivAt_pi.mp hgamma_v (0 : Fin 3)
    have hv1 := hasDerivAt_pi.mp hgamma_v (1 : Fin 3)
    have hv2 := hasDerivAt_pi.mp hgamma_v (2 : Fin 3)
    have hcomp : HasDerivAt (fun u ↦ evalMap (F ℝ) (gamma u) i) ((J *ᵥ v) i) t := by
      have hxy := hv0.mul hv1
      have hone := hxy.const_add 1
      fin_cases i
      · have hraw := ((hone.pow 3).mul hv2).add
            (((hv1.pow 2).mul hone).mul ((hxy.const_mul 3).const_add 4))
        have hraw' : HasDerivAt _ ((J *ᵥ v) (0 : Fin 3)) t := hraw.congr_deriv (by
          simp [J, jacobianMatrix, Matrix.mulVec, dotProduct, F, Fin.sum_univ_succ]
          ring)
        simpa [evalMap, F, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using! hraw'
      · have hraw := (hv1.add (((hv0.const_mul 3).mul (hone.pow 2)).mul hv2)).add
            (((hv0.const_mul 3).mul (hv1.pow 2)).mul
              ((hxy.const_mul 3).const_add 4))
        have hraw' : HasDerivAt _ ((J *ᵥ v) (1 : Fin 3)) t := hraw.congr_deriv (by
          simp [J, jacobianMatrix, Matrix.mulVec, dotProduct, F, Fin.sum_univ_succ]
          ring)
        simpa [evalMap, F, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using! hraw'
      · have hraw := (hv0.const_mul 2).sub (((hv0.pow 2).const_mul 3).mul hv1) |>.sub
            ((hv0.pow 3).mul hv2)
        have hraw' : HasDerivAt _ ((J *ᵥ v) (2 : Fin 3)) t := hraw.congr_deriv (by
          simp [J, jacobianMatrix, Matrix.mulVec, dotProduct, F, Fin.sum_univ_succ]
          ring)
        simpa [evalMap, F, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] using! hraw'
    have heq : (fun u ↦ evalMap (F ℝ) (gamma u) i) =ᶠ[𝓝 t]
        (fun u ↦ (![0, u, 2] : Fin 3 → ℝ) i) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact congrFun (evalMap_F_gamma hu) i
    have hsimple : HasDerivAt (fun u ↦ (![0, u, 2] : Fin 3 → ℝ) i) (e1 i) t := by
      fin_cases i
      · exact hasDerivAt_const t 0
      · exact hasDerivAt_id t
      · exact hasDerivAt_const t 2
    exact hcomp.unique (hsimple.congr_of_eventuallyEq heq)
  let BT : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j ↦ eval (gamma t) ((dualMatrixF ℝ).transpose i j)
  have hJBT : J * BT = 1 := by
    have hp := jacobian_mul_dualMatrixF_transpose ℝ (by norm_num)
    ext i j
    have hij := congrArg (fun M => M i j) hp
    change (∑ x, eval (gamma t) (jacobianMatrix (F ℝ) i x) *
      eval (gamma t) (dualMatrixF ℝ j x)) = if i = j then 1 else 0
    simpa [J, BT, Matrix.mul_apply, map_sum, map_mul, Matrix.one_apply] using
      congrArg (eval (gamma t)) hij
  have hBTJ : BT * J = 1 := mul_eq_one_comm.mp hJBT
  have hJX : J *ᵥ X1 (gamma t) = e1 := by
    funext i
    have hij := congrArg (fun M => M i (1 : Fin 3))
      (jacobian_mul_dualMatrixF_transpose ℝ (by norm_num))
    change (∑ x, eval (gamma t) (jacobianMatrix (F ℝ) i x) *
      eval (gamma t) (dualMatrixF ℝ 1 x)) = if i = 1 then 1 else 0
    simpa [J, X1, dualVectorField, Matrix.mul_apply, Matrix.one_apply, e1,
      map_sum, map_mul] using congrArg (eval (gamma t)) hij
  have hv : v = X1 (gamma t) := by
    calc
      v = (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v := by simp
      _ = (BT * J) *ᵥ v := by rw [hBTJ]
      _ = BT *ᵥ (J *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = BT *ᵥ e1 := by rw [hJv]
      _ = BT *ᵥ (J *ᵥ X1 (gamma t)) := by rw [hJX]
      _ = (BT * J) *ᵥ X1 (gamma t) := by rw [Matrix.mulVec_mulVec]
      _ = X1 (gamma t) := by rw [hBTJ]; simp
  rwa [hv] at hgamma_v

/-- T0.D.4: the trajectory escapes every norm ball at time `1/2`. -/
theorem tendsto_norm_gamma_atTop :
    Tendsto (fun t ↦ ‖gamma t‖) (𝓝[<] (1 / 2 : ℝ)) atTop := by
  let s : ℝ → ℝ := fun t ↦ Real.sqrt (1 - 2 * t)
  have hs_nhds : Tendsto s (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) := by
    have hinner : Tendsto (fun t : ℝ ↦ 1 - 2 * t) (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[<] (1 / 2 : ℝ)) (𝓝 1) :=
        tendsto_const_nhds
      have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (1 / 2)) :=
        tendsto_id.mono_left inf_le_left
      convert h1.sub (hid.const_mul 2) using 1 <;> norm_num
    simpa [s, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hinner
  have hs_pos : ∀ᶠ t in 𝓝[<] (1 / 2 : ℝ), 0 < s t := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
    exact Real.sqrt_pos.2 (by linarith [ht.2])
  have hs_nhdsGT : Tendsto s (𝓝[<] (1 / 2 : ℝ)) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hs_nhds, hs_pos⟩
  have hinv : Tendsto (fun t ↦ (s t)⁻¹) (𝓝[<] (1 / 2 : ℝ)) atTop :=
    hs_nhdsGT.inv_tendsto_nhdsGT_zero
  have hq0 : (fun t ↦ gamma t 0) =ᶠ[𝓝[<] (1 / 2 : ℝ)]
      (fun t ↦ 2 / (s t * (1 + s t))) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have hden : 2 * t - 1 ≠ 0 := by linarith [ht.2]
    have hs0 : s t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith [ht.2]))
    have hs2 : (s t) ^ 2 = 1 - 2 * t := Real.sq_sqrt (by linarith [ht.2])
    dsimp [s] at hs0 hs2
    have hs3 : Real.sqrt (1 - 2 * t) ^ 3 =
        Real.sqrt (1 - 2 * t) * (1 - 2 * t) := by
      calc
        _ = Real.sqrt (1 - 2 * t) * Real.sqrt (1 - 2 * t) ^ 2 := by ring
        _ = _ := by rw [hs2]
    simp [gamma, blowupCurve, blowupQ0, s]
    field_simp [ht0, hden, hs0]
    ring_nf at hs2 hs3 ⊢
    nlinarith [hs2, hs3]
  have hs_le_one : ∀ᶠ t in 𝓝[<] (1 / 2 : ℝ), s t ≤ 1 :=
    hs_nhds (Iic_mem_nhds (by norm_num))
  have hcoord : Tendsto (fun t ↦ gamma t 0) (𝓝[<] (1 / 2 : ℝ)) atTop := by
    apply tendsto_atTop_mono' (𝓝[<] (1 / 2 : ℝ)) _ hinv
    filter_upwards [hq0, hs_pos, hs_le_one] with t hq hspos hsle
    rw [hq]
    have h1s : 0 < 1 + s t := by linarith
    field_simp [ne_of_gt hspos, ne_of_gt h1s]
    nlinarith
  apply tendsto_atTop_mono' (𝓝[<] (1 / 2 : ℝ)) _ hcoord
  filter_upwards with t
  exact le_trans (le_abs_self (gamma t 0)) (by
    rw [Pi.norm_def]
    exact_mod_cast Finset.le_sup (f := fun b ↦ ‖gamma t b‖₊) (Finset.mem_univ (0 : Fin 3)))

/-- T0.D: the first dual field is a smooth incomplete vector field. -/
theorem X1_incomplete : IsIncompleteSmoothVectorField X1 := by
  refine ⟨contDiff_X1, ?_⟩
  apply not_isCompleteVectorField_of_finite_escape (contDiff_X1.of_le (by simp))
    (by norm_num : (0 : ℝ) < 1 / 2) (fun t ht ↦ hasDerivAt_gamma ht)
      tendsto_norm_gamma_atTop

end ExoticCCR
