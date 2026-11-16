import ExoticCCR.TheoremC
import ExoticCCR.TheoremFSymmetricCore
import ExoticCCR.TheoremFMaximalSheetDensity

noncomputable section
open MeasureTheory Set TopologicalSpace MvPolynomial
open scoped LinearPMap ENNReal ComplexConjugate
namespace ExoticCCR

/-- The actual smooth dual field given by row j of the polynomial inverse transpose. -/
def analyticDualField (j : Fin 3) (q : R3) : R3 :=
  fun k => MvPolynomial.eval q (dualMatrixF Real j k)

/-- Every polynomial dual field is smooth. -/
theorem contDiff_analyticDualField (j : Fin 3) :
    ContDiff Real ⊤ (analyticDualField j) := by
  exact contDiff_pi.mpr (fun k => contDiff_eval_mvPolynomial (dualMatrixF Real j k))

/-- The existing all-row polynomial divergence certificate. -/
theorem sum_pderiv_dualMatrixF_row (j : Fin 3) :
    (∑ i : Fin 3, pderiv i (dualMatrixF Real j i)) = 0 :=
  dualFieldDivergence_eq_zero j

theorem analyticDivergence_analyticDualField_eq_zero (j : Fin 3) (q : R3) : analyticDivergence (analyticDualField j) q = 0 := by
  have hdiff : ∀ k : Fin 3, DifferentiableAt ℝ (fun x : R3 => (analyticDualField j) x k) q := fun k =>
    (hasFDerivAt_eval_mvPolynomial (dualMatrixF ℝ j k) q).differentiableAt
  have hcoord : ∀ i : Fin 3, fderiv ℝ (analyticDualField j) q (Pi.single i 1) i =
      eval q (pderiv i (dualMatrixF ℝ j i)) := by
    intro i
    have hpi : fderiv ℝ (analyticDualField j) q = ContinuousLinearMap.pi
        fun k => fderiv ℝ (fun x : R3 => (analyticDualField j) x k) q := fderiv_pi hdiff
    rw [hpi, ContinuousLinearMap.pi_apply]
    have heval : fderiv ℝ (fun x : R3 => (analyticDualField j) x i) q = evalPDeriv (dualMatrixF ℝ j i) q :=
      (hasFDerivAt_eval_mvPolynomial (dualMatrixF ℝ j i) q).fderiv
    rw [heval]
    simp [evalPDeriv, Pi.single_apply]
  rw [analyticDivergence]
  calc
    (∑ i, fderiv ℝ (analyticDualField j) q (Pi.single i 1) i)
        = ∑ i : Fin 3, eval q (pderiv i (dualMatrixF ℝ j i)) :=
      Finset.sum_congr rfl fun i _ => hcoord i
    _ = eval q (∑ i : Fin 3, pderiv i (dualMatrixF ℝ j i)) := by rw [map_sum]
    _ = 0 := by rw [sum_pderiv_dualMatrixF_row, map_zero]


theorem transportAction_testFunction_pairing
    (X : R3 -> R3) (hX : ContDiff Real ⊤ X)
    (hDiv : forall q : R3, analyticDivergence X q = 0) (φ ψ : CcinftyR3) :
    inner ℂ (transportAction X hX.continuous φ) (testFunctionToL2 ψ) =
      inner ℂ (testFunctionToL2 φ) (transportAction X hX.continuous ψ) := by
  rw [show transportAction X hX.continuous φ =
      (transportExpressionMemLp X hX.continuous φ).toLp
        (minimalTransportExpression X φ) from rfl,
    testFunctionToL2_apply,
    inner_toLp_toLp_eq_integral]
  rw [show transportAction X hX.continuous ψ =
      (transportExpressionMemLp X hX.continuous ψ).toLp
        (minimalTransportExpression X ψ) from rfl,
    testFunctionToL2_apply,
    inner_toLp_toLp_eq_integral]
  have hIBP := integral_transport_derivative_eq_neg_of_analyticDivergence_eq_zero
    X hX hDiv φ ψ
  have hleft :
      (∫ q : R3, inner ℂ (minimalTransportExpression X φ q) (ψ q) ∂volume) =
        Complex.I *
          (∫ q : R3, star (fderiv ℝ (φ : R3 → ℂ) q (X q)) * ψ q ∂volume) := by
    calc
      (∫ q : R3, inner ℂ (minimalTransportExpression X φ q) (ψ q) ∂volume) =
          ∫ q : R3, Complex.I *
            (star (fderiv ℝ (φ : R3 → ℂ) q (X q)) * ψ q) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with q
              rw [show minimalTransportExpression X φ q =
                -Complex.I * fderiv ℝ (φ : R3 → ℂ) q (X q) from rfl]
              rw [RCLike.inner_apply', RCLike.star_def, map_mul, map_neg, Complex.conj_I]
              ring
      _ = _ := by rw [integral_const_mul]
  have hright :
      (∫ q : R3, inner ℂ (φ q) (minimalTransportExpression X ψ q) ∂volume) =
        -Complex.I *
          (∫ q : R3, star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X q) ∂volume) := by
    calc
      (∫ q : R3, inner ℂ (φ q) (minimalTransportExpression X ψ q) ∂volume) =
          ∫ q : R3, -Complex.I *
            (star (φ q) * fderiv ℝ (ψ : R3 → ℂ) q (X q)) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with q
              rw [show minimalTransportExpression X ψ q =
                -Complex.I * fderiv ℝ (ψ : R3 → ℂ) q (X q) from rfl]
              rw [RCLike.inner_apply', RCLike.star_def]
              ring
      _ = _ := by rw [integral_const_mul]
  rw [hleft, hright, hIBP]
  ring


/-- Canonical minimal dual transport operators, all with the same test-function domain. -/
def H_j_min (j : Fin 3) :=
  minimalTransportCore (analyticDualField j) (contDiff_analyticDualField j).continuous

/-- All three actual canonical dual operators are symmetric on their common compact smooth core. -/
theorem H_j_min_isFormalAdjoint (j : Fin 3) :
    (H_j_min j).IsFormalAdjoint (H_j_min j) :=
  minimalTransportCore_isFormalAdjoint_of_testFunctionPairing
    (analyticDualField j) (contDiff_analyticDualField j).continuous
    (transportAction_testFunction_pairing (analyticDualField j)
      (contDiff_analyticDualField j) (analyticDivergence_analyticDualField_eq_zero j))

/-- Evaluation translates the checked polynomial duality into an actual derivative. -/
theorem fderiv_anchor_on_dual (i j : Fin 3) (q : R3) :
    fderiv Real (fun x : R3 => eval x (F Real i)) q (analyticDualField j q) =
      if i = j then 1 else 0 := by
  rw [(hasFDerivAt_eval_mvPolynomial (F Real i) q).fderiv]
  have h := congrArg (eval q) (dualField_F (K := Real) (by norm_num) i j)
  simpa [evalPDeriv, analyticDualField, dualField, map_sum, map_mul, mul_comm,
    apply_ite] using h

/-- The concrete anchor coordinate acting as a complex-valued multiplier. -/
def anchorComplex (i : Fin 3) (q : R3) : Complex :=
  (eval q (F Real i) : Complex)

theorem contDiff_anchorComplex (i : Fin 3) :
    ContDiff Real ⊤ (anchorComplex i) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_eval_mvPolynomial (F Real i))

theorem fderiv_anchorComplex_on_dual (i j : Fin 3) (q : R3) :
    fderiv Real (anchorComplex i) q (analyticDualField j q) =
      if i = j then 1 else 0 := by
  have hchain : fderiv Real (anchorComplex i) q =
      Complex.ofRealCLM.comp (evalPDeriv (F Real i) q) :=
    (Complex.ofRealCLM.hasFDerivAt.comp q
      (hasFDerivAt_eval_mvPolynomial (F Real i) q)).fderiv
  rw [hchain]
  change ((evalPDeriv (F Real i) q (analyticDualField j q) : Real) : Complex) = _
  have hreal := fderiv_anchor_on_dual i j q
  rw [(hasFDerivAt_eval_mvPolynomial (F Real i) q).fderiv] at hreal
  rw [hreal]
  split_ifs <;> simp

/-- Polynomial multiplication preserves the concrete compact smooth core. -/
def anchorMultiplication (i : Fin 3) (phi : CcinftyR3) : CcinftyR3 :=
  ⟨fun q => anchorComplex i q * phi q,
    (contDiff_anchorComplex i).mul phi.contDiff,
    phi.hasCompactSupport.mul_left, Set.subset_univ _⟩

/-- Smooth dual transport preserves the same compact smooth core. -/
def dualTransportOnCore (j : Fin 3) (phi : CcinftyR3) : CcinftyR3 :=
  ⟨minimalTransportExpression (analyticDualField j) phi,
    contDiff_const.mul ((phi.contDiff.fderiv_right (by simp)).clm_apply
      (contDiff_analyticDualField j)),
    hasCompactSupport_minimalTransportExpression (analyticDualField j) phi,
    Set.subset_univ _⟩

/-- Multiplication is linear on its invariant compact smooth domain. -/
def anchorMultiplicationMap (i : Fin 3) : CcinftyR3 →ₗ[Complex] CcinftyR3 where
  toFun := anchorMultiplication i
  map_add' phi psi := by
    ext q
    change anchorComplex i q * (phi q + psi q) =
      anchorComplex i q * phi q + anchorComplex i q * psi q
    ring
  map_smul' c phi := by
    ext q
    change anchorComplex i q * (c * phi q) = c * (anchorComplex i q * phi q)
    ring

/-- Graph map for polynomial multiplication on the canonical embedded core. -/
def anchorMultiplicationGraphMap (i : Fin 3) : CcinftyR3 →ₗ[Complex] L2R3 × L2R3 :=
  testFunctionToL2.prod (testFunctionToL2.comp (anchorMultiplicationMap i))

theorem anchorMultiplicationGraph_functional (i : Fin 3) :
    forall (x : L2R3 × L2R3), x ∈ LinearMap.range (anchorMultiplicationGraphMap i) ->
      x.fst = 0 -> x.snd = 0 := by
  rintro _ ⟨phi, rfl⟩ hphi
  have : phi = 0 := testFunctionToL2_injective
    (by simpa [anchorMultiplicationGraphMap] using hphi)
  subst phi
  simp [anchorMultiplicationGraphMap]

/-- Actual polynomial multiplication as a partial L2 operator on the common core. -/
def M_F_min (i : Fin 3) : L2R3 →ₗ.[Complex] L2R3 :=
  (LinearMap.range (anchorMultiplicationGraphMap i)).toLinearPMap

theorem M_F_min_domain (i : Fin 3) :
    (M_F_min i).domain = LinearMap.range testFunctionToL2 := by
  ext u
  simp [M_F_min, anchorMultiplicationGraphMap, Submodule.toLinearPMap_domain,
    LinearMap.mem_range]

theorem M_F_min_mem_domain (i : Fin 3) (phi : CcinftyR3) :
    testFunctionToL2 phi ∈ (M_F_min i).domain := by
  rw [M_F_min_domain]
  exact LinearMap.mem_range_self testFunctionToL2 phi

theorem M_F_min_apply (i : Fin 3) (phi : CcinftyR3) :
    M_F_min i ⟨testFunctionToL2 phi, M_F_min_mem_domain i phi⟩ =
      testFunctionToL2 (anchorMultiplication i phi) := by
  symm
  rw [LinearPMap.image_iff]
  unfold M_F_min
  rw [Submodule.toLinearPMap_graph_eq _ (anchorMultiplicationGraph_functional i)]
  exact LinearMap.mem_range_self (anchorMultiplicationGraphMap i) phi

/-- The newly bundled smooth transport and old L2 action have identical representatives. -/
theorem testFunctionToL2_dualTransportOnCore (j : Fin 3) (phi : CcinftyR3) :
    testFunctionToL2 (dualTransportOnCore j phi) =
      transportAction (analyticDualField j) (contDiff_analyticDualField j).continuous phi := rfl

theorem H_j_min_domain (j : Fin 3) :
    (H_j_min j).domain = LinearMap.range testFunctionToL2 :=
  minimalTransportCore_domain (analyticDualField j) (contDiff_analyticDualField j).continuous

theorem H_j_min_mem_domain (j : Fin 3) (phi : CcinftyR3) :
    testFunctionToL2 phi ∈ (H_j_min j).domain := by
  rw [H_j_min_domain]
  exact LinearMap.mem_range_self testFunctionToL2 phi

theorem H_j_min_apply (j : Fin 3) (phi : CcinftyR3) :
    H_j_min j ⟨testFunctionToL2 phi, H_j_min_mem_domain j phi⟩ =
      testFunctionToL2 (dualTransportOnCore j phi) := by
  rw [testFunctionToL2_dualTransportOnCore]
  exact minimalTransportCore_apply (analyticDualField j)
    (contDiff_analyticDualField j).continuous phi

/-- The actual H action lies in the multiplication domain. -/
theorem H_j_min_preserves_common_core (i j : Fin 3) (phi : CcinftyR3) :
    H_j_min j ⟨testFunctionToL2 phi, H_j_min_mem_domain j phi⟩ ∈ (M_F_min i).domain := by
  rw [H_j_min_apply]
  exact M_F_min_mem_domain i (dualTransportOnCore j phi)

/-- The actual multiplication action lies in the H domain. -/
theorem M_F_min_preserves_common_core (i j : Fin 3) (phi : CcinftyR3) :
    M_F_min i ⟨testFunctionToL2 phi, M_F_min_mem_domain i phi⟩ ∈ (H_j_min j).domain := by
  rw [M_F_min_apply]
  exact H_j_min_mem_domain j (anchorMultiplication i phi)

/-- Product-rule commutator of the two actual operators on compact smooth functions. -/
theorem commonCore_commutator (i j : Fin 3) (phi : CcinftyR3) :
    anchorMultiplication i (dualTransportOnCore j phi) -
      dualTransportOnCore j (anchorMultiplication i phi) =
        (if i = j then Complex.I else 0) • phi := by
  ext q
  change anchorComplex i q *
      (-Complex.I * fderiv Real (phi : R3 -> Complex) q (analyticDualField j q)) -
    (-Complex.I * fderiv Real (fun x : R3 => anchorComplex i x * phi x) q
      (analyticDualField j q)) = (if i = j then Complex.I else 0) * phi q
  rw [fderiv_mul ((contDiff_anchorComplex i).differentiable (by simp)).differentiableAt
    (phi.contDiff.differentiable (by simp)).differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_anchorComplex_on_dual]
  split_ifs <;> ring

/-- The all-index CCR is an equality of the actual partial-L2 compositions on the common core. -/
theorem theoremC_commonCore_commutator (i j : Fin 3) (phi : CcinftyR3) :
    M_F_min i ⟨H_j_min j ⟨testFunctionToL2 phi, H_j_min_mem_domain j phi⟩,
        H_j_min_preserves_common_core i j phi⟩ -
      H_j_min j ⟨M_F_min i ⟨testFunctionToL2 phi, M_F_min_mem_domain i phi⟩,
        M_F_min_preserves_common_core i j phi⟩ =
      (if i = j then Complex.I else 0) • testFunctionToL2 phi := by
  have h := congrArg testFunctionToL2 (commonCore_commutator i j phi)
  simp only [map_sub, map_smul] at h
  simpa only [H_j_min_apply, M_F_min_apply] using h

/-- The evaluated all-index field is the existing canonical polynomial field. -/
theorem analyticDualField_eq_dualVectorField (j : Fin 3) :
    analyticDualField j = dualVectorField j := rfl

/-- The all-index package retains exactly the previous canonical escaping operator. -/
theorem H_j_min_one_eq_H_X1_min : H_j_min 1 = H_X1_min := rfl

/-- The common domain is dense in the ambient L2 space. -/
theorem H_j_min_dense_domain (j : Fin 3) : Dense ((H_j_min j).domain : Set L2R3) := by
  rw [H_j_min_domain]
  exact testFunctionL2_dense

end ExoticCCR
