/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFVonNeumannGraph
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The first von Neumann graph formula for Theorem F

This module proves the orthogonal graph decomposition of the adjoint of the
canonical symmetric minimal transport core.  The residual after projection
onto the closed minimal graph is split constructively into the deficiency
lines at `+i` and `-i`.
-/

noncomputable section

open scoped LinearPMap

namespace ExoticCCR

/-- A graph vector orthogonal to the minimal graph has its second component in
the adjoint domain, and applying the adjoint to that component gives the
negative of its first component. -/
theorem residual_second_mem_adjoint_domain_and_apply
    {u v : L2R3}
    (horth :
      toGraphSpace (u, v) ∈ minimalGraphL2.topologicalClosureᗮ) :
    ∃ hv : v ∈ (H_X1_min†).domain, H_X1_min† ⟨v, hv⟩ = -u := by
  have hpair : ∀ φ : H_X1_min.domain,
      inner ℂ (-u) (φ : L2R3) = inner ℂ v (H_X1_min φ) := by
    intro φ
    have hgraph : toGraphSpace ((φ : L2R3), H_X1_min φ) ∈
        minimalGraphL2.topologicalClosure :=
      minimalGraphL2.le_topologicalClosure
        ((mem_graphL2_iff_exists H_X1_min).mpr ⟨φ, rfl⟩)
    have hzero :
        inner ℂ (toGraphSpace ((φ : L2R3), H_X1_min φ))
          (toGraphSpace (u, v)) = 0 :=
      (Submodule.mem_orthogonal _ _).mp horth _ hgraph
    rw [toGraphSpace_inner] at hzero
    calc
      inner ℂ (-u) (φ : L2R3) = -inner ℂ u (φ : L2R3) := by
        rw [inner_neg_left]
      _ = inner ℂ v (H_X1_min φ) := by
        apply neg_eq_iff_add_eq_zero.mpr
        have hs := congrArg (starRingEnd ℂ) hzero
        simpa only [map_add, map_zero, inner_conj_symm] using hs
  have hv : v ∈ (H_X1_min†).domain :=
    LinearPMap.mem_adjoint_domain_of_exists v ⟨-u, hpair⟩
  exact ⟨hv, LinearPMap.adjoint_apply_eq H_X1_min_dense_domain ⟨v, hv⟩ hpair⟩

/-- The part of the adjoint graph orthogonal to the closed minimal graph is
exactly the sum of the two deficiency lines. -/
theorem adjointGraphL2_inf_orthogonal_minimalGraphL2_topologicalClosure :
    minimalGraphL2.topologicalClosureᗮ ⊓ adjointGraphL2 =
      deficiencyLine Complex.I ⊔ deficiencyLine (-Complex.I) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxOrth, hxAdj⟩ := Submodule.mem_inf.mp hx
    obtain ⟨φ, rfl⟩ := (mem_graphL2_iff_exists (H_X1_min†)).mp hxAdj
    obtain ⟨hv, hvEq⟩ :=
      residual_second_mem_adjoint_domain_and_apply hxOrth
    let ψ : (H_X1_min†).domain := ⟨H_X1_min† φ, hv⟩
    have hψ : H_X1_min† ψ = -(φ : L2R3) := hvEq
    have hIhalfI :
        Complex.I * ((2 : ℂ)⁻¹ * Complex.I) = -(2 : ℂ)⁻¹ := by
      calc
        Complex.I * ((2 : ℂ)⁻¹ * Complex.I) =
            (2 : ℂ)⁻¹ * (Complex.I * Complex.I) := by ring
        _ = -(2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; ring
    have hNegIhalfI :
        (-Complex.I) * ((2 : ℂ)⁻¹ * Complex.I) = (2 : ℂ)⁻¹ := by
      calc
        (-Complex.I) * ((2 : ℂ)⁻¹ * Complex.I) =
            -(2 : ℂ)⁻¹ * (Complex.I * Complex.I) := by ring
        _ = (2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; ring
    let P : (H_X1_min†).domain :=
      (2 : ℂ)⁻¹ • (φ - Complex.I • ψ)
    let Q : (H_X1_min†).domain :=
      (2 : ℂ)⁻¹ • (φ + Complex.I • ψ)
    let p : L2R3 := P
    let q : L2R3 := Q
    have hp : p ∈ adjointEigenspace H_X1_min Complex.I := by
      rw [mem_adjointEigenspace_iff]
      refine ⟨P.property, ?_⟩
      change H_X1_min† P = Complex.I • (P : L2R3)
      dsimp [P]
      rw [LinearPMap.map_smul, LinearPMap.map_sub, LinearPMap.map_smul, hψ]
      dsimp [ψ]
      simp only [smul_sub, smul_neg, smul_smul]
      rw [hIhalfI]
      module
    have hq : q ∈ adjointEigenspace H_X1_min (-Complex.I) := by
      rw [mem_adjointEigenspace_iff]
      refine ⟨Q.property, ?_⟩
      change H_X1_min† Q = (-Complex.I) • (Q : L2R3)
      dsimp [Q]
      rw [LinearPMap.map_smul, LinearPMap.map_add, LinearPMap.map_smul, hψ]
      dsimp [ψ]
      simp only [smul_add, smul_neg, smul_smul]
      rw [hNegIhalfI]
      module
    rw [Submodule.mem_sup]
    refine ⟨toGraphSpace (p, Complex.I • p),
      mem_deficiencyLine_iff.mpr ⟨p, hp, rfl⟩,
      toGraphSpace (q, (-Complex.I) • q),
      mem_deficiencyLine_iff.mpr ⟨q, hq, rfl⟩, ?_⟩
    rw [← map_add]
    congr 1
    change (p, Complex.I • p) + (q, (-Complex.I) • q) =
      ((φ : L2R3), H_X1_min† φ)
    apply Prod.ext
    · dsimp [p, q, P, Q, ψ]
      module
    · dsimp [p, q, P, Q, ψ]
      simp only [smul_sub, smul_add, smul_smul]
      rw [hIhalfI, hNegIhalfI]
      module
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨deficiencyLine_le_orthogonal_topologicalClosure Complex.I
        Complex.I_sq hx, (deficiencyLine_eq_inf _ ▸ hx).1⟩
    · intro x hx
      exact ⟨deficiencyLine_le_orthogonal_topologicalClosure (-Complex.I)
        (by rw [neg_sq, Complex.I_sq]) hx,
        (deficiencyLine_eq_inf _ ▸ hx).1⟩

/-- The first von Neumann formula for the canonical minimal transport core:
the adjoint graph is the sum of the closed minimal graph and its two
deficiency lines. -/
theorem adjointGraphL2_eq_minimalGraphL2_topologicalClosure_sup_deficiencyLines :
    adjointGraphL2 =
      minimalGraphL2.topologicalClosure ⊔
        deficiencyLine Complex.I ⊔ deficiencyLine (-Complex.I) := by
  have hle : minimalGraphL2.topologicalClosure ≤ adjointGraphL2 := by
    rw [minimalGraphL2_topologicalClosure_eq_graphL2_closure]
    intro x hx
    exact (mem_graphL2_iff (H_X1_min†)).mpr
      (LinearPMap.le_graph_of_le H_X1_min_closure_le_adjoint
        ((mem_graphL2_iff H_X1_min.closure).mp hx))
  calc
    adjointGraphL2 =
        minimalGraphL2.topologicalClosure ⊔
          minimalGraphL2.topologicalClosureᗮ ⊓ adjointGraphL2 :=
      (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle).symm
    _ = minimalGraphL2.topologicalClosure ⊔
          (deficiencyLine Complex.I ⊔ deficiencyLine (-Complex.I)) := by
      rw [adjointGraphL2_inf_orthogonal_minimalGraphL2_topologicalClosure]
    _ = minimalGraphL2.topologicalClosure ⊔
          deficiencyLine Complex.I ⊔ deficiencyLine (-Complex.I) :=
      (sup_assoc _ _ _).symm

end ExoticCCR
