# Formalization Backlog

> ## SUPERSEDED / A001 CLOSED — not an active backlog
>
> **Do not treat this file as open work.** A001 is final/published in science
> (`v0.3.9-referee-revision` / `0010354`; Zenodo `10.5281/zenodo.21715479`).
> Audited Lean freeze pin: `2e40c4c` / theorem-audit `fbcdd034`. There is
> **no active A001 theorem-development backlog**. B/C residuals are **parked**
> and do not authorize further theorem work from the rows below.
>
> **Historical snapshot — superseded 2026-07-29 (coverage note), closed 2026-08-01 (A001).**
> The inventory below predates the theorem freeze and must not be used as
> current Lean coverage. Since this snapshot, the repository has formalized the
> full polynomial Theorem B Poisson relations, Theorem C algebraic commutation
> and Weyl endomorphism, Theorem D incompleteness, the `j = 1` compact-core
> formal symmetry in `ExoticCCR.TheoremFSymmetricCore`, and the bounded
> canonical Theorems E--F surfaces described in `README.md` and `INTEGRITY.md`.
> An all-`j` analytic minimal-operator package remains outside the A001 freeze
> and is **not** an authorized open backlog item.

This matrix records Lean coverage only. A historical paper result is not Lean-covered merely
because a related algebraic lemma appears in this repository.

## Lean-covered

- **Gate-0 seed:** exact Jacobian and collision certificates in `AnchorF`, `AnchorG`,
  `Counterexample`, and `Collision`.
- **DualFields algebraic seed:** the matrix identity
  `jacobian_mul_adjugate_F`; this is algebraic packaging only, not a Poisson, Weyl, or operator
  theorem.
- **A001 B algebraic core:** `DualMatrix` defines the polynomial matrix
  `B = -(adj J)ᵀ/2` and proves `J Bᵀ = I`; `TheoremB` defines the evaluated cotangent-lift
  formula and proves explicit three-point collision/non-injectivity at zero covector.
- **A001 C partial algebraic core:** `TheoremC` defines the directional dual fields, proves
  `X_j(F_i) = δ_ij`, and proves their bracket vanishes on the three anchor coordinates.
- **A001 D sample only:** `TheoremD` defines the radical-cleared rational curve formula and
  checks the exact specialization `t = 3/8`, `s = 1/2`. This is not the parameterized identity
  and is not an incompleteness theorem.
- **B5 algebraic Slice 1:** `PolyDiffeo1D` proves the nowhere-zero derivative monotonicity and
  bijectivity results on `ℝ`, coordinatewise product bijectivity and diagonal Jacobian determinant,
  and explicit inverses for elementary polynomial shears.

## Historical paper results not yet Lean-covered

- A001 Theorem B Poisson brackets.
- A001 Theorem C full Lie-bracket identity, Piola/divergence identity, analytic symmetry, and
  Weyl endomorphism.
- A001 Theorem D parameterized algebraic identity, ODE/integral-curve statement, escape limit,
  and incompleteness conclusion.
- B001 B6/B7 analysis and classification consequences.
- C001 J* results (including the J2–J7 historical sequence).
- Any full-program conclusion assembled from the partial algebraic seeds above.

## Blocked / definition infrastructure absent

- Complete positivity (CP) and channel statements.
- von Neumann algebra (`vNa`) closure or extension statements.
- Essential self-adjointness (ESS), strong CCR/Weyl realization, and associated gate claims.
- A001 Theorems E–F: `Dom H*`, deficiency vectors, and deficiency indices.

These blocked rows require explicit operator-algebraic definitions and proof infrastructure. No
paper-only argument or algebraic proxy should be reported as Lean coverage for them.
