# Formalization Backlog

This matrix records Lean coverage only. A historical paper result is not Lean-covered merely
because a related algebraic lemma appears in this repository.

## Lean-covered

- **Gate-0 seed:** exact Jacobian and collision certificates in `AnchorF`, `AnchorG`,
  `Counterexample`, and `Collision`.
- **DualFields algebraic seed:** the matrix identity
  `jacobian_mul_adjugate_F`; this is algebraic packaging only, not a Poisson, Weyl, or operator
  theorem.
- **B5 algebraic Slice 1:** `PolyDiffeo1D` proves the nowhere-zero derivative monotonicity and
  bijectivity results on `ℝ`, coordinatewise product bijectivity and diagonal Jacobian determinant,
  and explicit inverses for elementary polynomial shears.

## Historical paper results not yet Lean-covered

- A001 Theorems B–F, except for the separately listed DualFields algebraic seed.
- B001 B6/B7 analysis and classification consequences.
- C001 J* results (including the J2–J7 historical sequence).
- Any full-program conclusion assembled from the partial algebraic seeds above.

## Blocked / definition infrastructure absent

- Complete positivity (CP) and channel statements.
- von Neumann algebra (`vNa`) closure or extension statements.
- Essential self-adjointness (ESS), strong CCR/Weyl realization, and associated gate claims.

These blocked rows require explicit operator-algebraic definitions and proof infrastructure. No
paper-only argument or algebraic proxy should be reported as Lean coverage for them.
