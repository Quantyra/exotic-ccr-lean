# INTEGRITY — Claim control

This repository contains bounded algebraic certificates for Project EXOTIC-CCR. In addition to
the Gate 0 anchor, it contains a one-dimensional real-polynomial and elementary-shear slice of
the historical B5 algebraic core.

## What this artifact asserts

1. **T0.1.** For the anchor family `F : Fin 3 → MvPolynomial (Fin 3) K`, the Jacobian determinant equals the constant polynomial `C (-2)`.
2. **T0.2.** The three evaluation identities
   - `evalMap F ![0, 0, -(1/4)] = ![-(1/4), 0, 0]`
   - `evalMap F ![1, -(3/2), 13/2] = ![-(1/4), 0, 0]` (requires `2 ≠ 0`)
   - `evalMap F ![-1, 3/2, 13/2] = ![-(1/4), 0, 0]` (requires `2 ≠ 0`)
   hold as equalities of functions `Fin 3 → K`.
3. **Packaging.** Over any field, there exists a polynomial self-map of affine 3-space with unit Jacobian determinant that is not injective (proved via `F` when `2 ≠ 0`, and via the det-1 form `G` in all characteristics).
4. **T0.B5.2.** A real univariate polynomial whose derivative is nonzero at every real point is
   strictly monotone in one orientation and is a bijection of `ℝ`.
5. **T0.B5.3.** Coordinatewise products of such maps are bijective, and their explicitly defined
   diagonal polynomial Jacobian has nonzero determinant.
6. **T0.B5.7.** Vertical and horizontal elementary polynomial shears are bijective over a
   commutative ring, with the displayed subtraction shears as explicit inverses.
7. **T0.B.1–3.** The polynomial adjugate formula gives `J Bᵀ = I`; the evaluated algebraic
   cotangent-lift formula has the displayed three zero-covector collisions and is not injective.
8. **T0.C.1–3.** The directional dual fields send `F_i` to Kronecker deltas, every row of
    the polynomial dual matrix has zero coefficient divergence, and the fields commute as
    derivations on every multivariate polynomial.
9. **T0.C.4.** The left-coefficient formulas `q_i ↦ F_i(q)` and
   `p_j ↦ ∑_k B_jk(q)p_k` define a unital algebra endomorphism of the abstract polynomial
   Weyl algebra presented by generator CCR, when `2 ≠ 0`.
10. **T0.D.** The parameterized algebraic curve identity is proved, and over `ℝ` the explicit
    curve `gamma` is an integral curve of the smooth evaluated dual field `X1` on `(0,1/2)`.
    Its norm tends to infinity as `t → (1/2)⁻`, so `X1` is incomplete.
11. **T0.E infrastructure (bounded claim).** The artifact defines `L²(ℝ³)`, compactly supported
    smooth test functions, the pointwise expression `-iX`, and essential self-adjointness as
    closability plus self-adjointness of the closure. It proves the pointwise polynomial
    divergence identity and packages `X1` as smooth, divergence-free, and incomplete.
12. **T0.E conditional only.** Given a supplied analytic realization and the explicit proposition
    `TransportNecessityStatement`, `theoremE_of_transportNecessity` concludes that the realization
    is not essentially self-adjoint. The proposition is a definition/hypothesis, not an axiom or
    an unconditional theorem.

These are machine-checked polynomial identities, elementary field arithmetic, and the stated
one-dimensional real-analysis consequences. They do not constitute all of Program B.

## What this artifact does **not** assert

- Full resolution or literature status of the Jacobian conjecture beyond the finite identities proved in this tree.
- That any particular public announcement is the definitive historical priority record (see PROVENANCE.md for citations only).
- Physical significance, quantum channels, gates, continuous-variable protocols, or computational advantage.
- Poisson-bracket theorems, analytic/operator CCR realizations, or exponentiated Weyl relations.
- Essential self-adjointness, strong CCR/Weyl relations, C*-extension, complete positivity, or dilations.
- Unconditional A001 Theorem E. The repository does not construct the `L²` realization of
  `-iX1`, prove transport necessity, or construct a nonzero vector in `ker(H† ± i)`.
- A001 Theorem F, `Dom H*`, and all deficiency-index values. No deficiency indices are claimed.
- Full B001, B6/B7 analytic classification, von Neumann algebra (`vNa`) conclusions, or any
  operator realization derived from the B5 algebraic slice.
- Experimental, hardware, or metrology claims.
- Any P-vs-NP, circuit lower bound, or complexity separation.

## Claim boundary (charter alignment)

Per the EXOTIC-CCR Research Charter v1.0:

- Algebra endomorphisms are not automatically state transformations, unitary symmetries, or quantum channels.
- Preservation of formal commutators on polynomials is weaker than exponentiated Weyl relations for self-adjoint operators.
- Gate G0 freezes the algebraic anchor; physical admissibility is deferred to later gates with independent evidence packages.

## Release discipline

- Version tags must list proved theorems and restated non-claims.
- Do not upgrade language from “algebraic certificate” to “physical result” without a new gate and evidence package.
- Zenodo metadata must carry the same non-claims language.
