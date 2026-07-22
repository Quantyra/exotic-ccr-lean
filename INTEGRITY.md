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

These are machine-checked polynomial identities, elementary field arithmetic, and the stated
one-dimensional real-analysis consequences. They do not constitute all of Program B.

## What this artifact does **not** assert

- Full resolution or literature status of the Jacobian conjecture beyond the finite identities proved in this tree.
- That any particular public announcement is the definitive historical priority record (see PROVENANCE.md for citations only).
- Physical significance, quantum channels, gates, continuous-variable protocols, or computational advantage.
- Poisson or Weyl endomorphism theorems (EXOTIC-CCR Gate 1+).
- Essential self-adjointness, strong CCR/Weyl relations, C*-extension, complete positivity, or dilations.
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
