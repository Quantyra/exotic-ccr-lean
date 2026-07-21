# INTEGRITY — Claim control (Gate G0)

This repository contains **Gate 0 algebraic certificates only** for Project EXOTIC-CCR.

## What this artifact asserts

1. **T0.1.** For the anchor family `F : Fin 3 → MvPolynomial (Fin 3) K`, the Jacobian determinant equals the constant polynomial `C (-2)`.
2. **T0.2.** The three evaluation identities
   - `evalMap F ![0, 0, -(1/4)] = ![-(1/4), 0, 0]`
   - `evalMap F ![1, -(3/2), 13/2] = ![-(1/4), 0, 0]` (requires `2 ≠ 0`)
   - `evalMap F ![-1, 3/2, 13/2] = ![-(1/4), 0, 0]` (requires `2 ≠ 0`)
   hold as equalities of functions `Fin 3 → K`.
3. **Packaging.** Over any field, there exists a polynomial self-map of affine 3-space with unit Jacobian determinant that is not injective (proved via `F` when `2 ≠ 0`, and via the det-1 form `G` in all characteristics).

These are finite, machine-checked polynomial identities and elementary field arithmetic.

## What this artifact does **not** assert

- Full resolution or literature status of the Jacobian conjecture beyond the finite identities proved in this tree.
- That any particular public announcement is the definitive historical priority record (see PROVENANCE.md for citations only).
- Physical significance, quantum channels, gates, continuous-variable protocols, or computational advantage.
- Poisson or Weyl endomorphism theorems (EXOTIC-CCR Gate 1+).
- Essential self-adjointness, strong CCR/Weyl relations, C*-extension, complete positivity, or dilations.
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
