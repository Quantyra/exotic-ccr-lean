# exotic-ccr-lean

Lean 4 algebraic certificates for the **EXOTIC-CCR** program (Quantyra).

This repository formalizes finite exact algebraic identities used as the frozen anchor object for Project EXOTIC-CCR (Exotic Endomorphisms of the Canonical Commutation Relations): Jacobian determinant certificates and three-point collision witnesses for an explicit polynomial map \(F\colon K^3\to K^3\), plus standard non-injectivity packaging.

**Organization:** Quantyra Inc.  
**Program:** EXOTIC-CCR research charter (Gate G0 / WP0)  
**License:** Apache-2.0  
**Version:** 0.1.0

## What is proved

| ID | Statement | Module |
|----|-----------|--------|
| T0.1 | `jacobianDet F = C (-2)` | `ExoticCCR.AnchorF` |
| T0.2 | Three collision identities for F | `ExoticCCR.AnchorF` |
| T0.B.1 | Polynomial `B = -(adj J)ᵀ/2` and `J * Bᵀ = I` (when `2 ≠ 0`) | `ExoticCCR.DualMatrix` |
| T0.B.2–3 | Cotangent-lift evaluation; three zero-covector collisions and non-injectivity | `ExoticCCR.TheoremB` |
| T0.C.1 | Directional dual fields satisfy `X_j(F_i) = δ_ij` | `ExoticCCR.TheoremC` |
| T0.C.2 | Every row of the polynomial dual matrix has zero coefficient divergence | `ExoticCCR.TheoremC` |
| T0.C.3 | The dual fields commute as derivations on every multivariate polynomial | `ExoticCCR.TheoremC` |
| T0.D.alg partial | Exact rational specialization of the proposed radical-cleared curve | `ExoticCCR.TheoremD` |
| T0.Collision | Three-point collision packaging + gate0 algebra bundle | `ExoticCCR.Collision` |
| T0.B5.2 | A real polynomial with nowhere-zero derivative is strictly monotone in one orientation, injective, surjective, and bijective | `ExoticCCR.PolyDiffeo1D` |
| T0.B5.3 | The coordinatewise product map is bijective; its diagonal polynomial Jacobian has determinant `p'(x) * q'(y)`, nonzero under the derivative hypotheses | `ExoticCCR.PolyDiffeo1D` |
| T0.B5.7 | Vertical and horizontal elementary polynomial shears over a commutative ring are bijective, with explicit polynomial inverses | `ExoticCCR.PolyDiffeo1D` |
| — | `jacobianDet G = 1` and G collisions / char-2 case | `ExoticCCR.AnchorG` |
| — | Unit-Jacobian non-injectivity packaging (char ≠ 2 via F; all char via G) | `ExoticCCR.Counterexample` |

Anchor polynomials (charter form):

```
F0 = (1 + X0*X1)^3 * X2 + X1^2 * (1 + X0*X1) * (4 + 3*(X0*X1))
F1 = X1 + 3*X0*(1 + X0*X1)^2 * X2 + 3*X0*X1^2 * (4 + 3*(X0*X1))
F2 = 2*X0 - 3*X0^2*X1 - X0^3*X2
```

Collisions (char ≠ 2 as needed):

- `F(0, 0, -1/4) = (-1/4, 0, 0)`
- `F(1, -3/2, 13/2) = (-1/4, 0, 0)`
- `F(-1, 3/2, 13/2) = (-1/4, 0, 0)`

## Non-claims

See [INTEGRITY.md](INTEGRITY.md). In short:

- These are bounded algebraic and real-polynomial analysis certificates only.
- This repo does **not** claim full status of the Jacobian conjecture literature beyond the identities proved here.
- This repo does **not** claim physical, operator-algebraic, channel, gate, or computational-advantage results.
- Poisson brackets, Weyl endomorphisms, incompleteness, self-adjointness, deficiency indices, CCR realization, and CP maps are **not proved** by these algebraic slices.
- A001 Theorems E–F remain **blocked** on adjoint-domain and deficiency-index infrastructure.

## Build

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake exe cache get
lake build
```

Toolchain: see `lean-toolchain` (pinned with mathlib via `lakefile.toml`).

## Provenance

Quantyra **independent reimplementation** of the Gate-0 algebraic anchor. Sources credited in [PROVENANCE.md](PROVENANCE.md):

1. L. Alpöge announcement (19 July 2026)
2. D. Cureton Lean 4 formalization (`deancureton/jacobian`) — structure reference only; this is not a git fork
3. D. Speyer note (Secret Blogging Seminar, 20 July 2026)

Those works are **not** Quantyra products. This repository is a clean Quantyra artifact under Apache-2.0.

## Related Quantyra surfaces

- Science scaffold (not merged here): [Quantyra-Jacobian-Weyl-QC](https://github.com/Quantyra) local path / planning lane
- Planning: Quantyra-Planning2 story S013 / epic E005

## Citation

See [CITATION.cff](CITATION.cff). Zenodo DOI: pending GitHub–Zenodo integration (see [docs/zenodo-status.md](docs/zenodo-status.md)).

## License

Copyright 2026 Quantyra / Daniel Eric Fredriksen. Apache-2.0. See [LICENSE](LICENSE).
