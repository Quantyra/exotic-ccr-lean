# exotic-ccr-lean

Lean 4 algebraic certificates for the **EXOTIC-CCR** program (Quantyra).

This repository formalizes finite exact algebraic identities used as the frozen anchor object for Project EXOTIC-CCR (Exotic Endomorphisms of the Canonical Commutation Relations): Jacobian determinant certificates and three-point collision witnesses for an explicit polynomial map \(F\colon K^3\to K^3\), plus standard non-injectivity packaging.

**Organization:** Quantyra Inc.  
**Program:** EXOTIC-CCR research charter (Gate G0 / WP0)  
**License:** Apache-2.0  
**Version:** 0.1.7 (full algebraic Theorem B, including canonical Poisson generator brackets)

## What is proved

| ID | Statement | Module |
|----|-----------|--------|
| T0.1 | `jacobianDet F = C (-2)` | `ExoticCCR.AnchorF` |
| T0.2 | Three collision identities for F | `ExoticCCR.AnchorF` |
| T0.B.1 | Polynomial `B = -(adj J)ᵀ/2` and `J * Bᵀ = I` (when `2 ≠ 0`) | `ExoticCCR.DualMatrix` |
| T0.B.2–3 | Cotangent-lift evaluation; three zero-covector collisions and non-injectivity | `ExoticCCR.TheoremB` |
| T0.B.4 | The transformed polynomial phase-space generators satisfy `{Q_i,Q_j}=0`, `{P_i,P_j}=0`, and `{Q_i,P_j}=δ_ij` for the canonical Poisson bracket (when `2 ≠ 0`) | `ExoticCCR.Poisson` |
| T0.C.1 | Directional dual fields satisfy `X_j(F_i) = δ_ij` | `ExoticCCR.TheoremC` |
| T0.C.2 | Every row of the polynomial dual matrix has zero coefficient divergence | `ExoticCCR.TheoremC` |
| T0.C.3 | The dual fields commute as derivations on every multivariate polynomial | `ExoticCCR.TheoremC` |
| T0.C.4 | The left-coefficient formulas `q_i ↦ F_i(q)`, `p_j ↦ ∑_k B_jk(q)p_k` define a unital endomorphism of the abstract polynomial Weyl algebra and preserve its generator CCR | `ExoticCCR.TheoremCWeyl` |
| T0.D | The explicit curve `gamma` satisfies `evalMap F (gamma t) = ![0,t,2]`, is an integral curve of the smooth dual field `X1` on `(0,1/2)`, escapes every norm ball at `1/2`, and proves `X1` incomplete | `ExoticCCR.TheoremD` |
| T0.E-infra | `L²(ℝ³)`, the compactly supported smooth core, the pointwise expression `-iX`, and `IsEssentiallySelfAdjoint := IsClosable ∧ IsSelfAdjoint closure` are defined; `divergence_X1_eq_zero` and `X1_smooth_divergenceFree_incomplete` are unconditional | `ExoticCCR.TransportOperator`, `ExoticCCR.TheoremE` |
| T0.E-core | The canonical minimal transport core on embedded compactly supported smooth functions is constructed unconditionally. A nonzero adjoint eigenvector at `±i` unconditionally obstructs essential self-adjointness for any densely defined partial operator | `ExoticCCR.TransportCore`, `ExoticCCR.LinearPMapDeficiency`, `ExoticCCR.TheoremE` |
| T0.E-density | Compactly supported smooth test functions are dense in `L²(ℝ³)`, and the canonical minimal transport core has dense domain | `ExoticCCR.TransportCore` |
| T0.E-deficiency-conditional | Given a nonzero weak `-i` eigenvector for the canonical `X1` core, `theoremE_of_forwardWeakDeficiency` proves that core is not essentially self-adjoint | `ExoticCCR.TheoremEDeficiency` |
| T0.E-conditional | For any supplied `MinimalTransportRealization X1`, `theoremE_of_transportNecessity` derives failure of essential self-adjointness from the explicit hypothesis `TransportNecessityStatement` | `ExoticCCR.TheoremE` |
| T0.F-wall-base | The forward-wall cubic vanishes at `(a,s,c) = (0,1/2,2)`, while its formal `s`-derivative expression equals `-1/2` there | `ExoticCCR.TheoremFForwardWall` |
| T0.F-wall-reconstruction | A root of the displayed wall cubic reconstructs an explicit preimage of `(a,s,c)` under `F` whenever the reconstruction denominators are nonzero | `ExoticCCR.TheoremFForwardWall` |
| T0.F-forward-branch | The polynomial divided-difference extension has a smooth local varying-`β` `r+` germ at `√2`. It admits an open positive punctured reconstruction domain accumulating at the wall base; the branch map is smooth there, evaluates under `F` to `(a, β(a,c)-τ², c)`, is injective on its positive sheet, and its first coordinate and norm tend to infinity at the base within that sheet | `ExoticCCR.TheoremFForwardBranch` |
| T0.F-branch-density-data | The Fréchet derivative of real `evalMap F` is the evaluated polynomial Jacobian with determinant `-2`; on the open branch domain its chain derivative equals the target-map derivative. The reciprocal factor is `1/2`. The positive parameter domain is open, the standard-coordinate branch derivative is bijective with Jacobian `|τ|`, and consequently the branch image is open (and measurable). Mathlib's Jacobian change-of-variables formula is applied to the squared norm of `uMinus` on the image. For continuous compactly supported `χ`, the Gaussian candidate density and its `|τ|`-weighted square are integrable on the relevant parameter domains; a compactly supported cutoff can be chosen so that the measurable zero extension `uMinus` determines a nonzero vector of ambient `L²(ℝ³)`. Locally, `d(branchMap)/dτ=(-2τ)X1`, and reparameterization by the target coordinate `s=β-τ²` gives the pointwise characteristic identity `d uMinus/ds=uMinus`. A separate theorem records the exact unresolved finite-boundary condition: continuity of the zero extension at an artificial branch boundary would force the parameter density to tend to zero there | `ExoticCCR.TheoremFJacobianFDeriv`, `ExoticCCR.TheoremFBranchDensity` |
| T0.F-saturation-infrastructure | Every `ForwardBranchOpen` records the positive half-ball present in its construction. Shrinking it gives a nonempty open transverse set with full vertical segments and fixed-parameter wall escape. Square-root reparameterization by the anchor `s` coordinate produces an inhabited `ForwardSaturatedSheet` directly from this branch collar, with smoothness and injectivity inherited from `branchMap`; no jointly smooth maximal-flow family is assumed. Its lower face is the regular cross-section and is explicitly retained as a finite limit, not mislabeled as escape. The separate maximal-curve development still proves `tMax(qSigma x)=ε₀` and finite endpoint escape | `ExoticCCR.TheoremFSaturatedSheet`, `ExoticCCR.TheoremFMaximalCoordinate` |
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
- The canonical Poisson brackets of the transformed polynomial generators are proved. Exponentiated Weyl relations, unconditional essential-self-adjointness failure, deficiency indices, and CP maps are **not proved**. T0.C.4 is only an abstract polynomial-algebra endomorphism.
- The transport layer constructs the canonical minimal core, proves its test-function domain dense, and proves the generic deficiency-to-not-essentially-self-adjoint bridge.
- `X1ForwardWeakDeficiencyStatement` and the legacy `TransportNecessityStatement` are definitions used as explicit hypotheses, not axioms or unconditional theorems. No nonzero vector in `Dom(H*)` at eigenvalue `±i` has been constructed.
- `ForwardSaturatedSheet` is inhabited from every `ForwardBranchOpen` by the explicit map `branchMap (x, sqrt (β x - s))` on `β x - ε₀ < s < β x`. The upper face escapes by the branch-root estimate. The lower face converges to `qSigma x`; the structure records this honest regular finite-end alternative, so a future integration-by-parts argument must handle that residual by support or an estimate. This construction uses neither a jointly smooth maximal-flow family nor an integration-by-parts or Theorem E claim.
- Full unconditional A001 Theorem E remains open in Lean. Incompleteness alone is not used to claim it. The forward-branch modules prove the local chain identity, the resulting absolute derivative-determinant ratio `1/2` in fixed `Fin 3` coordinates, the exact branch Jacobian `|τ|`, bijectivity of the branch derivative and openness of the local branch image, a mathlib Jacobian change-of-variables identity on that image, weighted parameter integrability, measurable zero-extension packaging, a nonzero ambient `L²` class represented by a suitable `uMinus`, and the pointwise characteristic identities `d(branchMap)/dτ=(-2τ)X1` and `d uMinus/ds=uMinus` inside the branch domain. They do not prove continuity of the zero extension, the global weak-adjoint identity, an adjoint deficiency witness, or deficiency indices such as `(∞,∞)`. The precise residual is now formalized: at a finite artificial boundary point outside the local image, continuity would require the Gaussian parameter density to tend to zero. No such lateral/end vanishing follows from the current `χ(a,c)` cutoff, and no maximal flow-saturated boundary has yet been constructed.

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
