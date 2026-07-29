# exotic-ccr-lean

Lean 4 algebraic certificates for the **EXOTIC-CCR** program (Quantyra).

This repository formalizes finite exact algebraic identities used as the frozen anchor object for Project EXOTIC-CCR (Exotic Endomorphisms of the Canonical Commutation Relations): Jacobian determinant certificates and three-point collision witnesses for an explicit polynomial map \(F\colon K^3\to K^3\), plus standard non-injectivity packaging.

**Organization:** Quantyra Inc.  
**Program:** EXOTIC-CCR research charter (Gate G0 / WP0)  
**License:** Apache-2.0  
**Theorem E freeze:** commit `a6bb091c05943cfcf35c405659e57df93ab8bb3d` (untagged, unreleased, and without an assigned release version)

**Theorem F source root:** commit `ff50f4a2a312591c2e5b26e71eb390ade9164b34` first introduced the complete bounded classification source.

**Synchronized artifact candidate:** the current commit containing this text includes those theorem sources, synchronized documentation, the unit-phase multiplicity corollary, the executable publication axiom audit, and build provenance. It is untagged, unreleased, and has no assigned release version.

Version streams are intentionally separate: `0.1.8-dev` in `lakefile.toml` is
only Lean package-development metadata; it is not a GitHub release or Zenodo
version. The paper package's `v0.3.9-referee-revision` candidate label belongs to the
separate paper repository. No Lean release tag has been assigned.

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
| T0.E | A maximal forward sheet supplies a nonzero ambient `L²` weak `-i` eigenvector, and `ExoticCCR.theoremE` proves that the canonical minimal `X1` transport core is not essentially self-adjoint | `ExoticCCR.TheoremEForwardIBP` |
| T0.E-conditional | For any supplied `MinimalTransportRealization X1`, `theoremE_of_transportNecessity` derives failure of essential self-adjointness from the explicit hypothesis `TransportNecessityStatement` | `ExoticCCR.TheoremE` |
| T0.F-wall-base | The forward-wall cubic vanishes at `(a,s,c) = (0,1/2,2)`, while its formal `s`-derivative expression equals `-1/2` there | `ExoticCCR.TheoremFForwardWall` |
| T0.F-wall-reconstruction | A root of the displayed wall cubic reconstructs an explicit preimage of `(a,s,c)` under `F` whenever the reconstruction denominators are nonzero | `ExoticCCR.TheoremFForwardWall` |
| T0.F-forward-branch | The polynomial divided-difference extension has a smooth local varying-`β` `r+` germ at `√2`. It admits an open positive punctured reconstruction domain accumulating at the wall base; the branch map is smooth there, evaluates under `F` to `(a, β(a,c)-τ², c)`, is injective on its positive sheet, and its first coordinate and norm tend to infinity at the base within that sheet | `ExoticCCR.TheoremFForwardBranch` |
| T0.F-branch-density-data | The Fréchet derivative of real `evalMap F` is the evaluated polynomial Jacobian with determinant `-2`; on the open branch domain its chain derivative equals the target-map derivative. The reciprocal factor is `1/2`. The positive parameter domain is open, the standard-coordinate branch derivative is bijective with Jacobian `|τ|`, and consequently the branch image is open (and measurable). Mathlib's Jacobian change-of-variables formula is applied to the squared norm of `uMinus` on the image. For continuous compactly supported `χ`, the Gaussian candidate density and its `|τ|`-weighted square are integrable on the relevant parameter domains; a compactly supported cutoff can be chosen so that the measurable zero extension `uMinus` determines a nonzero vector of ambient `L²(ℝ³)`. Locally, `d(branchMap)/dτ=(-2τ)X1`, and reparameterization by the target coordinate `s=β-τ²` gives the pointwise characteristic identity `d uMinus/ds=uMinus`. A separate theorem records the exact unresolved finite-boundary condition: continuity of the zero extension at an artificial branch boundary would force the parameter density to tend to zero there | `ExoticCCR.TheoremFJacobianFDeriv`, `ExoticCCR.TheoremFBranchDensity` |
| T0.F-saturation-infrastructure | Every `ForwardBranchOpen` records the positive half-ball present in its construction. Shrinking it gives a nonempty open transverse set with full vertical segments and fixed-parameter wall escape. Square-root reparameterization by the anchor `s` coordinate produces an inhabited `ForwardSaturatedSheet` directly from this branch collar, with smoothness and injectivity inherited from `branchMap`. Its lower face is the regular cross-section and is explicitly retained as a finite limit, not mislabeled as escape. Picard--Lindelöf agrees with the canonical selected maximal curves on a common local collar through every ambient initial point; the total maximal-flow domain is open, and the selected flow is jointly continuous at every point of that domain (hence on every compact `K × Icc a b` lying fiberwise in it). The separate maximal-curve development still proves `tMax(qSigma x)=ε₀` and finite endpoint escape | `ExoticCCR.TheoremFSaturatedSheet`, `ExoticCCR.TheoremFMaximalCoordinate` |
| T0.F-forward-IBP | On finite maximal-sheet intervals, FTC/IBP retains both endpoint traces. Pointwise maximal extension leaves only `-∞` or finite escape at the lower end. Fiber exhaustion proves improper IBP without a globally selected lower endpoint; full-domain indicator Fubini then proves the parameter-space cancellation. The standard-coordinate sheet has constant absolute Jacobian `1/2`, and Bochner change of variables transfers both exact weak pairings to ambient space. For a suitable compactly supported cutoff, the measurable nonzero `L²` zero extension satisfies the representative weak `-i` identity | `ExoticCCR.TheoremEForwardIBP`, `ExoticCCR.TheoremFMaximalSheet`, `ExoticCCR.TheoremFMaximalSheetDensity` |
| T0.F-Hilbert-index | For the specific canonical minimal operator `H_X1_min`, the chosen Hilbert-basis deficiency indices at `+i` and `-i` both equal `Cardinal.aleph0`. This is an exact Hilbert-space dimension statement; the algebraic `Module.rank` results remain lower bounds, not an exact Hamel-rank computation | `ExoticCCR.TheoremFHilbertIndex` |
| T0.F-von-Neumann | For the specific canonical minimal operator `H_X1_min`, all `SelfAdjointExtension H_X1_min` witnesses are classified bijectively by complex-linear isometric equivalences from the `+i` to the `-i` adjoint eigenspace. The sign involution supplies an explicit such equivalence. Unit complex phases inject into distinct extension witnesses; in particular, at least two distinct witnesses exist | `ExoticCCR.TheoremFVonNeumannClassification`, `ExoticCCR.TheoremFExtensionMultiplicity` |
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

- These are bounded algebraic, real-analytic, and canonical transport-operator certificates.
- This repo does **not** claim full status of the Jacobian conjecture literature beyond the identities proved here.
- This repo does **not** claim physical, channel, gate, computational-advantage, or broader operator-algebraic results beyond the canonical `X1` conclusion stated above.
- The canonical Poisson brackets of the transformed polynomial generators are proved. Exponentiated Weyl relations, the full historical Theorem F package, and CP maps are **not proved in Lean**. For `H_X1_min`, the chosen Hilbert-basis deficiency indices at `±i` are exactly `Cardinal.aleph0`; the separate algebraic `Module.rank` statements are only lower bounds and do not compute an exact Hamel rank. T0.C.4 is only an abstract polynomial-algebra endomorphism.
- The transport layer constructs the canonical minimal core, proves its test-function domain dense, and proves the generic deficiency-to-not-essentially-self-adjoint bridge.
- `X1ForwardWeakDeficiencyStatement` remains the proposition packaged by the now-proved theorem `X1_forwardWeakDeficiency`; the legacy `TransportNecessityStatement` remains only a definition used by a separate conditional route.
- `ForwardSaturatedSheet` is inhabited from every `ForwardBranchOpen` by the explicit map `branchMap (x, sqrt (β x - s))` on `β x - ε₀ < s < β x`. Its upper face escapes and its lower face converges to `qSigma x`. Finite-interval IBP is proved with both traces retained, including directly on the maximal extension. A separate maximal extension agrees at `qSigma` and has only `-∞`/escape lower ends. Its translated total domain is open, and the translated map is jointly continuous, injective, and an exact right inverse of `F` in `(a,s,c)` coordinates. Its standard-coordinate Jacobian is `1/2`, its image is open and measurable, and change of variables is proved. For cutoffs compactly supported inside the transverse open set, the maximal zero extension is measurable and in `L²`; one such cutoff gives a nonzero `L²` class.
- Commit `ff50f4a2a312591c2e5b26e71eb390ade9164b34` introduced the complete bounded classification source. The current synchronized artifact additionally exports `theoremFDeficiencySigmaEquiv`, the explicit sign-involution isometric equivalence between the `+i` and `-i` eigenspaces, and the injective family `theoremFUnitPhaseExtension` parameterized by `unitary ℂ`. This does **not** select a preferred extension, identify the exact cardinality or inequivalence classes of all extensions, or prove a corresponding theorem for arbitrary operators or transport realizations.

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

## Lean freeze status

The untagged theorem freeze records the exact Lean declaration
`ExoticCCR.theoremE` at commit `a6bb091`: the canonical minimal `X1` transport
core is not essentially self-adjoint. This is a bounded canonical-core result.
No release version, release tag, version DOI, or Zenodo DOI exists for this new
theorem freeze.

Commit `ff50f4a2a312591c2e5b26e71eb390ade9164b34` is the theorem-source root,
not the final documentation freeze. The current commit containing this text
is the self-contained synchronized artifact candidate: it includes the same
bounded canonical `H_X1_min` classification, the sign-involution equivalence,
the injective unit-phase extension family, the audit source, and build
provenance. It does not freeze the full historical Theorem F package, an exact
Hamel rank, an exact cardinality of the full extension type, or any physical
or operator-algebraic consequence.

## Citation

See [CITATION.cff](CITATION.cff). The source root
`ff50f4a2a312591c2e5b26e71eb390ade9164b34` and the current synchronized
artifact candidate have no release tag, version DOI, or Zenodo DOI (see
[docs/zenodo-status.md](docs/zenodo-status.md)).

## License

Copyright 2026 Quantyra / Daniel Eric Fredriksen. Apache-2.0. See [LICENSE](LICENSE).
