# INTEGRITY — Claim control

This repository contains bounded algebraic certificates for Project EXOTIC-CCR. In addition to
the Gate 0 anchor, it contains a one-dimensional real-polynomial and elementary-shear slice of
the historical B5 algebraic core.

Commit `ff50f4a2a312591c2e5b26e71eb390ade9164b34` first introduced the complete bounded theorem
source. The current synchronized artifact candidate containing this text includes that source,
the executable axiom audit, and the following current exports. The named theorem
`ExoticCCR.theoremE` proves that the canonical minimal `X1` transport core is not essentially
self-adjoint. For the specific canonical minimal operator `H_X1_min`, the chosen Hilbert-basis
deficiency indices at `+i` and `-i` equal `Cardinal.aleph0`, and all
`SelfAdjointExtension H_X1_min` witnesses are classified bijectively by complex-linear isometric
equivalences from the `+i` to the `-i` adjoint eigenspace; at least two distinct witnesses exist.
The sign involution gives an explicit isometric equivalence between those eigenspaces, and
unitary complex phases inject into distinct self-adjoint extension witnesses.
The algebraic `Module.rank` statements remain lower bounds, not an exact Hamel-rank computation.
No release version, release tag, version DOI, or Zenodo DOI exists for this proposed theorem
freeze.

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
7. **T0.B.1–4.** The polynomial adjugate formula gives `J Bᵀ = I`; the evaluated algebraic
   cotangent-lift formula has the displayed three zero-covector collisions and is not injective.
   For the canonical polynomial Poisson bracket, its transformed generators satisfy
   `{Q_i,Q_j}=0`, `{P_i,P_j}=0`, and `{Q_i,P_j}=δ_ij` when `2 ≠ 0`.
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
12. **T0.E operator infrastructure.** The canonical minimal transport core on embedded compactly
    supported smooth functions is constructed without analytic existence assumptions. For a
    densely defined partial operator, a supplied nonzero adjoint eigenvector at either `i` or
    `-i` unconditionally obstructs essential self-adjointness.
13. **T0.E density, bridge, and witness.** Compactly supported smooth test functions are dense
    in `L²(ℝ³)`, so the canonical minimal transport core has dense domain. Given
    `X1ForwardWeakDeficiencyStatement`, `theoremE_of_forwardWeakDeficiency` packages the supplied
    weak eigenvector into adjoint deficiency and concludes that the canonical `X1` core is not
    essentially self-adjoint. The maximal-sheet construction now proves
    `X1_forwardWeakDeficiency` and, at commit `a6bb091`, the unconditional named theorem
    `ExoticCCR.theoremE` for this canonical core.
    The legacy route through `TransportNecessityStatement` remains conditional.
14. **T0.F bounded local branch.** The forward-wall divided difference has a polynomial smooth
    extension. The local smooth wall germ `β(a,c)` composes with a second implicit-function
    construction to give a smooth nonzero `r+` germ through `√2`. There is an open positive
    punctured reconstruction domain accumulating at the wall base. On it the reconstruction map
    is smooth and evaluates under `F` to `(a, β(a,c)-τ², c)`; it is injective on the positive
    sheet, while its divided-root first coordinate and norm tend to infinity on approach to the
    base within that sheet.
15. **T0.F branch density and change-of-variables data (bounded claim).** The Fréchet derivative of real `evalMap F` is
    the evaluated polynomial Jacobian with determinant `-2`, and on the open branch domain the
    derivative of `F ∘ branchMap` equals the derivative of `targetMap`. The reciprocal algebraic
    factor is `1/2`, as is the proved absolute local derivative-determinant ratio in fixed coordinates.
    The positive branch domain is open, the standard-coordinate branch derivative is bijective
    with Jacobian exactly `|τ|`, and its image is therefore open (and measurable). Mathlib's
    Jacobian theorem gives the displayed change-of-variables
    identity for the squared norm of `uMinus` on the image. For continuous compactly supported `χ`,
    the squared norm of `deficiencyDensity` and its required `|τ|`-weighted form are integrable on
    the relevant parameter domains. A compactly supported cutoff can be chosen for which the zero
    extension `uMinus` is measurable and represents a nonzero vector in ambient `L²(ℝ³)`. Its
    pullback along a vertical parameter line inside the positive open branch has derivative
    `-2τ uMinus`. These branch-density declarations alone do not assert the global weak-adjoint
    identity or operator conclusion; those are separately proved by item 18 below.
16. **T0.F cross-section and saturation infrastructure.** Every `ForwardBranchOpen` contains a
    smooth injective positive constant-`τ` cross-section. Its offset `ε₀=τ₀²` is positive and its
    anchor value is exactly `(a, β(a,c)-ε₀, c)`. A compact transverse closed ball inside the
    cross-section admits a common positive Picard--Lindelöf lifetime and a jointly continuous
    two-sided local `X1` flow map. This flow map is proved to agree with the canonical selected
    maximal curves, so those curves are jointly continuous on a nonempty open product collar.
    Connected open partial trajectories and their extended-real
    forward/backward reachable-time extrema are defined, and local uniqueness glues them to a
    pointwise maximal trajectory. The selected maximal curves obey the time-translation cocycle
    identity on their domains, and through every ambient initial point they agree with one jointly
    continuous Picard flow on a common local product collar. Independently, square-root
    reparameterization of the explicit vertical branch collar inhabits `ForwardSaturatedSheet`,
    with exact anchor evaluation,
    `X1` integral curves, and upper escape. Its finite lower face converges to the regular
    cross-section and is explicitly recorded as nonescaping boundary data.
17. **T0.F finite IBP and pointwise maximal extension (bounded claim).** On finite characteristic
    intervals the exponential flow-time density has derivative equal to itself, and the
    density--test pairing satisfies FTC/IBP with both endpoint traces displayed. A separate
    `ForwardMaximalSheet` extends each transverse trajectory backward through `qSigma`, agrees
    exactly with the explicit branch on the overlap, and has only the `tMin = -∞` or finite norm
    escape alternatives at its lower end. These local ambient collars and the cocycle identity are
    the continuation infrastructure. The total maximal-flow domain is open and the selected flow
    is jointly continuous at every point in it. For the translated `ForwardMaximalSheet`, the
    variable domain is open, `Psi` is jointly continuous and injective there, and its anchor
    coordinates are exactly `(a,s,c)`. In standard anchor coordinates, the local inverse theorem
    proves strict differentiability with constant absolute Jacobian `1/2`; the image is open and
    measurable, and Mathlib's `lintegral` change-of-variables formula applies on the full variable
    domain. The corresponding zero-extension is measurable and is in ambient `L²` for continuous
    compactly supported cutoffs whose topological support is contained in the transverse open set;
    a cutoff is constructed for which the resulting `L²` vector is nonzero. Finite-interval IBP
    with both endpoint residuals is also proved directly on maximal-sheet characteristics.
18. **T0.E full weak identity (bounded claim).** Fiber-first improper IBP exhausts every fixed
    maximal-sheet fiber, treating the `tMin = -∞` and finite-escape alternatives locally and
    retaining both residuals before taking their proved limits. Indicator-based Fubini gives the
    full parameter-domain cancellation without a measurable lower-endpoint selection. Bochner
    change of variables with absolute Jacobian `1/2` transfers the test and transport pairings to
    ambient space. A constructed nonzero `L²` zero extension is a weak `-i` eigenvector, so the
    canonical minimal transport core for `X1` is not essentially self-adjoint.
19. **T0.F Hilbert indices and canonical von Neumann classification (bounded claim).** For the
    specific canonical minimal operator `H_X1_min`, the chosen Hilbert-basis deficiency indices
    at `+i` and `-i` both equal `Cardinal.aleph0`. This exact Hilbert-space dimension statement is
    distinct from the algebraic `Module.rank` results, which prove lower bounds and do not compute
    an exact Hamel rank. Lean proves a bijection between all `SelfAdjointExtension H_X1_min`
    witnesses (self-adjoint `LinearPMap`s extending `H_X1_min`) and complex-linear isometric
    equivalences from the `+i` to the `-i` adjoint eigenspace. The explicit sign involution gives
    one such equivalence. Multiplication by unitary complex phases gives an injective
    phase-parameterized family of distinct extension witnesses; in particular, at least two
    distinct witnesses exist.

These are machine-checked polynomial identities, elementary field arithmetic, the stated
real-analysis consequences, and the bounded canonical transport-operator conclusion above.
They do not constitute all of Program B.

## What this artifact does **not** assert

- Full resolution or literature status of the Jacobian conjecture beyond the finite identities proved in this tree.
- That any particular public announcement is the definitive historical priority record (see PROVENANCE.md for citations only).
- Physical significance, quantum channels, gates, continuous-variable protocols, or computational advantage.
- Analytic/operator CCR realizations or exponentiated Weyl relations beyond the proved
  polynomial generator Poisson brackets and abstract polynomial Weyl-algebra endomorphism.
- Strong CCR/Weyl relations, C*-extension, complete positivity, or dilations.
- Any implication from incompleteness alone to failure of essential self-adjointness; the proved
  operator conclusion instead uses the explicit maximal-sheet weak-deficiency construction.
- A von Neumann classification for arbitrary operators or transport realizations, a preferred
  self-adjoint extension, an exact cardinality of the full extension type, or an inequivalence
  classification. The proved multiplicity result is the injective unit-phase family for
  `H_X1_min`; no exact-cardinality theorem is asserted.
- Full Theorem F, including a global A001 Theorem F sheet or unrestricted measure-`1/2`
  conclusion. The exact chosen Hilbert-basis indices for `H_X1_min` are Lean-covered as stated
  above, but no exact algebraic/Hamel-rank value is claimed.
- A weak-deficiency conclusion for every arbitrary cutoff. The proved witness uses the constructed
  cutoff with compact support inside the transverse open set. No boundary residual is dropped.
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
- Lean source commit `ff50f4a2a312591c2e5b26e71eb390ade9164b34` is the theorem-source
  root. The current commit containing this text is the synchronized artifact candidate. Neither
  has an assigned release version, release tag, version DOI, or Zenodo DOI.
- `0.1.8-dev` is Lean package-development metadata only. It is not a release version; the paper
  package's `v0.3.9-referee-revision` candidate label is maintained in the separate paper repository.
