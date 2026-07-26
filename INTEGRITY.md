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
13. **T0.E density and conditional bridge.** Compactly supported smooth test functions are dense
    in `L²(ℝ³)`, so the canonical minimal transport core has dense domain. Given
    `X1ForwardWeakDeficiencyStatement`, `theoremE_of_forwardWeakDeficiency` packages the supplied
    weak eigenvector into adjoint deficiency and concludes that the canonical `X1` core is not
    essentially self-adjoint. The weak-deficiency statement remains a definition/hypothesis, not
    an axiom or unconditional theorem. The legacy route through `TransportNecessityStatement` is
    likewise conditional.
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
    The positive branch domain and its image are measurable, the standard-coordinate branch
    Jacobian is exactly `|τ|`, and mathlib's Jacobian theorem gives the displayed change-of-variables
    identity for the squared norm of `uMinus` on the image. For continuous compactly supported `χ`,
    the squared norm of `deficiencyDensity` and its required `|τ|`-weighted form are integrable on
    the relevant parameter domains. A compactly supported cutoff can be chosen for which the zero
    extension `uMinus` is measurable and represents a nonzero vector in ambient `L²(ℝ³)`. Its
    pullback along a vertical parameter line inside the positive open branch has derivative
    `-2τ uMinus`. The global weak-adjoint identity and operator conclusions are not asserted.
16. **T0.F cross-section and saturation infrastructure.** Every `ForwardBranchOpen` contains a
    smooth injective positive constant-`τ` cross-section. Its offset `ε₀=τ₀²` is positive and its
    anchor value is exactly `(a, β(a,c)-ε₀, c)`. A compact transverse closed ball inside the
    cross-section admits a common positive Picard--Lindelöf lifetime and a jointly continuous
    two-sided local `X1` flow map. Joint smooth dependence is not proved.
    `ForwardSaturatedSheet` separately records the full interval-bundle, smooth injective flow
    parameterization, exact anchor evaluation, `X1` integral-curve, upper-escape, and lower-end
    conditions that would be needed before discarding endpoint terms. No inhabitant of this
    structure is asserted.

These are machine-checked polynomial identities, elementary field arithmetic, and the stated
one-dimensional real-analysis consequences. They do not constitute all of Program B.

## What this artifact does **not** assert

- Full resolution or literature status of the Jacobian conjecture beyond the finite identities proved in this tree.
- That any particular public announcement is the definitive historical priority record (see PROVENANCE.md for citations only).
- Physical significance, quantum channels, gates, continuous-variable protocols, or computational advantage.
- Analytic/operator CCR realizations or exponentiated Weyl relations beyond the proved
  polynomial generator Poisson brackets and abstract polynomial Weyl-algebra endomorphism.
- Essential self-adjointness, strong CCR/Weyl relations, C*-extension, complete positivity, or dilations.
- Unconditional A001 Theorem E. Although the canonical minimal `L²` core is constructed, its
  test-function domain is proved dense, and a nonzero `L²` branch candidate is now constructed,
  the repository does not prove that candidate lies in `Dom(H*)` or satisfies `H* u = ±i u`.
  The current local open branch has no flow-saturated boundary hypothesis that would by itself
  eliminate all integration-by-parts boundary terms. Incompleteness alone is not claimed to imply
  the operator conclusion.
- A global A001 Theorem F sheet or measure-`1/2` conclusion, a concrete `Dom(H*)`
  vector satisfying the weak deficiency identity, and all
  deficiency-index values. In particular, no `(∞,∞)` deficiency-index result is claimed.
- That the current `ForwardBranchOpen` collar extends to a jointly smooth uniform product flow
  collar or a `ForwardSaturatedSheet`. A compact transverse ball has a jointly continuous local
  flow with a common existence time, but no maximal interval, `escape_upper`,
  or `lower_ok` escape alternative is constructed. Its local `s = β-τ²` parameter domain is not
  proved to contain full flow intervals, and no theorem controls its other endpoint. Consequently
  no integration-by-parts boundary term is dropped here.
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
