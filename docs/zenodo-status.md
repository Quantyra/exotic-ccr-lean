# Zenodo status — exotic-ccr-lean

> ## Status supersession (A001 CLOSED)
>
> **A001 is final/published in the science package.** Review is **not** blocked.
> No Lean GitHub release or Lean Zenodo DOI is required for A001 closeout.
>
> | Surface | Receipt |
> |---------|---------|
> | Science GitHub release | `v0.3.9-referee-revision` @ SHA `0010354` (**published**) |
> | Science Zenodo DOI | **[10.5281/zenodo.21715479](https://doi.org/10.5281/zenodo.21715479)** (**published**) |
> | arXiv | **No arXiv id** — human endorsement only (VIPN6B) |
> | Audited Lean publication freeze | SHA **`2e40c4c`** (immutable; claims/provenance pin) |
> | Theorem / audit source | **`fbcdd034`** |
> | Lean freeze tag / Lean Zenodo DOI | **None** — intended package boundary; Lean remains untagged/unreleased as a separate deposit |
> | Current `main` | Post-freeze docs/`.gitignore` hygiene successor only; do not cite tip as freeze |
>
> Sections below marked **HISTORICAL** record the pre-closeout Lean seed / review-gate checklist. They are **superseded** for A001 operational status.

## Audited Lean freeze (current pin)

| Field | Value |
|-------|-------|
| Date (status reconciliation) | 2026-08-01 |
| Repo | https://github.com/Quantyra/exotic-ccr-lean |
| Audited Lean publication freeze | `2e40c4c` |
| Theorem / audit source | `fbcdd034` |
| Theorem-source root (historical) | `ff50f4a2a312591c2e5b26e71eb390ade9164b34` |
| Lean package metadata | `0.1.8-dev` (development only; not a release) |
| Lean freeze release version / tag | **none** (by package boundary; not review-blocked) |
| Lean freeze version DOI / Zenodo DOI | **none** (not required for A001) |
| Science release | `v0.3.9-referee-revision` @ `0010354` — **published** |
| Science Zenodo DOI | `10.5281/zenodo.21715479` — **published** |
| arXiv | none (VIPN6B endorsement only) |

The named theorem `ExoticCCR.theoremE` proves that the canonical minimal `X1`
transport core is not essentially self-adjoint. For the specific canonical
minimal operator `H_X1_min`, the chosen Hilbert-basis deficiency indices at
`+i` and `-i` equal `Cardinal.aleph0`, and Lean proves a bijective
classification of all `SelfAdjointExtension H_X1_min` witnesses by
complex-linear isometric equivalences from the `+i` to the `-i` adjoint
eigenspace. Lean also proves that at least two distinct such witnesses exist,
and unitary complex phases inject into distinct extension witnesses. Lean
proves this injection; the continuum-sized-family description additionally
uses the external classical cardinality of the complex unit circle and is not
formalized here. The algebraic `hamelDeficiencyRank` (`Module.rank`) results
remain lower bounds, not an exact Hamel-rank computation. No
arbitrary-operator theorem, preferred extension, exact cardinality of the full
extension type or inequivalence result, or full historical Theorem F package
is claimed.

## HISTORICAL — pre-closeout “proposed freeze / review blocked” checklist (superseded)

The following table and prose were the pre-publication Lean release checklist.
They incorrectly read as if A001 were still a review-blocked candidate. **Do
not use them as current operational status.** A001 science is published; Lean
review for that closeout is complete; absence of a Lean tag/DOI is a package
boundary, not a blocker.

| Field (historical) | Value at last pre-closeout draft |
|--------------------|----------------------------------|
| Date | 2026-07-28 |
| GitHub→Zenodo webhook | enabled (`release` events) |
| Historical seed releases | [v0.1.0](https://github.com/Quantyra/exotic-ccr-lean/releases/tag/v0.1.0), [v0.1.1](https://github.com/Quantyra/exotic-ccr-lean/releases/tag/v0.1.1) |
| Historical seed concept DOI | not yet public (as of that draft) |
| Historical seed version DOI | not yet public (as of that draft) |
| Theorem source root | `ff50f4a2a312591c2e5b26e71eb390ade9164b34` |
| Then-current wording | “synchronized artifact candidate” / “review blocked” — **superseded** |
| Theorem-freeze release version | none assigned |
| Theorem-freeze tag/release | none (now: package boundary, not review-blocked) |
| Theorem-freeze version DOI | none |
| Theorem-freeze Zenodo DOI | none |

The historical seed releases do not tag or archive the audited freeze
`2e40c4c` / theorem-audit `fbcdd034`.

### Historical seed webhook notes (unchanged archive)

| Event | Result |
|-------|--------|
| Initial webhook ping | **403** |
| v0.1.1 `release` / released | **403** |
| v0.1.1 `release` / created | **202 OK** |
| v0.1.1 `release` / published | **500** |

Public Zenodo search by repository title, related GitHub URL, and author returned
no matching **Lean-repo** seed records at the last poll of that draft. The
**science** package DOI `10.5281/zenodo.21715479` is the published A001 deposit.

## HISTORICAL — Lean release gate wording (superseded for A001)

Prior text required PASS from proof-adversarial, non-claims, package/metadata,
and Lean/build/audit roles plus Dan approval before any Lean tag/DOI. That gate
applied to minting a **Lean** release. It does **not** block A001 closeout:
science is already published, and no Lean release is required.

Any **future** optional Lean-only tag/DOI would still need fresh review and
explicit Dan approval. Do not invent DOIs.
