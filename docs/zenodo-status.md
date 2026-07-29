# Zenodo status — exotic-ccr-lean

## Proposed Theorem F classification freeze

Commit `ff50f4a2a312591c2e5b26e71eb390ade9164b34` first introduced the complete
bounded theorem source. The current synchronized artifact candidate containing
this text adds synchronized documentation, executable axiom auditing, build
provenance, and the unit-phase multiplicity corollary. The named theorem
`ExoticCCR.theoremE` proves that the canonical minimal `X1` transport core is
not essentially self-adjoint. For the specific canonical minimal operator
`H_X1_min`, the chosen Hilbert-basis deficiency indices at `+i` and `-i` equal
`Cardinal.aleph0`, and Lean proves a bijective classification of all
`SelfAdjointExtension H_X1_min` witnesses by complex-linear isometric
equivalences from the `+i` to the `-i` adjoint eigenspace. Lean also proves
that at least two distinct such witnesses exist, and unitary complex phases
inject into distinct extension witnesses. Lean proves this injection; the
continuum-sized-family description additionally uses the external classical
cardinality of the complex unit circle and is not formalized here. The
algebraic `hamelDeficiencyRank` (`Module.rank`) results remain lower bounds,
not an exact Hamel-rank computation. No
arbitrary-operator theorem, preferred extension, exact cardinality of the full extension type
or inequivalence result, or full historical Theorem F package is claimed. No
release version, release tag, version DOI, or Zenodo DOI exists for this
proposed theorem freeze. Do not create a release or DOI from this metadata
until all review roles pass and Dan approves the packet. Historical Theorem E
tag `v0.1.8-theorem-e` targets `be4f330980f15a503aa582cbadc09c36ecf2ea10`;
its reviewed theorem source anchor is
`a6bb091c05943cfcf35c405659e57df93ab8bb3d`.

| Field | Value |
|-------|-------|
| Date | 2026-07-28 |
| Repo | https://github.com/Quantyra/exotic-ccr-lean |
| GitHub→Zenodo webhook | **enabled** (`release` events) |
| Historical seed releases | [v0.1.0](https://github.com/Quantyra/exotic-ccr-lean/releases/tag/v0.1.0), [v0.1.1](https://github.com/Quantyra/exotic-ccr-lean/releases/tag/v0.1.1) |
| Historical seed concept DOI | **not yet public** |
| Historical seed version DOI | **not yet public** |
| Theorem source root | `ff50f4a2a312591c2e5b26e71eb390ade9164b34` |
| Synchronized artifact | current commit containing this status file |
| Lean package metadata | `0.1.8-dev` (development only; not a release) |
| Theorem-freeze release version | **none assigned** |
| Theorem-freeze tag/release | **none; review blocked** |
| Theorem-freeze version DOI | **none** |
| Theorem-freeze Zenodo DOI | **none** |

The historical seed releases do not tag or archive either the theorem-source
root or the current synchronized artifact candidate.

## Historical seed status

| Event | Result |
|-------|--------|
| Initial webhook ping | **403** |
| v0.1.1 `release` / released | **403** |
| v0.1.1 `release` / created | **202 OK** |
| v0.1.1 `release` / published | **500** |

Public Zenodo search by repository title, related GitHub URL, and author returned
no matching records at the last poll. The integration is enabled, but the
historical seed deposit is not confirmed published and has no public DOI.

## Release gate

Release, tag, DOI update, or public claim expansion requires PASS from the
proof-adversarial, non-claims, package/metadata, and Lean/build/audit roles,
followed by explicit Dan approval.

Do not invent DOIs.
