# Theorem F synchronized artifact provenance

This record belongs to the untagged, unreleased synchronized artifact
candidate. Commit
`ff50f4a2a312591c2e5b26e71eb390ade9164b34` is the earlier theorem-source
root, not the final documentation/build freeze.

## Resolved environment

- Verification date: 2026-07-29
- Platform: Windows x86_64
- Lean: `4.33.0-rc1`
- Lean commit: `62eed1db4d67327ec8120be05f1a1b0847d74561`
- mathlib input revision: `v4.33.0-rc1`
- resolved mathlib commit: `79d0395a1825a6264ad5d269e35e60537518955e`
- Lean package-development metadata: `0.1.8-dev`
- Historical Theorem E release: tag `v0.1.8-theorem-e` targets
  `be4f330980f15a503aa582cbadc09c36ecf2ea10`; reviewed theorem source anchor
  `a6bb091c05943cfcf35c405659e57df93ab8bb3d`
- Proposed Theorem F release/tag/DOI status: none assigned or created

## Reproducibility checks

The following commands completed successfully against the source and build
configuration at commit
`fbcdd0345d2f2540cd537204be2178ae07e18a5e`:

```text
lake build ExoticCCR.TheoremFPlusITransport
lake build ExoticCCR.TheoremFExtensionMultiplicity
lake build
lake env lean -D maxSynthPendingDepth=3 -D weak.linter.mathlibStandardSet=true -D relaxedAutoImplicit=false -D pp.unicode.fun=true ExoticCCR/PublicationAxiomAudit.lean
python scripts/check_publication_axioms.py publication-axioms.log
```

Observed results:

- targeted adjoint-eigenspace/sign-transport build: PASS, 8,684 jobs;
- targeted unit-phase multiplicity build: PASS, 8,692 jobs;
- full library build: PASS, 8,702 jobs;
- publication axiom audit: PASS for every declaration listed below;
- executable forbidden-marker scan over tracked Lean sources found no
  `sorry`, `admit`, custom `axiom`, `unsafe`, or `opaque` declaration.

CI is configured to run strict cache retrieval, the full build, Lean axiom
audit, and profile checker, and to upload the cache, build, and axiom logs as
an artifact named with the exact GitHub commit SHA. Commit
`fbcdd0345d2f2540cd537204be2178ae07e18a5e` was pushed to canonical
`origin/main`, and its exact-commit CI run completed successfully:
<https://github.com/Quantyra/exotic-ccr-lean/actions/runs/30514432433>.
That run uploaded artifact ID `8748395923`, named
`lean-publication-provenance-fbcdd0345d2f2540cd537204be2178ae07e18a5e`.

The push and CI status of the commit containing this prose is intentionally
not asserted inside its own tree. Determine that status from Git remote
topology and the repository's GitHub Actions history. The synchronized
artifact candidate remains untagged and unreleased; no release version or DOI
is assigned here.

## Publication axiom profiles

Each audited declaration depends exactly on:

```text
[propext, Classical.choice, Quot.sound]
```

Audited declarations:

- `ExoticCCR.theoremE`
- `ExoticCCR.theoremF`
- `ExoticCCR.aleph0_le_hamelDeficiencyRank_X1`
- `ExoticCCR.hilbertDeficiencyIndex_X1_eq_aleph0`
- `ExoticCCR.theoremFVonNeumannClassification`
- `ExoticCCR.theoremFDeficiencySigmaEquiv`
- `ExoticCCR.theoremF_exists_two_distinct_selfAdjointExtensions`
- `ExoticCCR.theoremFUnitPhaseExtension`
- `ExoticCCR.theoremFUnitPhaseExtension_injective`

## Bounded multiplicity and cutoff coverage

`theoremFDeficiencySigmaEquiv` is the stable, explicit complex-linear
isometric equivalence induced by the measure-preserving sign involution from
the `+i` adjoint eigenspace to the `-i` adjoint eigenspace.

`theoremFUnitPhaseExtension` and
`theoremFUnitPhaseExtension_injective` prove that unitary complex phases
parameterize distinct `SelfAdjointExtension H_X1_min` witnesses. This artifact
does not formalize the classical fact that the complex unit circle has
continuum cardinality. Thus Lean proves the injection, while the
continuum-sized lower-family wording is an external classical corollary. This
artifact does not identify the exact cardinality of the full extension type.

No uniform-collar norm lower-bound theorem is asserted. The present cutoff API
takes a raw continuous function together with support hypotheses; it is not a
bundled normed cutoff space or a linear map into `L²`. Existing Lean proves
nonzeroness using positivity after change of variables. A quantitative
lower-bound export would require additional Tonelli/change-of-variables work,
an explicit `L²` cutoff norm identity, and a bundled cutoff-to-deficiency map.
That expansion was not introduced into this bounded freeze.
