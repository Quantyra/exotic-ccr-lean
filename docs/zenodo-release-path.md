# Zenodo release path (exotic-ccr-lean)

## Goal

Mint a concept DOI and version DOI for `Quantyra/exotic-ccr-lean` via Zenodo’s GitHub integration, using `.zenodo.json` metadata and GitHub Releases.

## Prerequisites

1. Quantyra org (or a maintainer account with admin on this repo) linked at [zenodo.org](https://zenodo.org) → GitHub → enable repository `Quantyra/exotic-ccr-lean`.
2. Public repo, Apache-2.0 `LICENSE`, valid `.zenodo.json`, and `CITATION.cff`.
3. Green `lake build` on the tagged commit.

## Steps

1. Confirm GitHub release `v0.1.0` exists and points at a green build commit.
2. On Zenodo: log in → GitHub settings → flip **ON** for `Quantyra/exotic-ccr-lean` (org admin may need to grant Zenodo the GitHub app).
3. Optionally re-publish the release (or push a new tag) so Zenodo receives the `release` webhook.
4. Copy concept DOI and version DOI into:
   - `CITATION.cff` (`doi:` field)
   - `docs/zenodo-status.md`
   - README citation blurb
5. Do **not** invent DOIs. Leave DOI fields empty until Zenodo assigns them.

## Metadata checklist

- [x] `.zenodo.json` — software, Apache-2.0, keywords, HTML description with non-claims
- [x] `CITATION.cff` — authors, title, version, no fake DOI
- [x] `INTEGRITY.md` / non-claims in description
- [x] `LICENSE` Apache-2.0
- [ ] Zenodo GitHub hook enabled (human/org step)
- [ ] Concept + version DOI recorded

## Soft blocker

If the hook is not enabled after the first GitHub release, record status in `docs/zenodo-status.md` and stop. No manual fake deposit is required for Gate 0 closeout.
