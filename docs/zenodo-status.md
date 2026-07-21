# Zenodo status — exotic-ccr-lean

| Field | Value |
|-------|--------|
| Date | 2026-07-21 |
| Repo | https://github.com/Quantyra/exotic-ccr-lean |
| GitHub→Zenodo webhook | **enabled** (`release` events) |
| Releases | [v0.1.0](https://github.com/Quantyra/exotic-ccr-lean/releases/tag/v0.1.0), [v0.1.1](https://github.com/Quantyra/exotic-ccr-lean/releases/tag/v0.1.1) |
| Concept DOI | **not yet public** |
| Version DOI | **not yet public** |

## Webhook delivery log (GitHub)

| Event | Result |
|-------|--------|
| Initial ping (hook create) | **403** |
| v0.1.1 `release` / released | **403** |
| v0.1.1 `release` / created | **202 OK** |
| v0.1.1 `release` / published | **500** |

Public Zenodo search (title `exotic-ccr-lean`, related GitHub URL, Fredriksen+jacobian) returned **no** matching records as of last poll.

## Interpretation
- Integration is **on** (webhook exists).
- Deposit is **not confirmed published** (mixed 403/202/500; no public DOI).
- Common next step: open https://zenodo.org/account/settings/github/ → `Quantyra/exotic-ccr-lean` → check for failed/pending deposit or **draft** needing “Publish”.
- If drafts empty, toggle the repo off/on or reconnect GitHub OAuth, then publish a new tag or use Zenodo “Get it now” / sync if shown.

## When DOI appears
1. Record **concept DOI** and **version DOI** here.
2. Set `doi:` in `CITATION.cff` to the concept DOI (Quantyra convention).
3. Optionally badge README.
4. Close planning Soft Blocker on S013.

Do not invent DOIs.
