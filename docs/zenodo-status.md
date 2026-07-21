# Zenodo status — exotic-ccr-lean

| Field | Value |
|-------|--------|
| Date | 2026-07-21 |
| Repo | https://github.com/Quantyra/exotic-ccr-lean |
| GitHub→Zenodo webhook | present (`release` events) |
| Last webhook ping | **403** Invalid HTTP Response (2026-07-21) |
| Concept DOI | **pending** |
| Version DOI | **pending** |
| Status | Hook enabled; deposit not yet public — re-release after auth fix if 403 persists |

## History
1. v0.1.0 published **before** Zenodo was linked — no deposit from that release alone.
2. Zenodo switched on for this repository (Chief Scientist, 2026-07-21); GitHub webhook created.
3. Initial ping returned **403** — often means Zenodo OAuth/token needs reconnect in zenodo.org → GitHub settings.
4. v0.1.1 cut to re-fire `release` event after metadata touch.

## If DOI still missing after v0.1.1
1. https://zenodo.org/account/settings/github/ — flip repo OFF/ON or "Sync now" if offered
2. Confirm Quantyra org authorization includes this repo
3. Check webhook deliveries on GitHub: Settings → Webhooks → Zenodo (expect 200, not 403)
4. Paste concept + version DOIs into `CITATION.cff` and this file when visible

Do not invent DOIs.
