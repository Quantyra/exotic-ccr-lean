# D0-family pilot — Cor 5.3 d=4 (S015)

> ## CLOSED / PARKED — no active backlog
>
> **S015 constructive pilot is closed.** Seed + d=4 pilot certification stands.
> Full-family ∀d work (independent of the preprint) may remain mathematically
> open but is **parked / non-backlog** and does **not** authorize further
> theorem or validation development. A001 is closed. Body below is the
> 2026-07-21 historical closeout record.

**Status:** CLOSED as **constructive pilot certification** (not full ∀d re-proof; full-family parked)  
**Date:** 2026-07-21  
**Depends on:** G0-seed D0 (closed)

## Claims ledger (separated)

| ID | Statement | Status |
|----|-----------|--------|
| **Seed T0.1/T0.2** | det F=-2; 3 collisions | **certified** (S011 / D0-seed) |
| **F-pilot-det** | det F_ψ=-2 for d=4 Cor 5.3 pilot | **certified pilot** (dual CAS) |
| **F-pilot-coll** | same 3 collisions for pilot | **certified pilot** |
| **F-pilot-deg** | μ=4 | **partial** (fiber poly deg 4 + preprint); not full field-degree re-proof |
| **F-C5.3 ∀d** | every d≥3 exists | **schema + preprint**; pilot d=4 only machine-checked |
| Physical / factory-false | — | **not claimed** |

## Evidence
| Artifact | Path |
|----------|------|
| Theorem extract | `docs/literature/family-theorem-extract.md` |
| Freeze | `data/anchor/F_family_d4_cor53_pilot.json` |
| CAS A | `scripts/cas/verify_family_d4_sympy.py` → `cas_family_d4_sympy_report.json` |
| CAS B | `scripts/cas/verify_family_d4_purepython.py` → `cas_family_d4_purepython_report.json` |
| Lean plan | `docs/validation/lean-plan-family-d4.md` |

## Reproduce
```text
python scripts/cas/verify_family_d4_sympy.py
python scripts/cas/verify_family_d4_purepython.py
```

## G0 status after S015
| Half | Status |
|------|--------|
| G0-seed | closed |
| G0-family pilot (d=4 constructive) | closed |
| G0-family full (∀d independent of preprint) | **parked / non-backlog** — may remain mathematically open; not an authorized task |
| Full G0 (program) | **seed + pilot closed for program purposes**; historical atlas-start note only (preprint-derived labels until Lean); no active follow-on from this dossier |

## Non-claims
No “factory false”; no Poisson/Weyl/physical language; Zenodo DOI not required for this close.
