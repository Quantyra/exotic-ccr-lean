# Provenance ledger — G0 seed anchor

| Timestamp (UTC) | Actor | Class | Artifact / claim | Notes |
|-----------------|-------|-------|------------------|-------|
| 2026-07-19 | L. Alpöge (announcement) | original announcement | public X post (charter ref [1]) | Not independently verified by this ledger row |
| 2026-07-20 | D. Cureton | independent formalization | github.com/deancureton/jacobian | Prior Lean; not Quantyra product |
| 2026-07-20 | D. Speyer | commentary | Secret Blogging Seminar (charter [3]) | Literature context |
| 2026-07-20 | Ulam preprint | preprint claim | ulam.ai/research/jacobian.pdf | Family theorems → S015 only |
| 2026-07-21 | Quantyra / Fredriksen | independent Lean | Quantyra/exotic-ccr-lean v0.1.0–v0.1.1 | T0.1/T0.2 proved in Lean |
| 2026-07-21 | Quantyra AI VP Research | independent CAS A | scripts/cas/verify_anchor_sympy.py | PASS |
| 2026-07-21 | Quantyra AI VP Research | independent CAS B | scripts/cas/verify_anchor_purepython.py | PASS; no SymPy |
| 2026-07-21 | Quantyra AI VP Research | freeze | data/anchor/F_announced_det_m2.json | Expanded terms A≡B |
| 2026-07-21 | Quantyra AI VP Research | dossier | docs/validation/D0-seed-validation-dossier.md | G0-seed closed |

## Classification key
- **original announcement** — external source of the map formula  
- **independent formalization** — machine-checked proof not owned as Quantyra until Quantyra repo  
- **independent CAS** — exact computer algebra with separate code path  
- **AI-assisted exploration** — used for scripting/dossier prose; identities rechecked by CAS+Lean  
- **human-verified** — Chief Scientist review when signed  

## AI disclosure
CAS scripts, freeze tooling, and this ledger were produced with AI assistance under Chief Scientist direction. All T0.1/T0.2 identities are discharged by reproducible CAS reports and Lean theorems cited in the D0-seed dossier.
