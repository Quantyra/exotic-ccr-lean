# D0-seed — EXOTIC-CCR Gate 0 seed validation dossier

**Status:** CLOSED (seed half only)  
**Date:** 2026-07-21  
**Program:** EXOTIC-CCR  
**Planning story:** `Quantyra-Planning2/stories/S011-g0-anchor-validation-dossier.md`  
**Full G0:** still requires family certification (**S015**)

## 1. Scope
Independent exact validation and freeze of the **announced seed map** \(F\) with \(\det DF = -2\) and the three-point collision (charter App. A / Lean `ExoticCCR.F`).

**Out of scope for this dossier:** family Thm 5.2 / Cor 5.3, Poisson/Weyl lifts, physical admissibility, channels, gates, advantage claims.

## 2. Anchor object (frozen)
| Field | Value |
|-------|--------|
| Machine-readable freeze | [`data/anchor/F_announced_det_m2.json`](../../data/anchor/F_announced_det_m2.json) |
| Display form | \(F_0=(1+xy)^3 z + y^2(1+xy)(4+3xy)\), \(F_1=y+3x(1+xy)^2 z+3xy^2(4+3xy)\), \(F_2=2x-3x^2 y-x^3 z\) |
| \(\det DF\) | constant \(-2\) |
| Collision target | \((-1/4,\,0,\,0)\) |
| Collision inputs | \((0,0,-1/4)\), \((1,-3/2,13/2)\), \((-1,3/2,13/2)\) |

Variables: \((x,y,z)=(x_0,x_1,x_2)\).

## 3. Dual independent CAS (T0.1 + T0.2)

| Path | Engine | Script | Report | Result |
|------|--------|--------|--------|--------|
| A | SymPy 1.14.0 | `scripts/cas/verify_anchor_sympy.py` | `data/anchor/cas_sympy_report.json` | **PASS** |
| B | Pure Python `fractions.Fraction` (no SymPy) | `scripts/cas/verify_anchor_purepython.py` | `data/anchor/cas_purepython_report.json` | **PASS** |

Cross-check: expanded sparse term dictionaries from A and B are **identical** (enforced by `scripts/cas/freeze_anchor.py` before freeze).

Reproduce:
```text
python scripts/cas/verify_anchor_sympy.py
python scripts/cas/verify_anchor_purepython.py
python scripts/cas/freeze_anchor.py
```

## 4. Lean certificates (third independent path)
| Item | Value |
|------|--------|
| Repo | https://github.com/Quantyra/exotic-ccr-lean |
| Release | [v0.1.1](https://github.com/Quantyra/exotic-ccr-lean/releases/tag/v0.1.1) |
| Module | `ExoticCCR/AnchorF.lean` |
| T0.1 | `ExoticCCR.jacobianDet_F` — `jacobianDet F = C (-2)` |
| T0.2 | `ExoticCCR.evalMap_F_p0`, `evalMap_F_p1`, `evalMap_F_p2` |
| Packaging | `ExoticCCR.not_injective_unit_jacobian*` (non-injectivity packaging; still algebraic only) |

Lean is Quantyra’s independent reimplementation (see Lean `PROVENANCE.md`); dual CAS above does not import Lean.

## 5. Compact human derivation sketch
1. **Jacobian:** form \(J_{ij}=\partial_j F_i\) over \(\mathbb{Q}[x,y,z]\). Direct expansion (CAS-assisted, term-checked by two engines) yields \(\det J \equiv -2\). Nonzero constant ⇒ \(F\) is a Keller map (Jacobian nowhere zero).
2. **Collisions:** evaluate \(F\) at the three rational points listed above. All three map to \((-1/4,0,0)\). Distinct inputs with equal image ⇒ \(F\) is not injective ⇒ no polynomial inverse.
3. **Conclusion (seed only):** finite exact identities certify a noninjective polynomial self-map of \(\mathbb{A}^3\) with unit (constant nonzero) Jacobian determinant over characteristic \(0\) (and, with Lean packaging, broader field statements). This does **not** by itself settle literature status of all announcements or family constructions.

## 6. Claims ledger (seed)

| ID | Statement | Status | Evidence |
|----|-----------|--------|----------|
| T0.1 | \(\det DF = -2\) (constant) | **certified (seed)** | dual CAS + Lean `jacobianDet_F` |
| T0.2 | three collision identities | **certified (seed)** | dual CAS + Lean `evalMap_F_p*` |
| Family 5.2/5.3 | every \(d\ge 3\) … | **open (S015)** | not claimed here |
| Physical / CP / gate | — | **not authorized** | INTEGRITY / charter §6.3 |

## 7. Provenance
See [`docs/provenance/G0-seed-provenance-ledger.md`](../provenance/G0-seed-provenance-ledger.md).

## 8. Non-claims (binding)
- No family “factory false” claim.
- No Poisson/Weyl/physical/channel/gate/advantage language authorized by D0-seed.
- Zenodo DOI for Lean is independent Soft Blocker (do not invent DOIs).

## 9. Sign-off
| Role | Action |
|------|--------|
| VP Research (AI) | Dual CAS executed; freeze written; dossier filed 2026-07-21 |
| Chief Scientist | Review optional; G0 remains incomplete until S015 |
