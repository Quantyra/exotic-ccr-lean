# Lean plan — family pilot d=4 (not implemented this story)

> ## HISTORICAL / PARKED — not an active plan
>
> **Do not treat this file as open work.** S015 closed as dual-CAS constructive
> pilot without implementing this Lean plan. Full-family / d=4 Lean formalization
> remains outside the A001 freeze and is **parked / non-backlog**. A001 is
> closed. Body below is the 2026-07-21 historical sketch only.

## Goal (historical / parked)
Formalize Cor 5.3 pilot in `Quantyra/exotic-ccr-lean` (not authorized as current work):
1. Define `psi2`, `Q_psi`, `R_psi`, `F_psi` over a field of char ≠ 2.
2. Prove `jacobianDet F_psi = C (-2)`.
3. Prove three collision identities (reuse seed points).
4. Optional later: generic degree via function-field / polynomial degree of fiber.

## Why not in S015
- Seed Lean already covers d=3 base.
- Det proof in preprint uses chart calculus; porting cleanly needs careful `MvPolynomial` / localization or the cleared-denominator identity we checked in SymPy.
- Dual CAS pilot is sufficient for G0-family **constructive pilot** status without blocking on a large Lean development.

## Suggested modules (historical)
- `ExoticCCR/FamilyPilotD4.lean` — definitions + det + collisions
- Audit pins linking to CAS reports hashes

## Formalizable (historical note only)
Statements are fully explicit for fixed `c=1`, `j=2` only — no blocker on explicitness; still **not** an authorized backlog item.
