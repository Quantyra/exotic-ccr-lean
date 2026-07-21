# PROVENANCE

## Quantyra status

This repository is a **Quantyra independent reimplementation** of Gate-0 algebraic certificates for the EXOTIC-CCR Jacobian counterexample anchor. It is **not** a git fork of third-party repositories. Lean modules, naming (`ExoticCCR`), metadata, license packaging, and claim-control documents are Quantyra work product.

## Primary sources (charter references [1]–[3])

These sources document the announced map and early public formalization. They are cited for **provenance and current context**, not as substitutes for Quantyra’s independent Gate 0 validation, and **are not claimed as Quantyra work**.

1. **L. Alpöge**, announcement of an explicit three-variable Jacobian counterexample, X post, 19 July 2026, status `2079028340955197566`.
2. **D. Cureton**, “Levent Alpöge/Fable 5's counterexample to the Jacobian conjecture in Lean 4,” public repository [`deancureton/jacobian`](https://github.com/deancureton/jacobian), accessed 20 July 2026. Used as a **structure and formula reference only** (module layout, det/collision lemmas, packaging shape). Reimplemented cleanly under `ExoticCCR` without forking git history.
3. **D. Speyer**, “The new counterexample to the Jacobian conjecture,” Secret Blogging Seminar, 20 July 2026.

## Mathematical object

Announced real-coefficient polynomial map \(F\colon K^3\to K^3\) with constant Jacobian determinant \(-2\) and an explicit three-point collision. A determinant-one normalization \(G\) is maintained alongside \(F\) (charter §1.1; Cureton det-1 packaging).

Formulas match the EXOTIC-CCR Research Charter v1.0 (Quantyra planning lane) and the identities listed in `README.md`.

## Related classical background (not Gate-0 claims)

Charter references [4]–[6] (Belov-Kanel–Kontsevich; Adjamagbo–van den Essen; Tsuchimoto) connect Jacobian / Dixmier / Poisson / Weyl themes. This repository does **not** formalize those equivalences.

## Integrity

See [INTEGRITY.md](INTEGRITY.md). Gate G0 asserts only the finite algebraic certificates proved in Lean.
