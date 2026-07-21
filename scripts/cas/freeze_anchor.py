#!/usr/bin/env python3
"""Freeze machine-readable anchor JSON after dual CAS pass."""
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path


def norm_terms(rep):
    out = []
    for comp in rep["expanded_components"]:
        terms = sorted(
            ((tuple(t["exponents"]), t["coeff"]) for t in comp["terms"]),
            key=lambda x: x[0],
        )
        out.append(terms)
    return out


def main() -> int:
    sci = Path(__file__).resolve().parents[2]
    sym = json.loads((sci / "data/anchor/cas_sympy_report.json").read_text(encoding="utf-8"))
    pur = json.loads((sci / "data/anchor/cas_purepython_report.json").read_text(encoding="utf-8"))
    ns, np_ = norm_terms(sym), norm_terms(pur)
    match = ns == np_
    if not (match and sym["pass"] and pur["pass"]):
        print("REFUSE freeze: dual CAS mismatch or fail", file=sys.stderr)
        print("match", match, "sym", sym["pass"], "pure", pur["pass"], file=sys.stderr)
        return 1

    anchor = {
        "id": "F_announced_det_m2",
        "program": "EXOTIC-CCR",
        "gate": "G0-seed",
        "frozen_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "variables": ["x0", "x1", "x2"],
        "variable_aliases": {"x": "x0", "y": "x1", "z": "x2"},
        "formula_display": {
            "F0": "(1 + x0*x1)^3 * x2 + x1^2 * (1 + x0*x1) * (4 + 3*x0*x1)",
            "F1": "x1 + 3*x0*(1 + x0*x1)^2 * x2 + 3*x0*x1^2 * (4 + 3*x0*x1)",
            "F2": "2*x0 - 3*x0^2*x1 - x0^3*x2",
        },
        "jacobian_det_constant": "-2",
        "collision_target": ["-1/4", "0", "0"],
        "collision_inputs": [
            ["0", "0", "-1/4"],
            ["1", "-3/2", "13/2"],
            ["-1", "3/2", "13/2"],
        ],
        "components_sparse": sym["expanded_components"],
        "dual_cas": {
            "sympy_pass": True,
            "purepython_pass": True,
            "expanded_terms_identical": True,
            "reports": [
                "data/anchor/cas_sympy_report.json",
                "data/anchor/cas_purepython_report.json",
            ],
        },
        "lean": {
            "repo": "https://github.com/Quantyra/exotic-ccr-lean",
            "release": "v0.1.1",
            "module": "ExoticCCR.AnchorF",
            "theorems": [
                "ExoticCCR.jacobianDet_F",
                "ExoticCCR.evalMap_F_p0",
                "ExoticCCR.evalMap_F_p1",
                "ExoticCCR.evalMap_F_p2",
            ],
        },
        "non_claims": [
            "Does not certify family Thm 5.2 / Cor 5.3 (S015)",
            "Does not authorize physical/channel/gate/advantage language",
            "Finite exact algebraic identities only",
        ],
    }
    path = sci / "data/anchor/F_announced_det_m2.json"
    path.write_text(json.dumps(anchor, indent=2) + "\n", encoding="utf-8")
    print("wrote", path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
