#!/usr/bin/env python3
"""CAS path A: SymPy exact verification of EXOTIC-CCR seed anchor F.

T0.1: jacobian det F == -2 (constant)
T0.2: three collision identities (char 0)

Non-claims: algebraic identities only; not family theorems; not physical claims.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import sympy as sp

x, y, z = sp.symbols("x y z")


def F_components():
    """Announced map F (charter / Lean ExoticCCR.F). Variables (x,y,z) = (X0,X1,X2)."""
    u = 1 + x * y
    f1 = u**3 * z + y**2 * u * (4 + 3 * x * y)
    f2 = y + 3 * x * u**2 * z + 3 * x * y**2 * (4 + 3 * x * y)
    f3 = 2 * x - 3 * x**2 * y - x**3 * z
    return sp.Matrix([f1, f2, f3])


def main() -> int:
    F = F_components()
    vars_ = (x, y, z)
    J = F.jacobian(vars_)
    det = sp.simplify(J.det())
    det_ok = det == -2

    pts = [
        (sp.Integer(0), sp.Integer(0), sp.Rational(-1, 4)),
        (sp.Integer(1), sp.Rational(-3, 2), sp.Rational(13, 2)),
        (sp.Integer(-1), sp.Rational(3, 2), sp.Rational(13, 2)),
    ]
    target = sp.Matrix([sp.Rational(-1, 4), 0, 0])
    collisions = []
    all_coll = True
    for p in pts:
        val = sp.simplify(F.subs({x: p[0], y: p[1], z: p[2]}))
        ok = val == target
        all_coll = all_coll and ok
        collisions.append(
            {
                "input": [str(p[0]), str(p[1]), str(p[2])],
                "output": [str(val[0]), str(val[1]), str(val[2])],
                "equals_target": bool(ok),
            }
        )

    # Expanded monomial support for freeze (dictionary form)
    expanded = []
    for i, comp in enumerate(F):
        poly = sp.Poly(sp.expand(comp), x, y, z)
        terms = []
        for monom, coeff in poly.terms():
            terms.append({"exponents": list(monom), "coeff": str(coeff)})
        expanded.append({"component": i, "terms": terms})

    report = {
        "engine": "sympy",
        "sympy_version": sp.__version__,
        "map": "F_announced_det_m2",
        "T0_1_jacobian_det": {"value": str(det), "equals_minus_two": bool(det_ok)},
        "T0_2_collisions": collisions,
        "T0_2_all_pass": bool(all_coll),
        "pass": bool(det_ok and all_coll),
        "expanded_components": expanded,
    }

    out_dir = Path(__file__).resolve().parents[2] / "data" / "anchor"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "cas_sympy_report.json"
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    # Human-readable summary line
    print(f"sympy_version={sp.__version__}")
    print(f"det={det} det_ok={det_ok}")
    for c in collisions:
        print(f"collision {c['input']} -> {c['output']} ok={c['equals_target']}")
    print(f"PASS={report['pass']}")
    print(f"wrote {out_path}")
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
