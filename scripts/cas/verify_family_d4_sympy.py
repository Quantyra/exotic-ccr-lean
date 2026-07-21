#!/usr/bin/env python3
"""CAS path A: SymPy chain-rule + collision check for Cor 5.3 pilot d=4.

Full expanded Jac is too large; det identity follows Thm 5.2 proof chart.
Random exact Jac samples are in verify_family_d4_purepython.py (dual numbers).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import sympy as sp

x, y, z = sp.symbols("x y z")
c = sp.Integer(1)


def pieces():
    A = 1 + x * y
    B = A**2 * z + y**2 * (4 + 3 * x * y)
    P = A * B
    Q = y + 3 * x * B
    R = 2 * x - 3 * x**2 * y - x**3 * z
    psi2 = c * (4 * P + 1)
    Qp = Q + A**2 * (x**2) * (B**4) * psi2
    Rp = R - sp.Rational(1, 2) * (x**4) * (B**4) * psi2
    return A, B, P, Q, R, psi2, Qp, Rp


def main() -> int:
    A, B, P, Q, R, psi2, Qp, Rp = pieces()
    F = sp.Matrix([P, Qp, Rp])

    pts = [
        (sp.Integer(0), sp.Integer(0), sp.Rational(-1, 4)),
        (sp.Integer(1), sp.Rational(-3, 2), sp.Rational(13, 2)),
        (sp.Integer(-1), sp.Rational(3, 2), sp.Rational(13, 2)),
    ]
    target = (sp.Rational(-1, 4), sp.Integer(0), sp.Integer(0))
    collisions = []
    all_coll = True
    for pt in pts:
        sub = {x: pt[0], y: pt[1], z: pt[2]}
        Pv = sp.simplify(P.subs(sub))
        ps = sp.simplify(psi2.subs(sub))
        out = tuple(sp.simplify(F[i].subs(sub)) for i in range(3))
        ok = out == target and ps == 0 and Pv == sp.Rational(-1, 4)
        all_coll = all_coll and ok
        collisions.append(
            {
                "input": [str(v) for v in pt],
                "P": str(Pv),
                "psi2_P": str(ps),
                "output": [str(v) for v in out],
                "ok": bool(ok),
            }
        )

    s_expr = sp.together(x / A)
    psiP = c * (4 * P + 1)
    Ip = 3 * P * s_expr + (P**4) * psiP * (s_expr**2)
    Im = P * (s_expr**3) + sp.Rational(1, 2) * (P**4) * psiP * (s_expr**4)

    numQ, _ = sp.fraction(sp.together(Qp - y - Ip))
    numR, _ = sp.fraction(sp.together(Rp - (2 * s_expr - y * s_expr**2 - Im)))
    pullback_Q_ok = sp.expand(numQ) == 0
    pullback_R_ok = sp.expand(numR) == 0

    # det d(P,y,s)/d(x,y,z) with s=x/A
    Py = sp.Matrix([P, y, s_expr])
    J_pys = sp.Matrix(3, 3, lambda i, j: sp.diff(Py[i], [x, y, z][j]))
    det_pys = sp.together(J_pys.det())
    num_pys, _ = sp.fraction(sp.together(det_pys + A))
    det_pys_ok = sp.expand(num_pys) == 0

    Pv, yv, sv = sp.symbols("Pv yv sv")
    psi_pv = c * (4 * Pv + 1)
    Ip_v = 3 * Pv * sv + (Pv**4) * psi_pv * sv**2
    Im_v = Pv * sv**3 + sp.Rational(1, 2) * (Pv**4) * psi_pv * sv**4
    Qpv = yv + Ip_v
    Rpv = 2 * sv - yv * sv**2 - Im_v
    M = sp.Matrix(
        [
            [1, 0, 0],
            [sp.diff(Qpv, Pv), sp.diff(Qpv, yv), sp.diff(Qpv, sv)],
            [sp.diff(Rpv, Pv), sp.diff(Rpv, yv), sp.diff(Rpv, sv)],
        ]
    )
    det_chart_ok = sp.simplify(M.det() - 2 * (1 - yv * sv)) == 0
    chain_ok = pullback_Q_ok and pullback_R_ok and det_pys_ok and det_chart_ok

    p_, q_, r_, ss = sp.symbols("p q r ss")
    Phi = (
        2 * p_ * ss**3
        - q_ * ss**2
        + 2 * ss
        - r_
        + sp.Rational(1, 2) * p_**4 * c * (4 * p_ + 1) * ss**4
    )
    Phi_poly = sp.Poly(sp.expand(Phi), ss)
    fiber_ok = Phi_poly.degree() == 4 and Phi_poly.LC() != 0

    report = {
        "engine": "sympy",
        "sympy_version": sp.__version__,
        "pilot": "Cor5.3_d4_psi2_c1",
        "d_claimed": 4,
        "collisions": collisions,
        "collisions_all_pass": bool(all_coll),
        "chain_rule": {
            "pullback_Q_ok": bool(pullback_Q_ok),
            "pullback_R_ok": bool(pullback_R_ok),
            "det_pys_ok": bool(det_pys_ok),
            "det_chart_ok": bool(det_chart_ok),
            "chain_ok": bool(chain_ok),
            "note": "det Jac F = -2 on A!=0 by chart product; extends by polynomial identity (Thm 5.2)",
        },
        "fiber": {
            "degree": int(Phi_poly.degree()),
            "lead": str(Phi_poly.LC()),
            "ok": bool(fiber_ok),
        },
        "pass_pilot_algebraic": bool(all_coll and chain_ok and fiber_ok),
    }

    out = (
        Path(__file__).resolve().parents[2]
        / "data"
        / "anchor"
        / "cas_family_d4_sympy_report.json"
    )
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("collisions", all_coll)
    print("chain", report["chain_rule"])
    print("fiber", report["fiber"])
    print("PASS", report["pass_pilot_algebraic"])
    print("wrote", out)
    return 0 if report["pass_pilot_algebraic"] else 1


if __name__ == "__main__":
    sys.exit(main())
