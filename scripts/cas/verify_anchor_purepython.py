#!/usr/bin/env python3
"""CAS path B: pure-Python exact rationals (no SymPy) for EXOTIC-CCR seed anchor F.

Independent code path from scripts/cas/verify_anchor_sympy.py.
Polynomial ring Q[x,y,z] via dense exponent dicts; Jacobian by formal differentiation.

Non-claims: algebraic identities only.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple

# Monomial = (ex, ey, ez); Poly = dict monomial -> Fraction
Mono = Tuple[int, int, int]
Poly = Dict[Mono, Fraction]

ZERO: Poly = {}


def c(n: int | Fraction) -> Poly:
    if isinstance(n, int):
        n = Fraction(n)
    if n == 0:
        return {}
    return {(0, 0, 0): Fraction(n)}


def X(i: int) -> Poly:
    e = [0, 0, 0]
    e[i] = 1
    return {tuple(e): Fraction(1)}


def add(a: Poly, b: Poly) -> Poly:
    out: Poly = dict(a)
    for m, co in b.items():
        out[m] = out.get(m, Fraction(0)) + co
        if out[m] == 0:
            del out[m]
    return out


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, mul(c(-1), b))


def mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
            out[m] = out.get(m, Fraction(0)) + c1 * c2
            if out[m] == 0:
                del out[m]
    return out


def pow_p(a: Poly, n: int) -> Poly:
    out = c(1)
    for _ in range(n):
        out = mul(out, a)
    return out


def diff(p: Poly, var: int) -> Poly:
    out: Poly = {}
    for m, co in p.items():
        e = m[var]
        if e == 0:
            continue
        nm = list(m)
        nm[var] = e - 1
        out[tuple(nm)] = out.get(tuple(nm), Fraction(0)) + co * e
        if out[tuple(nm)] == 0:
            del out[tuple(nm)]
    return out


def eval_p(p: Poly, vals: Tuple[Fraction, Fraction, Fraction]) -> Fraction:
    s = Fraction(0)
    for m, co in p.items():
        term = co
        for i in range(3):
            term *= vals[i] ** m[i]
        s += term
    return s


def is_const(p: Poly, value: Fraction) -> bool:
    if not p:
        return value == 0
    if set(p.keys()) != {(0, 0, 0)}:
        # allow other zeros already stripped; any non-constant monomial fails
        return False
    return p[(0, 0, 0)] == value


def det3(M):
    """M is 3x3 list of Poly; return Poly det."""
    a, b, c_ = M[0]
    d, e, f = M[1]
    g, h, i = M[2]
    # a(ei-fh) - b(di-fg) + c(dh-eg)
    t1 = mul(a, sub(mul(e, i), mul(f, h)))
    t2 = mul(b, sub(mul(d, i), mul(f, g)))
    t3 = mul(c_, sub(mul(d, h), mul(e, g)))
    return add(sub(t1, t2), t3)


def F_components() -> Tuple[Poly, Poly, Poly]:
    x, y, z = X(0), X(1), X(2)
    u = add(c(1), mul(x, y))
    f1 = add(mul(pow_p(u, 3), z), mul(mul(pow_p(y, 2), u), add(c(4), mul(c(3), mul(x, y)))))
    f2 = add(
        y,
        add(
            mul(mul(mul(c(3), x), pow_p(u, 2)), z),
            mul(mul(mul(c(3), x), pow_p(y, 2)), add(c(4), mul(c(3), mul(x, y)))),
        ),
    )
    f3 = sub(sub(mul(c(2), x), mul(mul(c(3), pow_p(x, 2)), y)), mul(pow_p(x, 3), z))
    return f1, f2, f3


def poly_to_terms(p: Poly):
    terms = []
    for m in sorted(p.keys()):
        terms.append({"exponents": list(m), "coeff": str(p[m])})
    return terms


def main() -> int:
    f1, f2, f3 = F_components()
    F = [f1, f2, f3]
    J = [[diff(F[i], j) for j in range(3)] for i in range(3)]
    det = det3(J)
    det_ok = is_const(det, Fraction(-2))

    pts = [
        (Fraction(0), Fraction(0), Fraction(-1, 4)),
        (Fraction(1), Fraction(-3, 2), Fraction(13, 2)),
        (Fraction(-1), Fraction(3, 2), Fraction(13, 2)),
    ]
    target = (Fraction(-1, 4), Fraction(0), Fraction(0))
    collisions = []
    all_coll = True
    for p in pts:
        out = tuple(eval_p(F[i], p) for i in range(3))
        ok = out == target
        all_coll = all_coll and ok
        collisions.append(
            {
                "input": [str(v) for v in p],
                "output": [str(v) for v in out],
                "equals_target": bool(ok),
            }
        )

    report = {
        "engine": "purepython_fractions",
        "python": sys.version.split()[0],
        "map": "F_announced_det_m2",
        "T0_1_jacobian_det": {
            "is_constant_minus_two": bool(det_ok),
            "det_terms": poly_to_terms(det),
        },
        "T0_2_collisions": collisions,
        "T0_2_all_pass": bool(all_coll),
        "pass": bool(det_ok and all_coll),
        "expanded_components": [
            {"component": i, "terms": poly_to_terms(F[i])} for i in range(3)
        ],
    }

    out_dir = Path(__file__).resolve().parents[2] / "data" / "anchor"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "cas_purepython_report.json"
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(f"engine=purepython python={report['python']}")
    print(f"det_ok={det_ok} det_terms={report['T0_1_jacobian_det']['det_terms']}")
    for c_ in collisions:
        print(f"collision {c_['input']} -> {c_['output']} ok={c_['equals_target']}")
    print(f"PASS={report['pass']}")
    print(f"wrote {out_path}")
    return 0 if report["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
