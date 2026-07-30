#!/usr/bin/env python3
"""Fail unless every publication declaration has the approved Lean axiom profile."""

from pathlib import Path
import re
import sys


EXPECTED = (
    "ExoticCCR.theoremE",
    "ExoticCCR.theoremF",
    "ExoticCCR.aleph0_le_hamelDeficiencyRank_X1",
    "ExoticCCR.hilbertDeficiencyIndex_X1_eq_aleph0",
    "ExoticCCR.theoremFVonNeumannClassification",
    "ExoticCCR.theoremFDeficiencySigmaEquiv",
    "ExoticCCR.theoremF_exists_two_distinct_selfAdjointExtensions",
    "ExoticCCR.theoremFUnitPhaseExtension",
    "ExoticCCR.theoremFUnitPhaseExtension_injective",
)
APPROVED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_publication_axioms.py AXIOM_LOG", file=sys.stderr)
        return 2
    raw = Path(sys.argv[1]).read_bytes()
    encoding = "utf-16" if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8"
    text = raw.decode(encoding)
    failed = False
    for declaration in EXPECTED:
        pattern = re.compile(
            rf"'{re.escape(declaration)}' depends on axioms:\s*\[(.*?)\]",
            re.DOTALL,
        )
        match = pattern.search(text)
        if match is None:
            print(f"missing axiom profile: {declaration}", file=sys.stderr)
            failed = True
            continue
        actual = {
            item.strip()
            for item in match.group(1).replace("\n", " ").split(",")
            if item.strip()
        }
        if actual != APPROVED:
            print(
                f"unexpected axiom profile for {declaration}: "
                f"{sorted(actual)} != {sorted(APPROVED)}",
                file=sys.stderr,
            )
            failed = True
        else:
            print(f"PASS {declaration}: {sorted(actual)}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
