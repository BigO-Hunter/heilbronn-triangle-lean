#!/usr/bin/env python3
"""Exact comparison of the dated coefficients; this is not a scope or proof audit."""

from fractions import Fraction
import json


def main():
    coefficients = {
        "C141": Fraction(165971304277649481670619, 324956758716416046811841770291200),
        "Cstar": Fraction(4084754449786906742230661, 8009094702029267287249256448000000),
        "bottlebrushes_source_claim": Fraction(1, 2**38),
        "openai_body": Fraction(1, 2**293),
        "openai_abstract": Fraction(1, 2**310),
    }
    names = list(coefficients)
    checks = {
        f"{left}_gt_{right}": coefficients[left] > coefficients[right]
        for left, right in zip(names, names[1:])
    }
    if not all(checks.values()):
        raise RuntimeError(checks)
    result = {
        "search_as_of": "2026-10-17",
        "coefficients": {key: str(value) for key, value in coefficients.items()},
        "strict_comparisons": checks,
        "C141_minus_Cstar": str(coefficients["C141"] - coefficients["Cstar"]),
        "relative_improvement_over_Cstar": str(coefficients["C141"] / coefficients["Cstar"] - 1),
        "scope": "Exact arithmetic only; source evidence and scope are discussed in the paper and ATTRIBUTION.md.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
