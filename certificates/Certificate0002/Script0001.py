#!/usr/bin/env python3
"""Render or replay the exact two-stage eight-tent certificate artifact."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from fractions import Fraction
from pathlib import Path
from typing import Any

import jsonschema

import Script0002 as part_a
import Script0003 as part_b


ROOT = Path(__file__).resolve().parent
ARTIFACT = ROOT / "Data0001.json"
SCHEMA = ROOT / "Schema0001.json"
SOURCES = (
    ROOT / "Script0002.py",
    ROOT / "Script0003.py",
    ROOT / "Script0001.py",
    SCHEMA,
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rational(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def rational_row(values: tuple[Any, ...] | list[Any]) -> list[Any]:
    return [rational(value) if isinstance(value, Fraction) else value for value in values]


def build_candidate() -> dict[str, Any]:
    maxima, global_max = part_a.verify_center_cover()
    (
        original_error,
        derivative_rows,
        triple_error,
        _triple_rows,
        triple_center_lo,
        triple_center_hi,
        triple_exact_lo,
    ) = part_a.verify_tent_error_and_doubled_rule_witness()

    derivative_error, _, _, _ = part_a.tent_error_bound(2)
    q_witness = Fraction(1, 362)
    derivative_center_lo, derivative_center_hi = part_a.center_sum_interval(
        q_witness, q_witness, quadratic_multiplier=2
    )
    derivative_exact_lo = derivative_center_lo - derivative_error
    assert derivative_exact_lo > Fraction(93, 500)

    leaves = part_b.certify()
    minimum_leaf = min(leaves, key=lambda row: row[2])
    assert len(leaves) == 28
    assert leaves[0][0] == 0 and leaves[-1][1] == Fraction(1, 2)
    assert minimum_leaf[2] > Fraction(309, 1000)

    packet_floor = Fraction(27, 1) * part_b.T**2 * part_b.RHO**2 / 131072
    assert packet_floor > Fraction(1, 10**36)

    return {
        "schema": "certificate0002-historical-eight-tent-two-stage-v1",
        "claim_level": "paper proof with exact rational interval certificates; not Lean-kernel evidence",
        "configuration": {
            "design": {"m": 2, "n": 2},
            "part_a": {
                "eta": rational(part_a.ETA),
                "amplitude_a": rational(part_a.A),
                "left_centers": [rational(x) for x in part_a.ELLS],
                "frequency_centers": [rational(x) for x in part_a.FS],
                "coefficients": [rational(x) for x in part_a.CS],
            },
            "part_b": {
                "rho": rational(part_b.RHO),
                "step_t": rational(part_b.T),
                "gap_slack": rational(part_b.C),
                "left_bumps": [
                    {"coefficient": 3, "e": rational(part_b.LA), "F": rational(part_b.FA)},
                    {"coefficient": -4, "e": rational(part_b.LB), "F": rational(part_b.FB)},
                ],
            },
        },
        "environment": {"python": platform.python_version(), "arithmetic": "fractions.Fraction plus math.isqrt"},
        "part_a_certificate": {
            "q_half_interval_cells": 50000,
            "reflection_extends_to_full_q_interval": True,
            "macro_exact_upper_bounds": [rational(x) for x in maxima],
            "global_center_upper": rational(global_max[0]),
            "global_center_cell": global_max[1],
            "tent_error_upper": rational(original_error),
            "derivative_rows": [rational_row(row) for row in derivative_rows],
            "proved_full_bracket_upper": rational(-Fraction(117, 500)),
            "triple_tent_error_upper": rational(triple_error),
            "triple_center_at_q_1_over_362": {
                "lower": rational(triple_center_lo),
                "upper": rational(triple_center_hi),
            },
            "triple_exact_lower": rational(triple_exact_lo),
            "proved_triple_lower": rational(Fraction(739, 1000)),
            "derivative_center_at_q_1_over_362": {
                "lower": rational(derivative_center_lo),
                "upper": rational(derivative_center_hi),
            },
            "derivative_tent_error_upper": rational(derivative_error),
            "derivative_exact_lower": rational(derivative_exact_lo),
            "proved_derivative_lower": rational(Fraction(93, 500)),
        },
        "part_b_certificate": {
            "dyadic_leaves": [
                {"q_lo": rational(lo), "q_hi": rational(hi), "gap_lower": rational(gap)}
                for lo, hi, gap in leaves
            ],
            "leaf_count": len(leaves),
            "maximum_dyadic_depth": max((hi - lo).denominator.bit_length() - 1 for lo, hi, _ in leaves),
            "minimum_leaf": {
                "q_lo": rational(minimum_leaf[0]),
                "q_hi": rational(minimum_leaf[1]),
                "gap_lower": rational(minimum_leaf[2]),
            },
            "proved_minimum_gap_lower": rational(Fraction(309, 1000)),
            "anchored_packet_floor": rational(packet_floor),
            "proved_floor_lower": rational(Fraction(1, 10**36)),
        },
        "allowed_conclusions": [
            "The displayed d_a is a finite-risk positive-affine-equivariant strict improvement over the stable baseline at the balanced (2,2) design.",
            "At q=1/362 the original correction ray is already past its local optimum, and d_(2a) is worse than d_a.",
            "The displayed disjoint two-bump correction strictly improves d_a at every physical parameter.",
            "The anchored finite-packet Bayes excess for d_a has the displayed positive seed-specific floor.",
        ],
        "disallowed_conclusions": [
            "No terminality, admissibility, or master-flatness claim is made for the two-bump descendant.",
            "No four-term residual-defect floor is established.",
            "No result is claimed outside the ordinary balanced (2,2) design.",
            "No conclusions about other estimators or designs follow from these finite certificates alone.",
            "The finite interval covers are certificates through outward enclosures, not pointwise floating grids.",
        ],
        "source_manifest": {str(path.relative_to(ROOT)): sha256(path) for path in SOURCES},
    }


def validate_schema(document: dict[str, Any]) -> None:
    jsonschema.validate(document, json.loads(SCHEMA.read_text()))


def check() -> None:
    retained = json.loads(ARTIFACT.read_text())
    validate_schema(retained)
    replay = build_candidate()
    validate_schema(replay)
    if retained != replay:
        raise AssertionError("retained artifact differs from exact replay")


def main() -> None:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--render", action="store_true")
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.render:
        print(json.dumps(build_candidate(), indent=2, sort_keys=True))
        return
    if args.write:
        document = build_candidate()
        validate_schema(document)
        ARTIFACT.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
        print(f"wrote {ARTIFACT.relative_to(ROOT)}")
        return
    if args.check:
        check()
        print("artifact schema, source hashes, and exact replay: PASS")
        return
    document = json.loads(ARTIFACT.read_text())
    print("balanced historical eight-tent two-stage certificate")
    print(f"  Part A cells: {document['part_a_certificate']['q_half_interval_cells']}")
    print(f"  Part B leaves: {document['part_b_certificate']['leaf_count']}")
    print("  scope: strict two-stage descent and a fixed-seed packet floor")


if __name__ == "__main__":
    main()
