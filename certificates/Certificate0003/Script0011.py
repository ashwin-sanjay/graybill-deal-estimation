#!/usr/bin/env python3
"""Independent fail-closed checker for the double-Haar v3 wall artifact.

The v3 producer uses the exact pointwise posterior envelope

    Hbar_e <= (3/2) Gbar_e

to control its outer Poisson and omitted-lattice errors.  This checker does
not import any producer module.  It authenticates current source files and explicitly retained inputs through
the current input manifest, verifies exact binary64 endpoint
serialization, checks that every accepted cell is a correctly routed dyadic
leaf, and proves that the leaves form a positive gap-free cover of
``[0,1/50]`` with the declared exact global minimum.

The directed producer remains responsible for the analytic enclosures.  This
script checks their declared current provenance and all finite structural obligations.
Retained inputs are explicitly marked as not regenerated; fresh outputs must bind
the current producers. The immutable analytic subsection remains independently pinned.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from Script0012 import check_binding
import hashlib
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXP = Path(__file__).resolve().parent
DEFAULT_ARTIFACT = EXP / "Data0009.json"

SOURCES = {
    "wall_three_halves_script_sha256":
        EXP / "Script0008.py",
    "finite_wall_script_sha256": EXP / "Script0007.py",
    "core_script_sha256": EXP / "Script0002.py",
    "interval_core_sha256": EXP / "Script0001.py",
    "batch_script_sha256": EXP / "Script0009.py",
}

ANALYTIC_NOTE = (
    ROOT / "proofs" / "Proof0003.md"
)
THEOREM_BEGIN = b"### A uniform pointwise wall envelope\n"
THEOREM_END = b"## 6. Exact charge-vector formulas\n"
ANALYTIC_THEOREM_SECTION_SHA256 = (
    "a229c137ffa1037e4e509edacaa9f200122243acce13667c54c938e51f46c7cb"
)
LOCAL_CHECKER = EXP / "Script0010.py"
EXPECTED_FORMAT = "certificate0003-wall-three-halves-directed-sinc-v1"
EXPECTED_THEOREM = "Hbar_e <= (3/2) Gbar_e; equations (33a)-(33m)"
EXPECTED_GRID = {
    "outer_denominator": 16,
    "a_lo": -224,
    "a_hi": 56,
    "b_lo": -128,
    "b_hi": 128,
    "batch": 16,
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def analytic_theorem_section() -> bytes:
    """Extract exactly the reviewed theorem bytes, independently of producers."""
    raw = ANALYTIC_NOTE.read_bytes()
    if raw.count(THEOREM_BEGIN) != 1 or raw.count(THEOREM_END) != 1:
        raise ValueError("analytic theorem sentinels are not unique")
    start = raw.index(THEOREM_BEGIN)
    end = raw.index(THEOREM_END, start + len(THEOREM_BEGIN))
    return raw[start:end]


def exact_binary64(decimal: str, rational: str, label: str) -> Fraction:
    try:
        value = float(decimal)
        exact = Fraction(rational)
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"{label}: malformed binary64 endpoint") from exc
    if not math.isfinite(value):
        raise ValueError(f"{label}: non-finite binary64 endpoint")
    if Fraction.from_float(value) != exact:
        raise ValueError(f"{label}: decimal and exact binary64 disagree")
    return exact


def initial_spans() -> tuple[tuple[Fraction, Fraction], ...]:
    spans: list[tuple[Fraction, Fraction]] = []
    q = Fraction(1, 10**12)
    spans.append((Fraction(0), q))
    while q < Fraction(1, 10**6):
        next_q = 10 * q
        spans.append((q, next_q))
        q = next_q
    spans.append((Fraction(1, 10**6), Fraction(1, 10**5)))
    q = Fraction(1, 10**5)
    while q < Fraction(1, 5000):
        next_q = min(Fraction(1, 5000), q + Fraction(1, 10**5))
        spans.append((q, next_q))
        q = next_q
    while q < Fraction(1, 50):
        next_q = min(Fraction(1, 50), q + Fraction(1, 10**4))
        spans.append((q, next_q))
        q = next_q
    return tuple(spans)


INITIAL_SPANS = initial_spans()


def is_dyadic_leaf(lo: Fraction, hi: Fraction, depth: int) -> bool:
    for base_lo, base_hi in INITIAL_SPANS:
        width = (base_hi - base_lo) / 2**depth
        if hi - lo != width:
            continue
        offset = (lo - base_lo) / width
        if (offset.denominator == 1 and 0 <= offset < 2**depth
                and hi <= base_hi):
            return True
    return False


def finite_nonnegative(value: object, label: str) -> float:
    try:
        parsed = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{label}: malformed numeric ledger entry") from exc
    if not math.isfinite(parsed) or parsed < 0:
        raise ValueError(f"{label}: negative or non-finite ledger entry")
    return parsed


def check(data: dict) -> tuple[int, Fraction, int]:
    check_binding(data,SOURCES)
    theorem_section_sha = hashlib.sha256(analytic_theorem_section()).hexdigest()
    if theorem_section_sha != ANALYTIC_THEOREM_SECTION_SHA256:
        raise ValueError("the audited analytic theorem section has changed")
    if data.get("format") != EXPECTED_FORMAT:
        raise ValueError("wrong v3 wall artifact format")
    if tuple(map(Fraction, data.get("range", ()))) != (0, Fraction(1, 50)):
        raise ValueError("wrong v3 wall range")
    if data.get("analytic_theorem") != EXPECTED_THEOREM:
        raise ValueError("wrong analytic-theorem identifier")
    if data.get("analytic_theorem_section_sha256") != theorem_section_sha:
        raise ValueError("stale or mismatched analytic theorem section")

    rows = data.get("cells")
    if not isinstance(rows, list) or not rows:
        raise ValueError("missing v3 wall cells")
    checked: list[tuple[Fraction, Fraction, Fraction]] = []
    maximum_depth = 0
    ledger_keys = (
        "poisson", "tail", "external", "axis_ma", "axis_mb", "mixed_mab",
        "a_lattice_upper", "b0_lattice_upper", "b1_lattice_upper",
        "b2_lattice_upper", "finite_seconds",
    )
    for index, row in enumerate(rows):
        try:
            lo, hi = Fraction(row["lo"]), Fraction(row["hi"])
        except (KeyError, TypeError, ValueError, ZeroDivisionError) as exc:
            raise ValueError(f"cell {index}: malformed parameter endpoints") from exc
        depth = row.get("depth")
        if not isinstance(depth, int) or not 0 <= depth <= 4:
            raise ValueError(f"cell {index}: invalid bisection depth")
        if not 0 <= lo < hi <= Fraction(1, 50):
            raise ValueError(f"cell {index}: parameter interval outside wall")
        if not is_dyadic_leaf(lo, hi, depth):
            raise ValueError(f"cell {index}: invalid dyadic routing")
        if row.get("grid") != EXPECTED_GRID:
            raise ValueError(f"cell {index}: unexpected central grid")

        enclosure = row.get("enclosure")
        if not isinstance(enclosure, dict):
            raise ValueError(f"cell {index}: missing enclosure")
        lower = exact_binary64(
            enclosure.get("lower"), enclosure.get("lower_binary64_exact"),
            f"cell {index} lower")
        upper = exact_binary64(
            enclosure.get("upper"), enclosure.get("upper_binary64_exact"),
            f"cell {index} upper")
        if not 0 < lower <= upper or row.get("positive") is not True:
            raise ValueError(f"cell {index}: nonpositive or reversed enclosure")

        ledger = row.get("ledger")
        if not isinstance(ledger, dict):
            raise ValueError(f"cell {index}: missing analytic-error ledger")
        for key in ledger_keys:
            finite_nonnegative(ledger.get(key), f"cell {index} ledger {key}")
        finite = ledger.get("finite")
        if not isinstance(finite, list) or len(finite) != 2:
            raise ValueError(f"cell {index}: malformed finite-lattice enclosure")
        try:
            finite_lo, finite_hi = map(float, finite)
        except (TypeError, ValueError) as exc:
            raise ValueError(f"cell {index}: malformed finite-lattice endpoint") from exc
        if not (math.isfinite(finite_lo) and math.isfinite(finite_hi)
                and finite_lo <= finite_hi):
            raise ValueError(f"cell {index}: invalid finite-lattice enclosure")
        runtime = finite_nonnegative(row.get("seconds"), f"cell {index} runtime")
        if runtime == 0:
            raise ValueError(f"cell {index}: zero runtime")
        checked.append((lo, hi, lower))
        maximum_depth = max(maximum_depth, depth)

    checked.sort()
    if checked[0][0] != 0 or checked[-1][1] != Fraction(1, 50):
        raise ValueError("v3 wall endpoints are not covered")
    for left, right in zip(checked, checked[1:]):
        if left[1] != right[0]:
            raise ValueError(f"gap or overlap between {left[:2]} and {right[:2]}")

    exact_minimum = min(row[2] for row in checked)
    declared = Fraction(data.get("global_lower_binary64_exact", ""))
    if declared != exact_minimum:
        raise ValueError("declared exact global lower is not the cell minimum")
    exact_binary64(data.get("global_lower"), str(declared), "global lower")
    finite_nonnegative(data.get("seconds"), "total runtime")
    return len(checked), exact_minimum, maximum_depth


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("artifact", nargs="?", type=Path, default=DEFAULT_ARTIFACT)
    args = parser.parse_args()
    cells, lower, depth = check(json.loads(args.artifact.read_text()))
    print(f"cells = {cells}")
    print(f"maximum_depth = {depth}")
    print(f"global_lower_binary64_exact = {lower}")
    print(f"global_lower = {float(lower)!r}")
    print("Certificate0003_WALL_THREE_HALVES_INDEPENDENT_CHECK_PASS")


if __name__ == "__main__":
    main()
