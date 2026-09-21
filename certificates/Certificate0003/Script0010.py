#!/usr/bin/env python3
"""Exact structural checker for the double-Haar three-halves wall artifact."""

from __future__ import annotations

from fractions import Fraction
from Script0012 import check_binding
import hashlib
import json
import math
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
THEOREM_BEGIN = b"### A uniform pointwise wall envelope\n"
THEOREM_END = b"## 6. Exact charge-vector formulas\n"
THEOREM_SECTION_SHA = "a229c137ffa1037e4e509edacaa9f200122243acce13667c54c938e51f46c7cb"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def initial_spans():
    spans = []
    q = Fraction(1, 10**12)
    spans.append((Fraction(0), q))
    while q < Fraction(1, 10**6):
        nq = q * 10
        spans.append((q, nq))
        q = nq
    spans.append((Fraction(1, 10**6), Fraction(1, 10**5)))
    q = Fraction(1, 10**5)
    while q < Fraction(1, 5000):
        nq = min(Fraction(1, 5000), q + Fraction(1, 10**5))
        spans.append((q, nq))
        q = nq
    while q < Fraction(1, 50):
        nq = min(Fraction(1, 50), q + Fraction(1, 10**4))
        spans.append((q, nq))
        q = nq
    return spans


def dyadic_leaf(lo: Fraction, hi: Fraction, depth: int) -> bool:
    for base_lo, base_hi in initial_spans():
        if base_lo <= lo and hi <= base_hi:
            width = (base_hi - base_lo) / 2**depth
            if hi - lo != width:
                continue
            k = (lo - base_lo) / width
            if k.denominator == 1 and 0 <= k < 2**depth:
                return True
    return False


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "Data0009.json"
    obj = json.loads(path.read_text())
    if obj.get("format") != "certificate0003-wall-three-halves-directed-sinc-v1":
        raise SystemExit("bad format")
    if obj.get("range") != ["0", "1/50"]:
        raise SystemExit("bad wall range")
    if obj.get("analytic_theorem") != "Hbar_e <= (3/2) Gbar_e; equations (33a)-(33m)":
        raise SystemExit("bad analytic theorem identifier")

    paths = {
        "wall_three_halves_script_sha256": HERE / "Script0008.py",
        "finite_wall_script_sha256": HERE / "Script0007.py",
        "core_script_sha256": HERE / "Script0002.py",
        "interval_core_sha256": HERE / "Script0001.py",
        "batch_script_sha256": HERE / "Script0009.py",
    }
    check_binding(obj,paths)
    raw = (ROOT / "proofs/Proof0003.md").read_bytes()
    if raw.count(THEOREM_BEGIN) != 1 or raw.count(THEOREM_END) != 1:
        raise SystemExit("analytic theorem sentinels are not unique")
    start = raw.index(THEOREM_BEGIN)
    end = raw.index(THEOREM_END, start + len(THEOREM_BEGIN))
    section_sha = hashlib.sha256(raw[start:end]).hexdigest()
    if section_sha != THEOREM_SECTION_SHA:
        raise SystemExit("unreviewed analytic theorem section")
    if obj.get("analytic_theorem_section_sha256") != section_sha:
        raise SystemExit("artifact analytic theorem mismatch")

    rows = obj.get("cells")
    if not isinstance(rows, list) or not rows:
        raise SystemExit("missing cells")
    expected_grid = {
        "outer_denominator": 16,
        "a_lo": -224,
        "a_hi": 56,
        "b_lo": -128,
        "b_hi": 128,
        "batch": 16,
    }
    spans = []
    lower_bounds = []
    for row in rows:
        lo, hi = Fraction(row["lo"]), Fraction(row["hi"])
        depth = row.get("depth")
        if not isinstance(depth, int) or not 0 <= depth <= 4:
            raise SystemExit("bad depth")
        if not lo < hi or not dyadic_leaf(lo, hi, depth):
            raise SystemExit(f"bad routed leaf: {lo},{hi},depth={depth}")
        if row.get("grid") != expected_grid:
            raise SystemExit("bad central grid")
        enc = row.get("enclosure", {})
        lower = Fraction(enc["lower_binary64_exact"])
        upper = Fraction(enc["upper_binary64_exact"])
        if lower <= 0 or lower > upper or not row.get("positive"):
            raise SystemExit(f"nonpositive/invalid enclosure: {lo},{hi}")
        # The human-readable decimal must round back to the certified binary64.
        if Fraction(*float(enc["lower"]).as_integer_ratio()) != lower:
            raise SystemExit("lower decimal/binary mismatch")
        if Fraction(*float(enc["upper"]).as_integer_ratio()) != upper:
            raise SystemExit("upper decimal/binary mismatch")
        ledger = row.get("ledger")
        if not isinstance(ledger, dict) or "external" not in ledger:
            raise SystemExit("missing external ledger")
        external = float(ledger["external"])
        if not math.isfinite(external) or external < 0:
            raise SystemExit("invalid external ledger")
        if not math.isfinite(float(row.get("seconds", math.nan))) or row["seconds"] <= 0:
            raise SystemExit("invalid runtime")
        spans.append((lo, hi))
        lower_bounds.append(lower)

    spans.sort()
    if spans[0][0] != 0 or spans[-1][1] != Fraction(1, 50):
        raise SystemExit("wall endpoints not covered")
    for left, right in zip(spans, spans[1:]):
        if left[1] != right[0]:
            raise SystemExit(f"gap/overlap: {left},{right}")
    exact_min = min(lower_bounds)
    if Fraction(obj.get("global_lower_binary64_exact", "0")) != exact_min:
        raise SystemExit("wrong exact global minimum")
    if Fraction(*float(obj["global_lower"]).as_integer_ratio()) != exact_min:
        raise SystemExit("wrong decimal global minimum")
    print(f"cells={len(rows)} global_lower={float(exact_min):.17g}")
    print("Certificate0003_WALL_THREE_HALVES_ARTIFACT_CHECKED")


if __name__ == "__main__":
    main()
