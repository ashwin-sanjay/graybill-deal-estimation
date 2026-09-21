#!/usr/bin/env python3
"""Fail-closed wall replay using the double-Haar three-halves exterior theorem."""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

from Script0008 import finite_wall_three_halves


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
ANALYTIC_NOTE = ROOT / "proofs/Proof0003.md"
THEOREM_BEGIN = b"### A uniform pointwise wall envelope\n"
THEOREM_END = b"## 6. Exact charge-vector formulas\n"
ANALYTIC_THEOREM_SECTION_SHA256 = "a229c137ffa1037e4e509edacaa9f200122243acce13667c54c938e51f46c7cb"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def analytic_theorem_section() -> bytes:
    raw = ANALYTIC_NOTE.read_bytes()
    if raw.count(THEOREM_BEGIN) != 1 or raw.count(THEOREM_END) != 1:
        raise RuntimeError("analytic theorem sentinels are not unique")
    start = raw.index(THEOREM_BEGIN)
    end = raw.index(THEOREM_END, start + len(THEOREM_BEGIN))
    return raw[start:end]


def fstr(x: float) -> str:
    n, d = float(x).as_integer_ratio()
    return str(Fraction(n, d))


def producer_paths() -> dict[str, Path]:
    return {
        "wall_three_halves_script_sha256": HERE / "Script0008.py",
        "finite_wall_script_sha256": HERE / "Script0007.py",
        "core_script_sha256": HERE / "Script0002.py",
        "interval_core_sha256": HERE / "Script0001.py",
        "batch_script_sha256": Path(__file__).resolve(),
    }


def source_hashes() -> dict[str, str]:
    ans = {key: sha(path) for key, path in producer_paths().items()}
    section_sha = hashlib.sha256(analytic_theorem_section()).hexdigest()
    if section_sha != ANALYTIC_THEOREM_SECTION_SHA256:
        raise RuntimeError("the independently audited analytic theorem has changed")
    ans["analytic_theorem_section_sha256"] = section_sha
    return ans


def central_grid() -> dict:
    return {
        "outer_denominator": 16,
        "a_lo": -14 * 16,
        "a_hi": int(Fraction(7, 2) * 16),
        "b_lo": -8 * 16,
        "b_hi": 8 * 16,
        "batch": 16,
    }


def worker(cell):
    lo, hi, depth = cell
    grid = central_grid()
    ball, seconds, ledger = finite_wall_three_halves(lo, hi, **grid)
    return {
        "lo": str(lo),
        "hi": str(hi),
        "depth": depth,
        "enclosure": {
            "lower_binary64_exact": fstr(ball.lo),
            "upper_binary64_exact": fstr(ball.hi),
            "lower": repr(float(ball.lo)),
            "upper": repr(float(ball.hi)),
        },
        "seconds": seconds,
        "grid": grid,
        "ledger": ledger,
        "positive": bool(ball.lo > 0),
    }


def initial_cells():
    cells = []
    zero = Fraction(0)
    q = Fraction(1, 10**12)
    cells.append((zero, q, 0))
    while q < Fraction(1, 10**6):
        nq = q * 10
        cells.append((q, nq, 0))
        q = nq
    cells.append((Fraction(1, 10**6), Fraction(1, 10**5), 0))
    q = Fraction(1, 10**5)
    step = Fraction(1, 10**5)
    stop = Fraction(1, 5000)
    while q < stop:
        nq = min(stop, q + step)
        cells.append((q, nq, 0))
        q = nq
    step = Fraction(1, 10**4)
    stop = Fraction(1, 50)
    while q < stop:
        nq = min(stop, q + step)
        cells.append((q, nq, 0))
        q = nq
    return cells


def audit_cover(rows) -> None:
    spans = sorted((Fraction(row["lo"]), Fraction(row["hi"])) for row in rows)
    if not spans or spans[0][0] != 0 or spans[-1][1] != Fraction(1, 50):
        raise RuntimeError("wall endpoints are not covered")
    for left, right in zip(spans, spans[1:]):
        if left[1] != right[0]:
            raise RuntimeError(f"wall gap/overlap: {left}, {right}")
    if any(not row["positive"] for row in rows):
        raise RuntimeError("nonpositive leaf")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--max-depth", type=int, default=4)
    ap.add_argument(
        "--output", type=Path, default=HERE / "Data0009.json"
    )
    args = ap.parse_args()
    frozen = source_hashes()
    pending = initial_cells()
    passed = []
    started = time.time()
    round_no = 0
    while pending:
        round_no += 1
        failed = []
        print(f"round {round_no}: {len(pending)} cells", flush=True)
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(worker, cell): cell for cell in pending}
            done = 0
            for future in as_completed(futures):
                row = future.result()
                done += 1
                if row["positive"]:
                    passed.append(row)
                else:
                    lo, hi, depth = futures[future]
                    if depth >= args.max_depth:
                        raise RuntimeError(f"cell failed at max depth: {lo},{hi}")
                    mid = (lo + hi) / 2
                    failed.extend(((lo, mid, depth + 1), (mid, hi, depth + 1)))
                if done % 8 == 0 or done == len(futures):
                    print(
                        f"  {done}/{len(futures)} done; "
                        f"pass={len(passed)} split={len(failed)//2}",
                        flush=True,
                    )
        pending = failed
    audit_cover(passed)
    passed.sort(key=lambda row: Fraction(row["lo"]))
    after = source_hashes()
    if after != frozen:
        raise RuntimeError("certificate source changed during replay")
    exact_lower = min(
        Fraction(row["enclosure"]["lower_binary64_exact"]) for row in passed
    )
    out = {
        "format": "certificate0003-wall-three-halves-directed-sinc-v1",
        "range": ["0", "1/50"],
        "analytic_theorem": "Hbar_e <= (3/2) Gbar_e; equations (33a)-(33m)",
        "cells": passed,
        "global_lower_binary64_exact": str(exact_lower),
        "global_lower": repr(float(exact_lower)),
        **frozen,
        "seconds": time.time() - started,
    }
    args.output.write_text(json.dumps(out, indent=2) + "\n")
    print(f"cells={len(passed)} global_lower={out['global_lower']}")
    print("Certificate0003_WALL_THREE_HALVES_POSITIVITY_CERTIFIED")


if __name__ == "__main__":
    main()
