#!/usr/bin/env python3
"""Fail-closed exact checker for the reduced double-Haar parity simplex.

The checker consumes outward intervals for the *preconditioned, Euclidean
column-normalized* four-dimensional charge columns at the frozen ratios

    11/10, 2, 11/2, 18, 145.

All finite linear algebra after those input balls is exact ``Fraction``
arithmetic.  The checker proves that every matrix in the supplied interval
box is invertible and that its unique augmented-simplex solution is strictly
positive.  It does not produce or validate the statistical integral balls;
that independent directed-rounded computation must supply them.

Input schema (all endpoints are decimal or rational strings)::

  {
    "format": "certificate0003-parity-preconditioned-normalized-v1",
    "eta": ["11/10", "2", "11/2", "18", "145"],
    "row_scale": ["1/7", "4/7", "7/4", "7"],
    "columns": [
      [{"lower": "...", "upper": "..."}, ... four entries],
      ... five columns
    ]
  }

The final row of the augmented matrix is exactly one and is not an input.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


EXPECTED_FORMAT = "certificate0003-parity-preconditioned-normalized-v1"
EXPECTED_ETA = tuple(map(Fraction, ("11/10", "2", "11/2", "18", "145")))
EXPECTED_ROW_SCALE = tuple(map(Fraction, ("1/7", "4/7", "7/4", "7")))


def invert(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(matrix)
    if n == 0 or any(len(row) != n for row in matrix):
        raise ValueError("matrix is not square")
    work = [row[:] + [Fraction(int(i == j)) for j in range(n)]
            for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((row for row in range(col, n) if work[row][col]), None)
        if pivot is None:
            raise ValueError("center matrix is singular")
        work[col], work[pivot] = work[pivot], work[col]
        value = work[col][col]
        work[col] = [x / value for x in work[col]]
        for row in range(n):
            if row == col:
                continue
            factor = work[row][col]
            if factor:
                work[row] = [x - factor * y
                             for x, y in zip(work[row], work[col])]
    return [row[n:] for row in work]


def matmul(left, right):
    return [[sum((left[i][k] * right[k][j] for k in range(len(right))),
                 Fraction(0))
             for j in range(len(right[0]))]
            for i in range(len(left))]


def inf_norm(matrix):
    return max(sum(map(abs, row), Fraction(0)) for row in matrix)


def parse(data):
    if data.get("format") != EXPECTED_FORMAT:
        raise ValueError("unexpected or missing format identifier")
    eta = tuple(map(Fraction, data.get("eta", ())))
    scale = tuple(map(Fraction, data.get("row_scale", ())))
    if eta != EXPECTED_ETA:
        raise ValueError("variance-ratio support does not match frozen support")
    if scale != EXPECTED_ROW_SCALE:
        raise ValueError("row preconditioner does not match frozen preconditioner")
    columns = data.get("columns")
    if not isinstance(columns, list) or len(columns) != 5:
        raise ValueError("columns must contain exactly five charge columns")
    lower, upper = [], []
    for c, column in enumerate(columns):
        if not isinstance(column, list) or len(column) != 4:
            raise ValueError(f"column {c} does not have four coordinates")
        lo_col, hi_col = [], []
        for r, entry in enumerate(column):
            if not isinstance(entry, dict) or set(entry) != {"lower", "upper"}:
                raise ValueError(f"column {c}, row {r}: malformed interval")
            lo, hi = Fraction(entry["lower"]), Fraction(entry["upper"])
            if lo > hi:
                raise ValueError(f"column {c}, row {r}: reversed interval")
            if lo < -1 or hi > 1:
                raise ValueError(f"column {c}, row {r}: normalized range violated")
            lo_col.append(lo)
            hi_col.append(hi)
        lower.append(lo_col)
        upper.append(hi_col)
    return lower, upper


def check_box(lower, upper):
    # Input is column-major (5 by 4); the augmented matrix is row-major 5 by 5.
    center = [[(lower[c][r] + upper[c][r]) / 2 for c in range(5)]
              for r in range(4)] + [[Fraction(1) for _ in range(5)]]
    radius = [[(upper[c][r] - lower[c][r]) / 2 for c in range(5)]
              for r in range(4)] + [[Fraction(0) for _ in range(5)]]
    inverse = invert(center)
    # |A0^{-1} E| <= |A0^{-1}| R componentwise.
    perturbation = matmul([[abs(x) for x in row] for row in inverse], radius)
    q = inf_norm(perturbation)
    if q >= 1:
        raise ValueError(f"Neumann gate failed: q={q} is not below one")
    # w0=A0^{-1}e_5 is the last column of the inverse.
    weights = [row[4] for row in inverse]
    if min(weights) <= 0:
        raise ValueError("center simplex does not have strictly positive weights")
    error = q / (1 - q) * max(map(abs, weights))
    if error >= min(weights):
        raise ValueError("positive-weight perturbation gate failed")
    return {
        "q": q,
        "center_weights": weights,
        "weight_error_bound": error,
        "minimum_certified_weight": min(weights) - error,
        "center_inverse_norm_inf": inf_norm(inverse),
        "matrix_radius_inf": inf_norm(radius),
    }


def synthetic_selftest():
    # Columns e_1/2,...,e_4/2,-1/2 balance with weights 1/5.  Tiny rational boxes
    # exercise the same exact checker without asserting any statistical data.
    eps = Fraction(1, 10**8)
    columns = []
    for c in range(5):
        column = []
        for r in range(4):
            center = Fraction(int(c == r), 2) if c < 4 else Fraction(-1, 2)
            column.append({"lower": str(center - eps),
                           "upper": str(center + eps)})
        columns.append(column)
    result = check_box(*parse({
        "format": EXPECTED_FORMAT,
        "eta": [str(x) for x in EXPECTED_ETA],
        "row_scale": [str(x) for x in EXPECTED_ROW_SCALE],
        "columns": columns,
    }))
    assert result["minimum_certified_weight"] > 0
    print("SYNTHETIC_EXACT_SELFTEST_PASS")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        synthetic_selftest()
        return
    if args.input is None:
        parser.error("an interval JSON file is required unless --selftest is used")
    data = json.loads(args.input.read_text())
    result = check_box(*parse(data))
    print("double-Haar PARITY INTERVAL SIMPLEX CHECK")
    for key, value in result.items():
        if isinstance(value, list):
            print(key, "=", [str(x) for x in value])
        else:
            print(key, "=", str(value))
    print("FINITE_INTERVAL_SIMPLEX_CERTIFIED")
    print("CERTIFICATION_IS_CONDITIONAL_ON_THE_INPUT_CHARGE_ENCLOSURES")


if __name__ == "__main__":
    main()
