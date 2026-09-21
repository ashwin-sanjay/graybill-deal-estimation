#!/usr/bin/env python3
"""Directed wall certificate using the global three-halves posterior bound.

This producer is separate from ``Script0007.py``.  It reuses that
file only for the finite directed-rounded sinc lattice and replaces its loose
endpoint exterior envelope by the exact analytic inequality

    0 <= Hbar_e(a,b) <= (3/2) Gbar_e(b) <= (3/2) exp(b).

Consequently every outer Poisson and omitted-lattice term is controlled by
the first two beta-prime moments E exp(b)=5/4 and E exp(2b)=5/2.  No sampled
tail or floating grid is promoted to a proof.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
import time

import numpy as np
from flint import arb, ctx

from Script0002 import arb_upper, CT_NUM, CT_DEN, CS
from Script0007 import finite_wall_lattice


def _aq(q: Fraction | int) -> arb:
    q = Fraction(q)
    return arb(q.numerator) / q.denominator


def three_halves_external_error(
    eb: Fraction,
    step: Fraction,
    *,
    a_lo_index: int,
    a_hi_index: int,
    b_lo_index: int,
    b_hi_index: int,
    axis_strip: Fraction = Fraction(7, 25),
    mixed_strip: Fraction = Fraction(7, 50),
) -> dict[str, float]:
    """Rigorous outer Poisson and omitted-lattice error on ``0<=e<=eb``.

    On a complex outer shift ``(alpha,beta)``, put
    ``span=|alpha|+|beta|``.  The real three-halves theorem
    and the sector comparison give

      |G_C| <= sec(beta/2) X,
      |H_C| <= (3/2) sec((alpha+beta)/2)^p
                       sec(p span/2) X,

    where ``X=exp(b)`` and ``p=21/2``.  Integrating the resulting quadratic
    envelope uses E[X]=5/4 and E[X^2]=5/2 exactly.
    """
    old_prec = ctx.prec
    ctx.prec = 256
    try:
        p = arb(21) / 2
        h = _aq(step)
        ehi = _aq(eb)
        ex1 = arb(5) / 4
        ex2 = arb(5) / 2

        def boundary(alpha: arb, beta: arb) -> arb:
            span = alpha + beta
            density = (1 / (alpha / 2).cos()) ** (arb(23) / 2)
            density *= (1 / (beta / 2).cos()) ** 10
            gf = 1 / (beta / 2).cos()
            hf = (1 / (span / 2).cos()) ** p
            hf /= (p * span / 2).cos()
            # (gf X + 1)^2 + ((3/2) hf X + 1)^2.
            field = 2 + 2 * (gf + arb(3) * hf / 2) * ex1
            field += (gf**2 + arb(9) * hf**2 / 4) * ex2
            return density * (1 + ehi) * field / 11

        d0 = _aq(axis_strip)
        d1 = _aq(mixed_strip)
        ma = boundary(d0, arb(0))
        mb = boundary(arb(0), d0)
        mm = boundary(d1, d1)
        r0 = (-2 * arb.pi() * d0 / h).exp()
        r1 = (-2 * arb.pi() * d1 / h).exp()
        poisson = 2 * (ma + mb) * r0 / (1 - r0)
        poisson += 4 * mm * (r1 / (1 - r1)) ** 2

        # Infinite real h-lattice upper bounds from exact integrals and a
        # one-dimensional strip shift.  Numerators exp(k b) have unit modulus
        # under an imaginary shift, so the density secant power is unchanged.
        strip = arb(1)

        def full_lattice(integral: arb, density_power: arb) -> arb:
            relative = 2 * (1 / (strip / 2).cos()) ** density_power
            relative /= (2 * arb.pi() * strip / h).exp() - 1
            return integral * (1 + relative)

        afull = full_lattice(arb(1), arb(23) / 2)
        b0full = full_lattice(arb(1), arb(10))
        b1full = full_lattice(ex1, arb(10))
        b2full = full_lattice(ex2, arb(10))

        al = _aq(Fraction(a_lo_index - 1) * step)
        ar = _aq(Fraction(a_hi_index + 1) * step)
        bl = _aq(Fraction(b_lo_index - 1) * step)
        br = _aq(Fraction(b_hi_index + 1) * step)
        # CT=B(3/2,10)^(-1); CS=B(5,5)^(-1).
        ct = arb(CT_NUM) / CT_DEN
        cs = arb(CS)

        def two_tails(coef: arb, left_rate: int | Fraction,
                      right_rate: int | Fraction, left: arb, right: arb) -> arb:
            lr = _aq(Fraction(left_rate))
            rr = _aq(Fraction(right_rate))
            ans = h * coef * (lr * left).exp() / (1 - (-lr * h).exp())
            ans += h * coef * (-rr * right).exp() / (1 - (-rr * h).exp())
            return ans

        aout = two_tails(ct, Fraction(3, 2), 10, al, ar)
        b0out = two_tails(cs, 5, 5, bl, br)
        b1out = two_tails(cs, 6, 4, bl, br)
        b2out = two_tails(cs, 7, 3, bl, br)

        # Real field envelope 2 + 5 X + (13/4) X^2.  The union bound on
        # omitted a- or b-nodes deliberately double-counts the corner.
        bfield_full = 2 * b0full + 5 * b1full + arb(13) * b2full / 4
        bfield_out = 2 * b0out + 5 * b1out + arb(13) * b2out / 4
        omitted = (1 + ehi) * (aout * bfield_full + afull * bfield_out) / 11
        total = poisson + omitted
        return {
            "poisson": arb_upper(poisson),
            "tail": arb_upper(omitted),
            "external": arb_upper(total),
            "axis_ma": arb_upper(ma),
            "axis_mb": arb_upper(mb),
            "mixed_mab": arb_upper(mm),
            "a_lattice_upper": arb_upper(afull),
            "b0_lattice_upper": arb_upper(b0full),
            "b1_lattice_upper": arb_upper(b1full),
            "b2_lattice_upper": arb_upper(b2full),
        }
    finally:
        ctx.prec = old_prec


def finite_wall_three_halves(
    ea: Fraction,
    eb: Fraction,
    *,
    outer_denominator: int = 16,
    a_lo: int | None = None,
    a_hi: int | None = None,
    b_lo: int | None = None,
    b_hi: int | None = None,
    batch: int = 16,
):
    """Return the finite wall ball plus the analytic three-halves exterior."""
    if a_lo is None:
        a_lo = -14 * outer_denominator
    if a_hi is None:
        a_hi = Fraction(7, 2) * outer_denominator
    if b_lo is None:
        b_lo = -8 * outer_denominator
    if b_hi is None:
        b_hi = 8 * outer_denominator
    a_lo, a_hi, b_lo, b_hi = map(int, (a_lo, a_hi, b_lo, b_hi))
    started = time.time()
    finite, finite_seconds = finite_wall_lattice(
        ea,
        eb,
        outer_denominator=outer_denominator,
        a_lo=a_lo,
        a_hi=a_hi,
        b_lo=b_lo,
        b_hi=b_hi,
        batch=batch,
        include_external=False,
    )
    ledger = three_halves_external_error(
        eb,
        Fraction(1, outer_denominator),
        a_lo_index=a_lo,
        a_hi_index=a_hi,
        b_lo_index=b_lo,
        b_hi_index=b_hi,
    )
    from Script0007 import sym

    result = finite + sym(ledger["external"])
    ledger["finite"] = [float(finite.lo), float(finite.hi)]
    ledger["finite_seconds"] = finite_seconds
    return result, time.time() - started, ledger


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--e-lo", default="0")
    ap.add_argument("--e-hi", default="1/10000")
    ap.add_argument("--outer-denominator", type=int, default=16)
    ap.add_argument("--batch", type=int, default=16)
    args = ap.parse_args()
    ball, seconds, ledger = finite_wall_three_halves(
        Fraction(args.e_lo),
        Fraction(args.e_hi),
        outer_denominator=args.outer_denominator,
        batch=args.batch,
    )
    print(json.dumps({
        "e": [args.e_lo, args.e_hi],
        "enclosure": [float(ball.lo), float(ball.hi)],
        "seconds": seconds,
        "ledger": ledger,
    }, indent=2))


if __name__ == "__main__":
    main()
