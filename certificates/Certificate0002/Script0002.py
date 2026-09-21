#!/usr/bin/env python3
"""Exact-rational audit for the continuum sign certificate in Part A.

This script uses Fraction arithmetic and integer square roots for every
assertion.  Decimal strings are produced only after the assertions, for
human-readable output.  In particular, this is an interval cover of the
whole q-interval, not evaluation of the target function on a finite grid.
"""

from decimal import Decimal, getcontext
from fractions import Fraction as Q
from math import isqrt


ETA = Q(1, 100_000)
A = Q(1, 250)
SQRT_DEN = 10**18

ELLS = (Q(1, 20), Q(3, 20), Q(1, 50), Q(1, 10))
FS = (Q(2), Q(1, 50), Q(1, 50), Q(1, 50))
CS = (
    -Q(46_233, 500_000),
    Q(294_569, 500_000),
    Q(131_993, 1_000_000),
    Q(70_711, 1_000_000),
)


def decimal(x: Q, digits: int = 16) -> str:
    """Display only; no assertion depends on Decimal arithmetic."""
    getcontext().prec = digits
    return str(Decimal(x.numerator) / Decimal(x.denominator))


def sqrt_interval(x: Q) -> tuple[Q, Q]:
    """Return exact rational lo,hi with lo <= sqrt(x) < hi."""
    assert x > 0
    scaled_floor = (x.numerator * SQRT_DEN * SQRT_DEN) // x.denominator
    m = isqrt(scaled_floor)
    lo = Q(m, SQRT_DEN)
    hi = Q(m + 1, SQRT_DEN)
    assert lo * lo <= x < hi * hi
    return lo, hi


def interval_mul(x: tuple[Q, Q], y: tuple[Q, Q]) -> tuple[Q, Q]:
    products = (x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1])
    return min(products), max(products)


def p_value(q: Q, e: Q, f: Q) -> Q:
    return e + q * (1 - 2 * e + f) - f * q * q


def p_interval(q_lo: Q, q_hi: Q, e: Q, f: Q) -> tuple[Q, Q]:
    """Exact range enclosure for concave quadratic P_q on [q_lo,q_hi]."""
    endpoint_values = [p_value(q_lo, e, f), p_value(q_hi, e, f)]
    p_lo = min(endpoint_values)  # A concave function has endpoint minimum.
    candidates = list(endpoint_values)
    vertex = Q(1 - 2 * e + f, 2 * f)
    if q_lo <= vertex <= q_hi:
        candidates.append(p_value(vertex, e, f))
    p_hi = max(candidates)
    assert 0 < p_lo <= p_hi
    return p_lo, p_hi


def kernel_interval(q_lo: Q, q_hi: Q, e: Q, f: Q) -> tuple[Q, Q]:
    """Enclose sqrt(f/[e(1-e)]) P_q(e,f)^(-5/2)."""
    ratio_lo, ratio_hi = sqrt_interval(f / (e * (1 - e)))
    p_lo, p_hi = p_interval(q_lo, q_hi, e, f)

    # x -> x^(-5/2) is decreasing.  The indicated choices of square-root
    # endpoints round the reciprocal bounds outwards.
    sqrt_p_hi_lo, sqrt_p_hi_hi = sqrt_interval(p_hi)
    sqrt_p_lo_lo, sqrt_p_lo_hi = sqrt_interval(p_lo)
    del sqrt_p_hi_lo, sqrt_p_lo_hi
    power_lo = 1 / (p_hi * p_hi * sqrt_p_hi_hi)
    power_hi = 1 / (p_lo * p_lo * sqrt_p_lo_lo)
    return interval_mul((ratio_lo, ratio_hi), (power_lo, power_hi))


def coefficient(q: Q, e: Q, c: Q, sign: int, quadratic_multiplier: int) -> Q:
    return (
        2 * sign * c * (e - q)
        + Q(4, 9) * quadratic_multiplier * A * c * c
    )


def center_term_interval(
    q_lo: Q,
    q_hi: Q,
    e: Q,
    f: Q,
    c: Q,
    sign: int,
    quadratic_multiplier: int,
) -> tuple[Q, Q]:
    coeff_endpoints = sorted(
        (
            coefficient(q_lo, e, c, sign, quadratic_multiplier),
            coefficient(q_hi, e, c, sign, quadratic_multiplier),
        )
    )
    return interval_mul(
        (coeff_endpoints[0], coeff_endpoints[1]),
        kernel_interval(q_lo, q_hi, e, f),
    )


def center_sum_interval(
    q_lo: Q, q_hi: Q, quadratic_multiplier: int = 1
) -> tuple[Q, Q]:
    lo = Q(0)
    hi = Q(0)
    for ell, f, c in zip(ELLS, FS, CS):
        for sign, e in ((1, ell), (-1, 1 - ell)):
            term_lo, term_hi = center_term_interval(
                q_lo, q_hi, e, f, c, sign, quadratic_multiplier
            )
            lo += term_lo
            hi += term_hi
    return lo, hi


# Macro-ranges are unions of the 10^-5 closed rational cells.  The listed
# caps are deliberately rounded upward (toward +infinity).
MACRO_CELL_CUTS = (0, 100, 200, 300, 400, 500, 700, 1_000,
                   2_000, 5_000, 10_000, 20_000, 30_000, 40_000, 50_000)
MACRO_CAPS = (
    -Q(811, 1000),
    -Q(399, 1000),
    -Q(247, 1000),
    -Q(235, 1000),
    -Q(256, 1000),
    -Q(363, 1000),
    -Q(715, 1000),
    -Q(1305, 1000),
    -Q(2484, 1000),
    -Q(2543, 1000),
    -Q(2542, 1000),
    -Q(2511, 1000),
    -Q(2449, 1000),
    -Q(2425, 1000),
)


def verify_center_cover() -> tuple[list[Q], tuple[Q, int]]:
    """Cover every q in [0,1/2] and prove S_0(q) < -47/200."""
    group_maxima: list[Q | None] = [None] * len(MACRO_CAPS)
    global_max: tuple[Q, int] | None = None
    group = 0

    for k in range(50_000):
        while k >= MACRO_CELL_CUTS[group + 1]:
            group += 1
        q_lo = Q(k, 100_000)
        q_hi = Q(k + 1, 100_000)
        _, upper = center_sum_interval(q_lo, q_hi)

        if group_maxima[group] is None or upper > group_maxima[group]:
            group_maxima[group] = upper
        if global_max is None or upper > global_max[0]:
            global_max = (upper, k)

    assert all(x is not None for x in group_maxima)
    exact_maxima = [x for x in group_maxima if x is not None]
    for exact_upper, advertised_cap in zip(exact_maxima, MACRO_CAPS):
        assert exact_upper < advertised_cap
    assert global_max is not None
    assert global_max[0] < -Q(47, 200)
    return exact_maxima, global_max


def ceil_fraction(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


# Simple integer upper bounds for K on the eight full tent rectangles.
# Each is independently checked below by a rational squared inequality.
K_INTEGER_BOUNDS = (
    (11_615, 8),
    (46, 3),
    (17_889, 6),
    (150, 3),
)


def tent_error_bound(quadratic_multiplier: int = 1):
    """Exact Taylor-remainder bound for all eight tent rectangles."""
    total_linear = Q(0)
    total_quadratic = Q(0)
    rows = []

    for r, (ell, f, c) in enumerate(zip(ELLS, FS, CS)):
        for side, e_center in enumerate((ell, 1 - ell)):
            e_lo, e_hi = e_center - ETA, e_center + ETA
            f_lo, f_hi = f - ETA, f + ETA

            # On 0 <= q <= 1/2, P is increasing in e and F.  After taking
            # their lower endpoints it is concave in q, hence its minimum is
            # at q=0 or q=1/2.  At those endpoints P=e and P=1/2+F/4.
            p_min = min(e_lo, Q(1, 2) + f_lo / 4)
            e_product_min = min(e_lo * (1 - e_lo), e_hi * (1 - e_hi))
            k_bound = Q(K_INTEGER_BOUNDS[r][side])
            assert k_bound * k_bound * e_product_min * p_min**5 >= f_hi

            # Bounds for the logarithmic derivatives.  Here
            # |P_e|=|1-2q| <= 1 and P_F=q(1-q) <= 1/4.
            abs_log_e = (
                Q(1, 2) / e_lo
                + Q(1, 2) / (1 - e_hi)
                + Q(5, 2) / p_min
            )
            abs_log_ee = (
                Q(1, 2) / e_lo**2
                + Q(1, 2) / (1 - e_hi) ** 2
                + Q(5, 2) / p_min**2
            )
            k_ee = Q(ceil_fraction(k_bound * (abs_log_e**2 + abs_log_ee)))

            abs_log_f = Q(1, 2) / f_lo + Q(5, 8) / p_min
            abs_log_ff = Q(1, 2) / f_lo**2 + Q(5, 32) / p_min**2
            k_ff = Q(ceil_fraction(k_bound * (abs_log_f**2 + abs_log_ff)))

            # Maximum of |e-q| on the rectangle occurs at a corner.
            abs_e_minus_q = max(
                abs(e_lo), abs(e_hi), abs(e_lo - Q(1, 2)), abs(e_hi - Q(1, 2))
            )
            phi_ee = 2 * abs(c) * (
                abs_e_minus_q * k_ee + 2 * k_bound * abs_log_e
            )
            phi_ff = 2 * abs(c) * abs_e_minus_q * k_ff

            # rho_1(u)=1-|u| has E u^2=1/6, producing eta^2/12.
            linear_error = ETA**2 * (phi_ee + phi_ff) / 12
            # Normalized rho_2=(3/2)(1-|u|)^2 has E u^2=1/10;
            # the unnormalized squared tents have total mass 4/9.
            base_quadratic_error = (
                Q(4, 9) * A * c * c * ETA**2 * (k_ee + k_ff) / 20
            )
            total_linear += linear_error
            total_quadratic += base_quadratic_error
            rows.append(
                (
                    r + 1,
                    "low" if side == 0 else "high",
                    int(k_bound),
                    int(k_ee),
                    int(k_ff),
                    ceil_fraction(
                        (linear_error + quadratic_multiplier * base_quadratic_error)
                        * 10**9
                    ),
                )
            )

    total = total_linear + quadratic_multiplier * total_quadratic
    return total, total_linear, total_quadratic, rows


def verify_tent_error_and_doubled_rule_witness():
    original_error, linear_error, quadratic_error, rows = tent_error_bound(1)
    assert original_error < Q(1, 1000)
    # S_0 < -47/200 and |T-S_0| below this exact error imply T<-117/500.
    assert -Q(47, 200) + original_error < -Q(117, 500)

    triple_error, linear_again, quadratic_again, triple_rows = tent_error_bound(3)
    assert linear_again == linear_error
    assert quadratic_again == quadratic_error
    assert triple_error < Q(718, 1_000_000)

    # At sigma=19,tau=1 one has q=1/362.  The coefficient of Q^2 in
    # R(d_{2a})-R(d_a) is 3a, so use quadratic_multiplier=3.
    q = Q(1, 362)
    center_lo, center_hi = center_sum_interval(q, q, quadratic_multiplier=3)
    assert center_lo > Q(7403, 10_000)
    exact_lower = center_lo - triple_error
    assert exact_lower > Q(739, 1000)
    return (
        original_error,
        rows,
        triple_error,
        triple_rows,
        center_lo,
        center_hi,
        exact_lower,
    )


def main() -> None:
    maxima, global_max = verify_center_cover()
    (
        original_error,
        rows,
        triple_error,
        _triple_rows,
        witness_center_lo,
        witness_center_hi,
        witness_exact_lo,
    ) = verify_tent_error_and_doubled_rule_witness()

    print("EXACT ASSERTIONS PASSED")
    print("covered q cells: 50000 (entire [0,1/2])")
    print("macro interval upper bounds:")
    for j, (exact_upper, cap) in enumerate(zip(maxima, MACRO_CAPS)):
        lo = Q(MACRO_CELL_CUTS[j], 100_000)
        hi = Q(MACRO_CELL_CUTS[j + 1], 100_000)
        print(
            f"  [{decimal(lo, 8)}, {decimal(hi, 8)}]: "
            f"exact upper {decimal(exact_upper, 16)} < cap {cap}"
        )
    print(
        "global interval upper:",
        decimal(global_max[0], 18),
        "on cell",
        global_max[1],
        "; proved < -47/200",
    )
    print("tent derivative rows (r,side,K,K_ee,K_FF,ceil(1e9 error)):")
    for row in rows:
        print(" ", row)
    print("original exact tent error upper:", decimal(original_error, 20))
    print("proved exact T(q) < -117/500 on [0,1]")
    print("3a exact tent error upper:", decimal(triple_error, 20))
    print(
        "q=1/362, 3a center enclosure:",
        decimal(witness_center_lo, 20),
        decimal(witness_center_hi, 20),
    )
    print("q=1/362, exact 3a bracket lower:", decimal(witness_exact_lo, 20))
    print("proved exact 3a bracket > 739/1000")


if __name__ == "__main__":
    main()
