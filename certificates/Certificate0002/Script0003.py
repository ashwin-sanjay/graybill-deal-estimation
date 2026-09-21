#!/usr/bin/env python3
"""Exact rational interval certificate for the Part B two-bump competitor.

Every interval endpoint is a Fraction.  Square-root enclosures are obtained
by integer square roots and then checked by exact squaring.
"""

from fractions import Fraction as F
from math import isqrt

SQRT_DEN = 10**24


def sqrt_bounds(x: F):
    assert x > 0
    k = isqrt((x.numerator * SQRT_DEN * SQRT_DEN) // x.denominator)
    lo, hi = F(k, SQRT_DEN), F(k + 1, SQRT_DEN)
    assert lo * lo <= x <= hi * hi
    return lo, hi


def mul(i, j):
    vals = (i[0] * j[0], i[0] * j[1], i[1] * j[0], i[1] * j[1])
    return min(vals), max(vals)


def add(*xs):
    return sum((x[0] for x in xs), F(0)), sum((x[1] for x in xs), F(0))


def neg(i):
    return -i[1], -i[0]


def sub(i, j):
    return add(i, neg(j))


def div(i, j):
    assert j[0] > 0
    return mul(i, (1 / j[1], 1 / j[0]))


def weight_bounds(e: F, f: F, qlo: F, qhi: F):
    """Bounds C/N(q)^(5/2), C=sqrt(f/(e(1-e)))."""
    c = F(f, e * (1 - e))
    clo, chi = sqrt_bounds(c)
    # N=e+(1-2e+f)q-fq^2 is concave.  Its minimum is at an
    # endpoint; its maximum is at an endpoint or its vertex.
    def n(q):
        return e + (1 - 2 * e + f) * q - f * q * q

    vals = [n(qlo), n(qhi)]
    vertex = F(1 - 2 * e + f, 2 * f)
    if qlo <= vertex <= qhi:
        vals.append(n(vertex))
    nlo, nhi = min(vals), max(vals)
    snlo, _ = sqrt_bounds(nlo)
    _, snhi = sqrt_bounds(nhi)
    # monotonicity of C/(N^2 sqrt(N))
    wlo = clo / (nhi * nhi * snhi)
    whi = chi / (nlo * nlo * snlo)
    return wlo, whi


def weight_box(ei, fi, qi, mirror=False):
    """Natural exact interval extension of C/N^(5/2)."""
    one = (F(1), F(1))
    if mirror:
        ni_e = sub(one, ei)
    else:
        ni_e = ei
    eprod = mul(ei, sub(one, ei))
    crat = div(fi, eprod)
    clo, _ = sqrt_bounds(crat[0])
    _, chi = sqrt_bounds(crat[1])
    # N=e+q-2eq+fq(1-q), with e replaced by 1-e for mirror.
    nbox = add(ni_e, qi, neg(mul((F(2), F(2)), mul(ni_e, qi))),
               mul(fi, mul(qi, sub(one, qi))))
    if nbox[0] <= 0:
        return None
    snlo, _ = sqrt_bounds(nbox[0])
    _, snhi = sqrt_bounds(nbox[1])
    return clo / (nbox[1] * nbox[1] * snhi), chi / (nbox[0] * nbox[0] * snlo)


LA, FA = F(1, 500), F(1, 1000)
LB, FB = F(1, 120), F(20)
T = F(1, 10000)
C = F(1, 1000)


def affine_bounds(alpha: F, beta: F, qlo: F, qhi: F):
    a, b = alpha * qlo + beta, alpha * qhi + beta
    return min(a, b), max(a, b)


def gap_bounds(qlo: F, qhi: F):
    """Interval for L-C(S_A+S_B), notation in the accompanying proof."""
    ua = weight_bounds(LA, FA, qlo, qhi)
    va = weight_bounds(1 - LA, FA, qlo, qhi)
    ub = weight_bounds(LB, FB, qlo, qhi)
    vb = weight_bounds(1 - LB, FB, qlo, qhi)

    # Coefficients after expanding
    # Strong pointwise inequality
    # 4g_B-3g_A-(T/2)(9S_A+16S_B)-C(S_A+S_B).
    # It implies the desired integrated inequality because tent^2 <= tent.
    ca_u = affine_bounds(F(3), -3 * LA - F(9, 2) * T - C, qlo, qhi)
    ca_v = affine_bounds(F(-3), 3 * (1 - LA) - F(9, 2) * T - C, qlo, qhi)
    cb_u = affine_bounds(F(-4), 4 * LB - 8 * T - C, qlo, qhi)
    cb_v = affine_bounds(F(4), 4 * (LB - 1) - 8 * T - C, qlo, qhi)
    return add(mul(ca_u, ua), mul(ca_v, va), mul(cb_u, ub), mul(cb_v, vb))


RHO = F(1, 10**12)


def gap_box(qlo: F, qhi: F):
    """Same strong gap, now for every point in both rho-wide tents."""
    qi = (qlo, qhi)
    ea = (LA - RHO, LA + RHO)
    eb = (LB - RHO, LB + RHO)
    fa = (FA - RHO, FA + RHO)
    fb = (FB - RHO, FB + RHO)
    ua, va = weight_box(ea, fa, qi), weight_box(ea, fa, qi, True)
    ub, vb = weight_box(eb, fb, qi), weight_box(eb, fb, qi, True)
    if None in (ua, va, ub, vb):
        return None
    # Coefficients use the varying left center e; after pairing z with -z
    # the right coordinate is 1-e.
    ca_u = sub(mul((F(3), F(3)), sub(qi, ea)),
               (F(9,2)*T+C, F(9,2)*T+C))
    ca_v = sub(mul((F(3), F(3)), sub(sub((F(1),F(1)), ea), qi)),
               (F(9,2)*T+C, F(9,2)*T+C))
    cb_u = sub(mul((F(4), F(4)), sub(eb, qi)), (8*T+C, 8*T+C))
    cb_v = sub(mul((F(4), F(4)), sub(add(qi, eb), (F(1),F(1)))),
               (8*T+C, 8*T+C))
    return add(mul(ca_u, ua), mul(ca_v, va), mul(cb_u, ub), mul(cb_v, vb))


def certify(lo=F(0), hi=F(1, 2), max_depth=80, box=True):
    stack = [(lo, hi, 0)]
    leaves = []
    while stack:
        a, b, depth = stack.pop()
        gb = gap_box(a, b) if box else gap_bounds(a, b)
        if gb is not None and gb[0] > 0:
            leaves.append((a, b, gb[0]))
            continue
        if depth >= max_depth:
            raise RuntimeError((a, b, gb))
        m = (a + b) / 2
        stack.append((m, b, depth + 1))
        stack.append((a, m, depth + 1))
    leaves.sort()
    assert leaves[0][0] == lo and leaves[-1][1] == hi
    assert all(leaves[i][1] == leaves[i + 1][0] for i in range(len(leaves)-1))
    return leaves


if __name__ == "__main__":
    leaves = certify()
    print("certified leaves", len(leaves))
    print("maximum dyadic depth", max((b-a).denominator.bit_length()-1 for a,b,_ in leaves))
    print("exact leaf certificates (gap > displayed rational):")
    for a, b, g in leaves:
        floor_milli = g.numerator * 1000 // g.denominator
        print(a, b, ">", F(floor_milli, 1000))
    # Coarse bins: report the least exact lower bound among leaves meeting bin.
    bins = [F(0), F(1,10000), F(1,2000), F(1,1000), F(3,2000),
            F(1,500), F(1,250), F(1,120), F(1,100), F(1,20),
            F(1,10), F(1,5), F(3,10), F(2,5), F(1,2)]
    for x, y in zip(bins, bins[1:]):
        vals = [g for a,b,g in leaves if a < y and b > x]
        z = min(vals)
        print(f"[{float(x):.7g},{float(y):.7g}] leaves={len(vals):4d} lower>{float(z):.12g}")
