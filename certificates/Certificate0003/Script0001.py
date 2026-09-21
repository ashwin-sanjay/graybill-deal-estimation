#!/usr/bin/env python
"""Theorem A certificate (v2): rigorous numerical lower bounds for
D(eta) = R_eta(delta_GD) - R_eta(delta_H) at (n1,n2) = (11,11), m1 = m2 = 10.

Supersedes v1 (first-order brackets; failed at eta in {0.1,100,1000}).

EXACT IDENTITY CERTIFIED (full derivation + lemma proofs in Script0001.md):

  D(eta) = C0 * Int_{x>0} Int_{r>0} F(x,r) dx dr,
  C0     = 21!! / (294912 * eta^5 * sqrt(V)),   V = (1+eta)/11,  b = -1/(1+eta),
  F(x,r) = r^4 * Q^{-23/2} * (x*W_G - T1) * (x*W_G + T1 + 2*b*x),
  Q      = 1 + x^2/V + r/eta,   W_G = 1/(1+r),
  T1(x,r)= E[t] under the 1-d posterior pi(t) ~ (1+11 t^2)^{-11/2} (r+11(t-x)^2)^{-11/2}
           (both variances integrated out in closed form; W_H = T1/x).

21!! = 13749310575; Gamma(23/2)*2^{23/2} = 21!!*sqrt(2 pi) cancels the Gaussian
normalization, so every constant is rational or a sqrt of a rational.  The whole
computation uses only +,-,*,/,sqrt, all IEEE-754 correctly rounded, so outward
rounding by 1 ulp per operation yields unconditional enclosures.

Key structural lemmas (proved in the note):
  (L1) reflection lemma: 0 <= T1(x,r) <= x  (hence W_H in [0,1]); used to clamp
       enclosures and to bound |P| <= M0 x^2, M0 = max(b^2,(1+b)^2), in tails.
  (L2) closed-form outer tails in x (power decay from Q >= x^2/V) and in r
       (splits Q^{23/2} >= (1+x^2/V)^a (r/eta)^{23/2-a}); Beta constants rational.
  (L3) closed-form inner t-tails from monotone kernel comparison and the exact
       antiderivative of t (1+11 t^2)^{-11/2}.

Quadrature: composite MEAN-VALUE (centered) rule at both levels -- on a cell
[a,b] with float c in [a,b] and G an enclosure of f' on [a,b]:
  Int_a^b f  in  (b-a) f(c) + mid(G)*I1 + [-1,1]*rad(G)*I2,
  I1 = ((b-c)^2-(c-a)^2)/2 (~0),  I2 = ((b-c)^2+(c-a)^2)/2 = Int |t-c| dt.
This is 2nd order and needs no exact-midpoint assumption.  The outer 2-d cell
version applies the segment mean-value theorem coordinatewise; the required
gradient enclosures dF/dx, dF/dr involve dT1/dx, dT1/dr, which are again ratios
of explicit 1-d integrals (differentiation under the integral sign).
First moments are computed CENTERED at tc ~ T1 (a float), which removes the
catastrophic correlation loss of interval division A1/A0 across parameter cells.

Usage:
  uv run python Script0001.py --selftest
  uv run python Script0001.py                 # all five etas
  uv run python Script0001.py --etas 1 10 --Kx 80 --Kr 160
"""

import argparse
import time

import numpy as np

U = float(np.float64(2.0) ** -53)  # unit roundoff


def _up(a):
    return np.nextafter(a, np.inf)


def _dn(a):
    return np.nextafter(a, -np.inf)


class IV:
    """Intervals with outward rounding (element-wise over numpy arrays)."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = np.asarray(lo, dtype=np.float64)
        self.lo = lo
        self.hi = lo if hi is None else np.asarray(hi, dtype=np.float64)

    @staticmethod
    def _c(o):
        return o if isinstance(o, IV) else IV(np.float64(o))

    def width(self):
        return self.hi - self.lo

    def mag(self):
        return np.maximum(np.abs(self.lo), np.abs(self.hi))

    def __add__(self, o):
        o = IV._c(o)
        return IV(_dn(self.lo + o.lo), _up(self.hi + o.hi))

    __radd__ = __add__

    def __sub__(self, o):
        o = IV._c(o)
        return IV(_dn(self.lo - o.hi), _up(self.hi - o.lo))

    def __rsub__(self, o):
        return IV._c(o).__sub__(self)

    def __neg__(self):
        return IV(-self.hi, -self.lo)

    def __mul__(self, o):
        o = IV._c(o)
        a = self.lo * o.lo
        b = self.lo * o.hi
        c = self.hi * o.lo
        d = self.hi * o.hi
        return IV(_dn(np.minimum(np.minimum(a, b), np.minimum(c, d))),
                  _up(np.maximum(np.maximum(a, b), np.maximum(c, d))))

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = IV._c(o)
        if not np.all((o.lo > 0) | (o.hi < 0)):
            raise ZeroDivisionError("interval denominator straddles 0")
        a = self.lo / o.lo
        b = self.lo / o.hi
        c = self.hi / o.lo
        d = self.hi / o.hi
        return IV(_dn(np.minimum(np.minimum(a, b), np.minimum(c, d))),
                  _up(np.maximum(np.maximum(a, b), np.maximum(c, d))))

    def __rtruediv__(self, o):
        return IV._c(o).__truediv__(self)

    def sq(self):
        a = self.lo * self.lo
        b = self.hi * self.hi
        lo = np.where((self.lo <= 0) & (self.hi >= 0), 0.0,
                      _dn(np.minimum(a, b)))
        return IV(lo, _up(np.maximum(a, b)))

    def sqrt(self):
        if not np.all(self.lo >= 0):
            raise ValueError("sqrt of interval with negative part")
        return IV(_dn(np.sqrt(self.lo)), _up(np.sqrt(self.hi)))

    def ipow(self, n):
        r = self
        for _ in range(int(n) - 1):
            r = r * self
        return r

    def pow_m55(self):
        """z^{-11/2} for z > 0."""
        return 1.0 / (self.ipow(5) * self.sqrt())

    def clamp(self, lo, hi):
        nl = np.maximum(self.lo, lo)
        nh = np.minimum(self.hi, hi)
        if not np.all(nl <= nh):
            raise ValueError("empty intersection in clamp -- lemma violated?")
        return IV(nl, nh)


def sym(u):
    """[-u, u] from a rigorous nonnegative upper-bound float array."""
    u = np.asarray(u, dtype=np.float64)
    return IV(-u, u)


def sum_iv(v, axis=-1):
    """Enclosure of sum of interval entries incl. fl-summation error:
    |fl(sum) - sum| <= gamma_n sum|x_i|, gamma_n = n u/(1-n u)  (Higham)."""
    n = v.lo.shape[axis]
    slo = v.lo.sum(axis=axis)
    shi = v.hi.sum(axis=axis)
    sab = v.mag().sum(axis=axis)
    e = _up((n * U) / (1.0 - n * U) * 1.05 * sab)
    return IV(_dn(slo - e), _up(shi + e))


def mid_rad(G):
    gm = 0.5 * (G.lo + G.hi)
    rho = np.maximum(_up(G.hi - gm), _up(gm - G.lo))
    return gm, rho


# ---------------------------------------------------------------------------
# constants (n1 = n2 = 11, m1 = m2 = 10, nu = 11/2)
# ---------------------------------------------------------------------------
DF21 = 13749310575.0          # 21!!, exact in float64
B_5_132 = 7983360.0           # B(5,13/2)*21!!  (rational numerator)
B_32_10 = 371589120.0         # B(3/2,10)*21!!


def eta_iv(eta_str):
    from fractions import Fraction
    fr = Fraction(eta_str)
    return IV(float(fr.numerator)) / IV(float(fr.denominator))


class Consts:
    def __init__(self, eta_str):
        self.eta = eta_iv(eta_str)
        self.V = (1.0 + self.eta) / 11.0
        self.b = IV(-1.0) / (1.0 + self.eta)
        self.C0 = IV(DF21) / (294912.0 * self.eta.ipow(5) * self.V.sqrt())
        self.M0 = np.maximum(self.b.sq().hi, (1.0 + self.b).sq().hi)


# ---------------------------------------------------------------------------
# inner 1-d integrals over t
# ---------------------------------------------------------------------------
def kernels(t, x, r, tc, need_B):
    """g and dg/dt for the integrands. t,x,r,tc: IV broadcastable together.
    pi = (A B)^{-11/2}, A = 1+11 t^2, B = r+11 (t-x)^2.
    A0: pi;  A1: (t-tc) pi;  B0x: pi chix;  B1x: (t-tc) pi chix;
    B0r: pi chir;  B1r: (t-tc) pi chir;
    chix = 121 (t-x)/B = d log pi/dx,  chir = -5.5/B = d log pi/dr,
    chit = -121 t/A - 121 (t-x)/B     = d log pi/dt."""
    u = t - x
    usq = u.sq()
    A = 1.0 + 11.0 * t.sq()
    B = r + 11.0 * usq
    pi = (A * B).pow_m55()
    chit = -121.0 * (t / A + u / B)
    dt = t - tc
    out = {"A0": (pi, pi * chit),
           "A1": (dt * pi, pi * (1.0 + dt * chit))}
    if need_B:
        Bsq = B.sq()
        chix = 121.0 * u / B
        chixp = 121.0 * (r - 11.0 * usq) / Bsq
        chir = -5.5 / B
        chirp = 121.0 * u / Bsq
        gx = chit * chix + chixp
        gr = chit * chir + chirp
        out["B0x"] = (pi * chix, pi * gx)
        out["B1x"] = (dt * pi * chix, pi * (chix + dt * gx))
        out["B0r"] = (pi * chir, pi * (chir + dt * gr))  # placeholder fixed below
        out["B0r"] = (pi * chir, pi * gr)
        out["B1r"] = (dt * pi * chir, pi * (chir + dt * gr))
    return out


def inner_tails(x, r, tlo, thi, need_B):
    """Upper bounds for |int_{t notin [tlo,thi]} g dt| (Lemma L3).
    Requires thi > max(x.hi,0), tlo < min(x.lo,0) -- checked."""
    if not (np.all(thi > np.maximum(x.hi, 0.0))
            and np.all(tlo < np.minimum(x.lo, 0.0))):
        raise ValueError("t-range does not bracket both kernel centers")
    tloI, thiI = IV(tlo), IV(thi)

    def dec9(T):  # (1+11 T^2)^{-9/2}
        z = 1.0 + 11.0 * T.sq()
        return 1.0 / (z.ipow(4) * z.sqrt())

    K2R = (r + 11.0 * (thiI - x).sq()).pow_m55()
    K2L = (r + 11.0 * (tloI - x).sq()).pow_m55()
    m1R = K2R * dec9(thiI) * (1.0 / 99.0)
    m1L = K2L * dec9(tloI) * (1.0 / 99.0)
    m0R = m1R / thiI
    m0L = m1L / (-tloI)
    t0 = (m0R + m0L).hi
    # first-moment integrand is (t - tc) pi with tc in [0, x] (Lemma L1):
    # right tail: |t - tc| <= t (t >= thi > x >= tc >= 0);
    # left tail:  |t - tc| <= |t| + tc <= |t| + x.hi
    t1 = (m1R + m1L + IV(np.maximum(x.hi, 0.0)) * m0L).hi
    out = {"A0": t0, "A1": t1}
    if need_B:
        fx = (121.0 / (2.0 * (11.0 * r).sqrt())).hi
        fr = (5.5 / r).hi
        out["B0x"] = _up(fx * t0)
        out["B1x"] = _up(fx * t1)
        out["B0r"] = _up(fr * t0)
        out["B1r"] = _up(fr * t1)
    return out


def build_nodes(x0, r0, K, extra=0.0):
    """Two sinh-graded grids centered on the kernel centers (0 and x0), merged.
    Node choice is heuristic float math; rigor never depends on it."""
    x0 = np.atleast_1d(np.asarray(x0, dtype=np.float64))
    r0 = np.atleast_1d(np.asarray(r0, dtype=np.float64))
    sc1 = np.full_like(x0, 1.0 / np.sqrt(110.0))
    sc2 = np.sqrt(r0 / 110.0)
    reach = 3.0 + 3.0 * np.abs(x0) + 30.0 * (sc1 + sc2) + extra
    K1 = max(K // 2, 8)
    y = np.linspace(-1.0, 1.0, K1 + 1)
    g1 = sc1[:, None] * np.sinh(np.arcsinh(reach / sc1)[:, None] * y)
    g2 = x0[:, None] + sc2[:, None] * np.sinh(np.arcsinh(reach / sc2)[:, None] * y)
    return np.sort(np.concatenate([g1, g2], axis=-1), axis=-1)


def float_tc(x0, r0, nodes):
    """Cheap float estimate of T1 (centering constant only)."""
    t = 0.5 * (nodes[:, :-1] + nodes[:, 1:])
    h = np.diff(nodes, axis=-1)
    logpi = -5.5 * (np.log1p(11.0 * t * t)
                    + np.log(r0[:, None] + 11.0 * (t - x0[:, None]) ** 2))
    logpi -= logpi.max(axis=-1, keepdims=True)
    w = np.exp(logpi) * h
    tc = (w * t).sum(-1) / w.sum(-1)
    return np.clip(tc, 0.0, x0)


def composite(nodes, x, r, tc, need_B):
    """Mean-value composite quadrature of all integrands over [tlo,thi] plus
    tail enclosures.  nodes: (M,Kn); x, r, tc: IV/(float) of shape (M,)."""
    a = nodes[:, :-1]
    bb = nodes[:, 1:]
    c = 0.5 * (a + bb)
    x2 = IV(x.lo[:, None], x.hi[:, None])
    r2 = IV(r.lo[:, None], r.hi[:, None])
    tc2 = IV(tc[:, None])
    tcell = IV(a, bb)
    tpt = IV(c)
    h = IV(bb) - IV(a)
    I1 = ((IV(bb) - IV(c)).sq() - (IV(c) - IV(a)).sq()) * 0.5
    I2 = (((IV(bb) - IV(c)).sq() + (IV(c) - IV(a)).sq()) * 0.5).hi
    kp = kernels(tpt, x2, r2, tc2, need_B)
    kc = kernels(tcell, x2, r2, tc2, need_B)
    tails = inner_tails(x, r, nodes[:, 0], nodes[:, -1], need_B)
    out = {}
    for name, (g, _) in kp.items():
        gm, rho = mid_rad(kc[name][1])
        mv = h * g + IV(gm) * I1 + sym(_up(rho * I2))
        fo = h * kc[name][0]          # first-order enclosure (same cells)
        both = IV(np.maximum(mv.lo, fo.lo), np.minimum(mv.hi, fo.hi))
        if not np.all(both.lo <= both.hi):
            raise RuntimeError("mean-value and first-order enclosures disjoint")
        out[name] = sum_iv(both, axis=-1) + sym(tails[name])
    return out


# ---------------------------------------------------------------------------
# outer tails (Lemma L2)
# ---------------------------------------------------------------------------
def outer_tails(cn, X, Rlo, Rhi):
    """Upper bound on |Int outside [0,X]x[Rlo,Rhi] of F|  (F-units)."""
    eta, V, M0 = cn.eta, cn.V, IV(cn.M0)
    B5132 = IV(B_5_132) / DF21
    B3210 = IV(B_32_10) / DF21
    V32 = V * V.sqrt()
    V132 = V.ipow(6) * V.sqrt()
    Tx = M0 * eta.ipow(5) * B5132 * V132 / (10.0 * IV(X).ipow(10))
    Trhi = M0 * eta.ipow(9) * V32 / (12.0 * IV(Rhi).ipow(4))
    Trlo = M0 * IV(Rlo).ipow(5) * V32 * B3210 / 10.0
    return _up((Tx + Trhi + Trlo).hi), (Tx.hi, Trhi.hi, Trlo.hi)


# ---------------------------------------------------------------------------
# explicit part:  D_G/C0 = (1/2) B(3/2,10) V^{3/2} * I_G,
#   I_G = Int_0^inf r^4 psi(r)^2 (1+r/eta)^{-10} dr,  psi = 1/(1+r) + b.
# (x-integral in closed form: Int_0^inf x^2 (c+x^2/V)^{-23/2} dx
#   = V^{3/2} c^{-10} (1/2) B(3/2,10).)   1-d mean-value composite + tails.
# ---------------------------------------------------------------------------
def IG_certify(cn, K1d=40000, tolfac=1e-9):
    eta, b = cn.eta, cn.b
    eta_f = 0.5 * (eta.lo + eta.hi)
    b2 = float(cn.b.sq().hi)
    # tail:  for r >= R >= eta, psi^2 <= b^2 and (1+r/eta)^{-10} <= (r/eta)^{-10}
    # so tail <= b^2 eta^10 R^{-5} / 5.  choose R for tail ~ tolfac * I_G-scale
    Iscale = max(eta_f ** 5 * 1e-3, 1e-300)
    R = max(2.0 * eta_f, (b2 * eta_f ** 10 / (5.0 * tolfac * Iscale)) ** 0.2)
    r1 = R * 1e-9
    nodes = np.geomspace(r1, R, K1d + 1)[None, :]

    def g_and_gp(r):
        one_p = 1.0 + r
        psi = 1.0 / one_p + b
        phi_base = 1.0 + r / eta
        phi = 1.0 / (phi_base.ipow(10))
        r2 = r.sq()
        r3 = r2 * r
        r4 = r2.sq()
        g = r4 * psi.sq() * phi
        gp = (4.0 * r3 * psi.sq() * phi
              - 2.0 * r4 * psi * phi / one_p.sq()
              - (10.0 / eta) * r4 * psi.sq() / phi_base.ipow(11))
        return g, gp

    a = nodes[:, :-1]
    bb = nodes[:, 1:]
    c = 0.5 * (a + bb)
    g_c, _ = g_and_gp(IV(c))
    _, gp_cell = g_and_gp(IV(a, bb))
    g_cell, _ = g_and_gp(IV(a, bb))
    h = IV(bb) - IV(a)
    I1 = ((IV(bb) - IV(c)).sq() - (IV(c) - IV(a)).sq()) * 0.5
    I2 = (((IV(bb) - IV(c)).sq() + (IV(c) - IV(a)).sq()) * 0.5).hi
    gm, rho = mid_rad(gp_cell)
    mv = h * g_c + IV(gm) * I1 + sym(_up(rho * I2))
    fo = h * g_cell
    both = IV(np.maximum(mv.lo, fo.lo), np.minimum(mv.hi, fo.hi))
    IG = sum_iv(both, axis=-1)
    IG = IV(float(IG.lo), float(IG.hi))
    # head [0, r1]: integrand <= r^4 (1+b)^2 ; tail [R, inf) as above
    head = (1.0 + b).sq() * IV(r1).ipow(5) / 5.0
    tail = cn.b.sq() * eta.ipow(10) / (5.0 * IV(R).ipow(5))
    IG = IG + IV(0.0, _up((head + tail).hi))
    B3210 = IV(B_32_10) / DF21
    return 0.5 * B3210 * cn.V * cn.V.sqrt() * IG


# ---------------------------------------------------------------------------
# certification driver
# ---------------------------------------------------------------------------
def certify(eta_str, D_est, Kx=120, Kr=240, Kin=1024, Kgrad=192,
            chunk=512, tail_frac=50.0, width_frac=0.35, max_rounds=12,
            split_frac=0.85, verbose=True):
    t_start = time.time()
    cn = Consts(eta_str)
    eta_f = 0.5 * (cn.eta.lo + cn.eta.hi)
    V_f = 0.5 * (cn.V.lo + cn.V.hi)
    C0_f = 0.5 * (cn.C0.lo + cn.C0.hi)
    M0_f = float(cn.M0)

    # ---- domain extents from float tail targets; verified rigorously below
    targF = (D_est / tail_frac) / C0_f
    X = (M0_f * eta_f ** 5 * (B_5_132 / DF21) * V_f ** 6.5 / (10 * targF)) ** 0.1
    X = max(X, 6.0 * np.sqrt(V_f))
    Rhi = (M0_f * eta_f ** 9 * V_f ** 1.5 / (12 * targF)) ** 0.25
    Rhi = max(Rhi, 50.0 * eta_f)
    Rlo = (10 * targF / (M0_f * V_f ** 1.5 * (B_32_10 / DF21))) ** 0.2
    Rlo = min(Rlo, eta_f / 50.0)
    tail_tot, tail_parts = outer_tails(cn, X, Rlo, Rhi)

    xs = np.linspace(0.0, X, Kx + 1)
    rs = np.geomspace(Rlo, Rhi, Kr + 1)
    xa = np.repeat(xs[:-1], Kr)
    xb = np.repeat(xs[1:], Kr)
    ra = np.tile(rs[:-1], Kx)
    rb = np.tile(rs[1:], Kx)
    N = xa.size

    def cells_enclosure(cxa, cxb, cra, crb):
        """Rigorous enclosure of Int_cell F_H for a batch of cells.
        Returns (cell IV array, remainder-width float array)."""
        x0 = 0.5 * (cxa + cxb)
        r0 = 0.5 * (cra + crb)

        # tight point evaluation F_H(x0, r0)
        nodes = build_nodes(x0, r0, Kin)
        tc = float_tc(x0, r0, nodes)
        res = composite(nodes, IV(x0), IV(r0), tc, need_B=False)
        A0, A1 = res["A0"], res["A1"]
        if not np.all(A0.lo > 0):
            raise RuntimeError("point A0 enclosure not positive; raise Kin")
        T1 = (IV(tc) + A1 / A0).clamp(0.0, x0)           # Lemma L1
        Q0 = 1.0 + IV(x0).sq() / cn.V + IV(r0) / cn.eta
        base0 = IV(r0).ipow(4) / (Q0.ipow(11) * Q0.sqrt())
        S0 = T1 + cn.b * IV(x0)          # = x (W_H + b), in [b x, (1+b) x]
        F0 = base0 * S0.sq()             # F_H at the cell center  (>= 0)

        # gradient enclosure of F_H over the cell
        xC = IV(cxa, cxb)
        rC = IV(cra, crb)
        gnodes = build_nodes(x0, r0, Kgrad, extra=(cxb - cxa))
        resc = composite(gnodes, xC, rC, tc, need_B=True)
        cA0, cA1 = resc["A0"], resc["A1"]
        if not np.all(cA0.lo > 0):
            raise RuntimeError("cell A0 enclosure not positive; raise Kgrad")
        T1crude = (IV(tc) + cA1 / cA0).clamp(0.0, cxb)
        dT = T1crude - IV(tc)
        dxT1 = (resc["B1x"] - dT * resc["B0x"]) / cA0
        drT1 = (resc["B1r"] - dT * resc["B0r"]) / cA0
        T1mv = T1 + dxT1 * (xC - IV(x0)) + drT1 * (rC - IV(r0))
        T1c = IV(np.maximum(T1mv.lo, T1crude.lo),
                 np.minimum(T1mv.hi, T1crude.hi)).clamp(0.0, cxb)
        dT = T1c - IV(tc)
        dxT1 = (resc["B1x"] - dT * resc["B0x"]) / cA0
        drT1 = (resc["B1r"] - dT * resc["B0r"]) / cA0

        Qc = 1.0 + xC.sq() / cn.V + rC / cn.eta
        basec = rC.ipow(4) / (Qc.ipow(11) * Qc.sqrt())
        Sc = T1c + cn.b * xC
        Sc = IV(np.maximum(Sc.lo, (cn.b * xC).lo),
                np.minimum(Sc.hi, ((1.0 + cn.b) * xC).hi))
        ax = (-23.0) * xC / (cn.V * Qc)
        ar = 4.0 / rC - 11.5 / (cn.eta * Qc)
        Gx = basec * (ax * Sc.sq() + 2.0 * Sc * (dxT1 + cn.b))
        Gr = basec * (ar * Sc.sq() + 2.0 * Sc * drT1)

        # assemble 2-d mean-value cell enclosure
        wx = IV(cxb) - IV(cxa)
        wr = IV(crb) - IV(cra)
        area = wx * wr
        I1x = ((IV(cxb) - IV(x0)).sq() - (IV(x0) - IV(cxa)).sq()) * 0.5
        I2x = (((IV(cxb) - IV(x0)).sq() + (IV(x0) - IV(cxa)).sq()) * 0.5).hi
        I1r = ((IV(crb) - IV(r0)).sq() - (IV(r0) - IV(cra)).sq()) * 0.5
        I2r = (((IV(crb) - IV(r0)).sq() + (IV(r0) - IV(cra)).sq()) * 0.5).hi
        gmx, rhox = mid_rad(Gx)
        gmr, rhor = mid_rad(Gr)
        remx = (IV(gmx) * I1x + sym(_up(rhox * I2x))) * wr
        remr = (IV(gmr) * I1r + sym(_up(rhor * I2r))) * wx
        cell = area * F0 + remx + remr
        # F_H >= 0 and the first-order enclosure is also valid: intersect
        fo_cell = area * (basec * Sc.sq())
        cell = IV(np.maximum(cell.lo, 0.0), np.minimum(cell.hi, fo_cell.hi))
        if not np.all(cell.lo <= cell.hi):
            raise RuntimeError("cell enclosures disjoint")
        return cell, cell.width(), remx.width(), remr.width()

    # ---------- adaptive certification loop ----------
    # target remainder (in F-units) for the D_H box sum
    targ_width = (D_est * width_frac) / C0_f
    lo_parts, hi_parts = [], []          # finished (narrow) cells
    work = (xa, xb, ra, rb)              # current worklist
    n_evals = 0
    for rnd in range(max_rounds):
        wl_lo, wl_hi, wl_w, wl_wx, wl_wr = [], [], [], [], []
        cxa, cxb, cra, crb = work
        for i0 in range(0, cxa.size, chunk):
            sl = slice(i0, min(i0 + chunk, cxa.size))
            cell, wdt, rxw, rrw = cells_enclosure(
                cxa[sl], cxb[sl], cra[sl], crb[sl])
            wl_lo.append(cell.lo); wl_hi.append(cell.hi); wl_w.append(wdt)
            wl_wx.append(rxw); wl_wr.append(rrw)
            n_evals += cxa[sl].size
        wl_lo = np.concatenate(wl_lo); wl_hi = np.concatenate(wl_hi)
        wl_w = np.concatenate(wl_w)
        wl_wx = np.concatenate(wl_wx); wl_wr = np.concatenate(wl_wr)
        done_w = sum(float(w.sum()) for w in
                     ([np.array([0.0])] if not lo_parts else
                      [h - l for l, h in zip(lo_parts, hi_parts)]))
        tot_w = float(wl_w.sum()) + done_w
        if verbose:
            print(f"    round {rnd}: cells={cxa.size} total-width(F-units)="
                  f"{tot_w:.3e} (target {targ_width:.3e})")
        if tot_w <= targ_width or rnd == max_rounds - 1:
            lo_parts.append(wl_lo); hi_parts.append(wl_hi)
            break
        # retire only cells whose aggregate width fits in a small budget
        # (<= 0.2*target over ALL rounds); split everything else
        order = np.argsort(wl_w)          # ascending
        cum = np.cumsum(wl_w[order])
        budget = 0.2 * targ_width / max_rounds
        ncold = int(np.searchsorted(cum, budget))
        cold = np.zeros(wl_w.size, dtype=bool)
        cold[order[:ncold]] = True
        hot = order[ncold:]
        lo_parts.append(wl_lo[cold]); hi_parts.append(wl_hi[cold])
        # anisotropic subdivision: halve the direction whose remainder
        # dominates (rem_x ~ wx^3, rem_r ~ wr^3: 4x gain per 2x cells)
        ha, hb = cxa[hot], cxb[hot]
        hra, hrb = cra[hot], crb[hot]
        splitx = wl_wx[hot] >= wl_wr[hot]
        hm = 0.5 * (ha + hb)
        hrm = np.sqrt(hra * hrb)
        # x-split children
        xa1 = np.concatenate([ha[splitx], hm[splitx]])
        xb1 = np.concatenate([hm[splitx], hb[splitx]])
        ra1 = np.concatenate([hra[splitx], hra[splitx]])
        rb1 = np.concatenate([hrb[splitx], hrb[splitx]])
        # r-split children
        sr = ~splitx
        xa2 = np.concatenate([ha[sr], ha[sr]])
        xb2 = np.concatenate([hb[sr], hb[sr]])
        ra2 = np.concatenate([hra[sr], hrm[sr]])
        rb2 = np.concatenate([hrm[sr], hrb[sr]])
        work = (np.concatenate([xa1, xa2]), np.concatenate([xb1, xb2]),
                np.concatenate([ra1, ra2]), np.concatenate([rb1, rb2]))

    all_lo = np.concatenate(lo_parts)
    all_hi = np.concatenate(hi_parts)
    S = sum_iv(IV(all_lo, all_hi), axis=-1)
    S = IV(S.lo.reshape(()).item(), S.hi.reshape(()).item())
    dg = dict(wF0=float((all_hi - all_lo).sum()), rem=0.0,
              Smid=float(all_lo.sum()), n_evals=n_evals)

    # D = C0 * (IG_part - int F_H),  int F_H in [S.lo, S.hi + tail_tot]
    IGpart = IG_certify(cn)
    SH_full = IV(float(S.lo), _up(float(S.hi) + float(tail_tot)))
    D = cn.C0 * (IGpart - SH_full)
    el = time.time() - t_start
    if verbose:
        DG = cn.C0 * IGpart
        DH = cn.C0 * SH_full
        print(f"eta={eta_str:>6}: certified D in [{float(D.lo):+.6e},"
              f" {float(D.hi):+.6e}]  (width {float(D.hi - D.lo):.2e})")
        print(f"    D_G in [{float(DG.lo):.9e}, {float(DG.hi):.9e}] "
              f" D_H in [{float(DH.lo):.9e}, {float(DH.hi):.9e}]")
        print(f"    grids: Kx={Kx} Kr={Kr} Kin={Kin} Kgrad={Kgrad}"
              f"  X={X:.3f} Rlo={Rlo:.3e} Rhi={Rhi:.3e}  [{el:.0f}s]")
        print(f"    diag: total box width(F-units)={dg['wF0']:.2e}"
              f"  cell evals={dg['n_evals']}"
              f"  outer-tail(F-units)={float(tail_tot):.2e}"
              f"  (x:{float(tail_parts[0]):.1e} rhi:{float(tail_parts[1]):.1e}"
              f" rlo:{float(tail_parts[2]):.1e})")
        ok = ("POSITIVE -- certified" if float(D.lo) > 0 else "NOT positive")
        print(f"    ==> D({eta_str}) >= {float(D.lo):+.6e}   [{ok}]")
    return float(D.lo), float(D.hi)


# ---------------------------------------------------------------------------
# self tests
# ---------------------------------------------------------------------------
def selftest():
    import mpmath
    from mpmath import iv as miv
    miv.prec = 113
    rng = np.random.default_rng(0)
    nops = 0
    for _ in range(1500):
        a = np.sort(rng.normal(scale=10.0, size=2))
        b = np.sort(rng.normal(scale=10.0, size=2))
        A, B = IV(a[0], a[1]), IV(b[0], b[1])
        mA = miv.mpf([a[0], a[1]])
        mB = miv.mpf([b[0], b[1]])
        checks = [(A + B, mA + mB), (A - B, mA - mB), (A * B, mA * mB),
                  (A.ipow(5), mA ** 5), (A.sq(), mA ** 2)]
        if b[0] > 0 or b[1] < 0:
            checks.append((A / B, mA / mB))
        if a[0] > 0:
            checks.append((A.sqrt(), miv.sqrt(mA)))
            checks.append((A.pow_m55(), 1 / (mA ** 5 * miv.sqrt(mA))))
        for got, want in checks:
            assert float(got.lo) <= float(mpmath.mpf(want.a)), (got.lo, want)
            assert float(got.hi) >= float(mpmath.mpf(want.b)), (got.hi, want)
            nops += 1
    mp = mpmath.mp
    mp.dps = 40
    g = mp.gamma(mp.mpf(23) / 2) * mp.mpf(2) ** (mp.mpf(23) / 2)
    assert abs(g / mp.sqrt(2 * mp.pi) - DF21) < 1e-25 * DF21
    assert abs(mp.beta(5, mp.mpf(13) / 2) - mp.mpf(B_5_132) / int(DF21)) < 1e-30
    assert abs(mp.beta(mp.mpf(3) / 2, 10) - mp.mpf(B_32_10) / int(DF21)) < 1e-30
    # summation lemma smoke test
    v = IV(rng.normal(size=10000))
    s = sum_iv(v)
    import math
    exact = math.fsum(v.lo.tolist())
    assert s.lo <= exact <= s.hi
    print(f"selftest passed ({nops} interval-op enclosure checks, constants OK)")


D_EST = {"0.1": 8.6e-6, "1": 1.87e-4, "10": 8.6e-5,
         "100": 1.39e-4, "1000": 1.83e-5}

PARAMS = {
    "0.1":  dict(Kx=120, Kr=240, Kin=1024, Kgrad=192),
    "1":    dict(Kx=120, Kr=240, Kin=1024, Kgrad=192),
    "10":   dict(Kx=120, Kr=240, Kin=1024, Kgrad=192),
    "100":  dict(Kx=120, Kr=240, Kin=1024, Kgrad=192),
    "1000": dict(Kx=120, Kr=240, Kin=1024, Kgrad=192),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--etas", nargs="*",
                    default=["0.1", "1", "10", "100", "1000"])
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--Kx", type=int, default=0)
    ap.add_argument("--Kr", type=int, default=0)
    ap.add_argument("--Kin", type=int, default=0)
    ap.add_argument("--Kgrad", type=int, default=0)
    ap.add_argument("--chunk", type=int, default=512)
    args = ap.parse_args()
    if args.selftest:
        selftest()
        return
    results = {}
    for e in args.etas:
        p = dict(PARAMS.get(e, dict(Kx=120, Kr=240, Kin=1024, Kgrad=192)))
        for k in ("Kx", "Kr", "Kin", "Kgrad"):
            if getattr(args, k):
                p[k] = getattr(args, k)
        results[e] = certify(e, D_EST.get(e, 1e-5), chunk=args.chunk, **p)
    print("\nSUMMARY -- certified enclosures of D(eta) = R_GD - R_H at (11,11):")
    for e, (lo, hi) in results.items():
        tag = "D>0 CERTIFIED" if lo > 0 else "INCONCLUSIVE"
        print(f"  eta={e:>6}:  D in [{lo:+.6e}, {hi:+.6e}]   {tag}")
    import json
    import os
    out = [{"eta": e, "D_lo": lo, "D_hi": hi, "certified": lo > 0}
           for e, (lo, hi) in results.items()]
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "theoremA_certificates_v2.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
