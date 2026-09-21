#!/usr/bin/env python3
"""Directed-rounded sinc certificates for the compact double-Haar integrals.

The program uses the exact logit form of the Dirichlet--Feynman reduction.
There are no empirical grid-error estimates in this file.  Infinite
trapezoid errors follow from strip analyticity and are bounded by explicit
Poisson/contour estimates; omitted lattice tails are bounded by geometric
series.  All sampled arithmetic and all finite sums use outward-rounded IEEE
intervals.  Arb rounds both sampled exponentials and transcendental error
constants outward.

The default lattice spacings are dyadic.  Consequently every sampled logit is
represented exactly as a binary floating-point number.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import time

from flint import arb, ctx
import numpy as np

from Script0001 import IV, _dn, _up, sum_iv, sym


P = Fraction(21, 2)
CT_NUM, CT_DEN = 4849845, 131072       # B(3/2,10)^-1
CS = 630                               # B(5,5)^-1


_EXP_CACHE: dict[float, tuple[float, float]] = {}


def _arb_exp_float_bounds(x: float) -> tuple[float, float]:
    """Rigorous binary64 bounds for exp of the *exact* binary64 ``x``.

    C/Python ``exp`` is not specified to be correctly rounded.  Every
    transcendental sample in the replay is therefore routed through Arb.
    The input float is embedded by its exact integer ratio, not by a decimal
    string conversion.  Results are cached because all sinc nodes lie on
    three fixed dyadic lattices.
    """
    x=float(x)
    if x in _EXP_CACHE:
        return _EXP_CACHE[x]
    old=ctx.prec;ctx.prec=192
    try:
        n,d=x.as_integer_ratio()
        y=(arb(n)/d).exp()
        ans=(arb_lower(y),arb_upper(y))
        _EXP_CACHE[x]=ans
        return ans
    finally:
        ctx.prec=old


def _arb_exp_array(values: np.ndarray, upper: bool) -> np.ndarray:
    values=np.asarray(values,dtype=np.float64)
    unique,inverse=np.unique(values,return_inverse=True)
    bounds=np.array([_arb_exp_float_bounds(float(x))[int(upper)] for x in unique])
    return bounds[inverse].reshape(values.shape)


def iv_exp(x: IV) -> IV:
    return IV(_arb_exp_array(x.lo,False),_arb_exp_array(x.hi,True))


def rational_iv(x: Fraction | str | int) -> IV:
    q = Fraction(x)
    old=ctx.prec;ctx.prec=192
    try:
        y=arb(q.numerator)/q.denominator
        return IV(arb_lower(y),arb_upper(y))
    finally:ctx.prec=old


def arb_upper(x: arb) -> float:
    """A binary64 strictly above an Arb upper endpoint."""
    return float(np.nextafter(float(x.upper()), math.inf))


def arb_lower(x: arb) -> float:
    """A binary64 strictly below an Arb lower endpoint."""
    return float(np.nextafter(float(x.lower()), -math.inf))


def positive_constant_ball(x: arb) -> IV:
    return IV(max(0.0, arb_lower(x)), arb_upper(x))


def _scalar_sum(v: IV) -> IV:
    return sum_iv(IV(np.ravel(v.lo), np.ravel(v.hi)))


def qmax(parity: int) -> IV:
    """Exact maximum of h(1-h)|h-1/2|^parity on [0,1]."""
    if parity == 1:
        return IV(1) / (IV(12) * IV(3).sqrt())
    if parity == 3:
        return (IV(3) / IV(20)).sqrt().ipow(3) / IV(10)
    raise ValueError("only odd parities 1 and 3 are used")


def inner_sinc_constants(step: Fraction, strip: Fraction) -> dict[str, float]:
    """Rigorous relative infinite-trapezoid error for both inner moments."""
    old = ctx.prec
    ctx.prec = 192
    try:
        h = arb(step.numerator) / step.denominator
        d = arb(strip.numerator) / strip.denominator
        p = arb(21) / 2
        kappa = (1 / d.cos()) ** p
        eps = 2 * kappa / ((2 * arb.pi() * d / h).exp() - 1)
        return {"kappa_upper": arb_upper(kappa), "epsilon_upper": arb_upper(eps)}
    finally:
        ctx.prec = old


def _grid(lo_index: int, hi_index: int, denominator: int) -> np.ndarray:
    # Division by a power of two is exact for the default denominators.
    ans = np.arange(lo_index, hi_index + 1, dtype=np.float64) / denominator
    if denominator & (denominator - 1):
        raise ValueError("the rigorous replay requires a dyadic grid denominator")
    return ans


def inner_haar_sinc(
    a: IV,
    b: IV,
    eta: IV,
    *,
    c_lo_index: int = -192,
    c_hi_index: int = 192,
    c_denominator: int = 8,
    strip: Fraction = Fraction(3, 4),
) -> IV:
    """Enclose H_eta at arrays of real outer-logit points.

    The lambda-logit lattice is c=k/8, -24<=c<=24 by default.  For

      Q=e^b + L e^c + eta e^(2c),

    the two unnormalised moments are

      f0=e^(11c/2)(1+e^c)^10 Q^(-21/2),
      f1=e^(13c/2)(1+e^c)^9  Q^(-21/2).

    On |Im c|=d<pi/2, rotating Q by exp(-i Im c) gives
    |f_j(c+id)| <= sec(d)^(21/2) f_j(c).  The returned ratio therefore
    includes both the infinite-trapezoid error and exact geometric bounds for
    the two omitted lattice tails.
    """
    rows = np.size(a.lo)
    c = _grid(c_lo_index, c_hi_index, c_denominator)
    hq = Fraction(1, c_denominator)
    h = rational_iv(hq)

    aa = IV(a.lo.reshape(rows, 1), a.hi.reshape(rows, 1))
    bb = IV(b.lo.reshape(rows, 1), b.hi.reshape(rows, 1))
    ee = IV(np.broadcast_to(eta.lo, (rows,)).reshape(rows, 1),
            np.broadcast_to(eta.hi, (rows,)).reshape(rows, 1))
    cc = IV(c.reshape(1, -1))
    ea, eb, ec = iv_exp(aa), iv_exp(bb), iv_exp(cc)
    one = IV(1)
    # Stable logistic form avoids powers of exp(c) near the finite tails.
    ml = one / (one + ec)
    lam = ec * ml
    common = lam * ml
    kcoef = (one + ee) * ea * (one + eb)
    cpoly = eb * ml + ee * lam + kcoef * common
    invp = one / (cpoly.ipow(10) * cpoly.sqrt())
    f0 = common.ipow(5) * common.sqrt() * invp
    f1 = lam * f0
    s0 = h * sum_iv(f0, axis=1)
    s1 = h * sum_iv(f1, axis=1)

    # First omitted nodes, exactly on the dyadic lattice.
    c_left = Fraction(c_lo_index - 1, c_denominator)
    c_right = Fraction(c_hi_index + 1, c_denominator)
    cl, cr = rational_iv(c_left), rational_iv(c_right)
    ecl, emcr = iv_exp(cl), iv_exp(-cr)
    # e^{-p b} and e^{-p log eta}; evaluate as x^-10/sqrt(x).
    ebp = one / (iv_exp(b).ipow(10) * iv_exp(b).sqrt())
    etap = one / (eta.ipow(10) * eta.sqrt())
    eh11 = iv_exp(-rational_iv(Fraction(11, 2)) * hq)
    eh13 = iv_exp(-rational_iv(Fraction(13, 2)) * hq)
    # Left tails (c <= c_left).
    tail0_l = (h * ebp * (one + ecl).ipow(10)
               * iv_exp(rational_iv(Fraction(11, 2)) * c_left)
               / (one - eh11))
    tail1_l = (h * ebp * (one + ecl).ipow(9)
               * iv_exp(rational_iv(Fraction(13, 2)) * c_left)
               / (one - eh13))
    # Right tails (c >= c_right).
    tail0_r = (h * etap * (one + emcr).ipow(10)
               * iv_exp(-rational_iv(Fraction(11, 2)) * c_right)
               / (one - eh11))
    tail1_r = (h * etap * (one + emcr).ipow(9)
               * iv_exp(-rational_iv(Fraction(11, 2)) * c_right)
               / (one - eh11))

    const = inner_sinc_constants(hq, strip)
    eps = IV(0.0, const["epsilon_upper"])
    # Compose every endpoint through IV arithmetic.  In particular, do not
    # perform two ordinary binary64 additions and widen only once: one ulp
    # need not cover both rounding errors in a three-term tail numerator.
    lo0 = s0 / (one + eps)
    lo1 = s1 / (one + eps)
    hi0 = (s0 + tail0_l + tail0_r) / (one - eps)
    hi1 = (s1 + tail1_l + tail1_r) / (one - eps)
    i0 = IV(lo0.lo, hi0.hi)
    i1 = IV(lo1.lo, hi1.hi)
    if np.any(i0.lo <= 0):
        raise RuntimeError("inner sinc denominator was not certified positive")
    return (i1 / i0).clamp(0.0, 1.0)


def _outer_density_lattices(a: IV, b: IV, eta: IV):
    one = IV(1)
    ea, eb = iv_exp(a), iv_exp(b)
    t, s = ea / (one + ea), eb / (one + eb)
    rhoa = rational_iv(Fraction(CT_NUM, CT_DEN)) * t * t.sqrt() * (one-t).ipow(10)
    rhob = IV(CS) * s.ipow(5) * (one-s).ipow(5)
    af = rhoa * ea
    bf = rhob * (one+eb) / (eta+eb)
    return rhoa, rhob, af, bf


def _geometric_outer_tails(
    eta: IV,
    *,
    a_lo_index: int,
    a_hi_index: int,
    b_lo_index: int,
    b_hi_index: int,
    denominator: int,
) -> dict[str, IV]:
    h = rational_iv(Fraction(1, denominator)); one = IV(1)
    al = rational_iv(Fraction(a_lo_index-1, denominator))
    ar = rational_iv(Fraction(a_hi_index+1, denominator))
    bl = rational_iv(Fraction(b_lo_index-1, denominator))
    br = rational_iv(Fraction(b_hi_index+1, denominator))
    ct = rational_iv(Fraction(CT_NUM, CT_DEN)); cs = IV(CS)

    def geo_left(coef, rate, x):
        r = rational_iv(rate)
        return h*coef*iv_exp(r*x)/(one-iv_exp(-r*h))

    def geo_right(coef, rate, x):
        r = rational_iv(rate)
        return h*coef*iv_exp(-r*x)/(one-iv_exp(-r*h))

    # rho_a <= ct exp(3a/2) on the left and ct exp(-10a) right.
    a0_out = geo_left(ct, Fraction(3,2), al) + geo_right(ct, 10, ar)
    # rho_a exp(a) has rates 5/2 and 9.
    af_out = geo_left(ct, Fraction(5,2), al) + geo_right(ct, 9, ar)
    b0_out = geo_left(cs, 5, bl) + geo_right(cs, 5, br)
    # For eta>=1, (1+e^b)/(eta+e^b)<=1.
    bf_out = b0_out
    return dict(a0_out=a0_out, af_out=af_out,
                b0_out=b0_out, bf_out=bf_out)


def _arb_sec_power(x: Fraction, power: Fraction) -> arb:
    xx = arb(x.numerator) / x.denominator
    pp = arb(power.numerator) / power.denominator
    return (1 / xx.cos()) ** pp


def outer_poisson_error(eta_q: Fraction, kind: str, parity: int,
                        step: Fraction = Fraction(1,32),
                        axis_strip: Fraction = Fraction(1,5),
                        mixed_strip: Fraction = Fraction(1,10)) -> float:
    """Absolute 2-D infinite-trapezoid error, rounded upward by Arb."""
    old = ctx.prec; ctx.prec = 192
    try:
        eta = arb(eta_q.numerator) / eta_q.denominator
        V = (1+eta)/11
        h = arb(step.numerator)/step.denominator
        p = arb(21)/2

        def envelope(da_q: Fraction, db_q: Fraction) -> arb:
            da=arb(da_q.numerator)/da_q.denominator
            db=arb(db_q.numerator)/db_q.denominator
            hc=1/((p*(da+db)/2).cos())
            wo=1/(1+eta)
            base=(hc+wo)*hc*(1+hc)*(hc+arb(1)/2)**parity
            dens=(1/(da/2).cos())**(arb(23)/2)
            dens*= (1/(db/2).cos())**10
            if kind == "charge_F":
                dens*=1/(db/2).cos()
                return dens*V*base*10*(1+eta)/6
            if kind == "charge_minus":
                return dens*V*base
            if kind == "risk":
                wgcap=1/(db/2).cos()
                riskcap=(wgcap+wo)**2+(hc+wo)**2
                return dens*V*riskcap
            raise ValueError(kind)

        ma=envelope(axis_strip,Fraction(0))
        mb=envelope(Fraction(0),axis_strip)
        mm=envelope(mixed_strip,mixed_strip)
        da=arb(axis_strip.numerator)/axis_strip.denominator
        dm=arb(mixed_strip.numerator)/mixed_strip.denominator
        ra=(-2*arb.pi()*da/h).exp()
        rm=(-2*arb.pi()*dm/h).exp()
        err=2*ma*ra/(1-ra)+2*mb*ra/(1-ra)
        err+=4*mm*(rm/(1-rm))**2
        return arb_upper(err)
    finally:
        ctx.prec=old


def certify_fixed_eta(
    eta_q: Fraction,
    *,
    kinds: tuple[tuple[str,int], ...] = (("charge_F",1),("charge_minus",1),
                                         ("charge_F",3),("charge_minus",3)),
    outer_denominator: int = 32,
    a_lo_index: int = -512,
    a_hi_index: int = 128,
    b_lo_index: int = -192,
    b_hi_index: int = 192,
    inner_batch: int = 4,
    inner_lo_index: int = -192,
    inner_hi_index: int = 192,
    inner_denominator: int = 8,
    inner_strip: Fraction = Fraction(3,4),
    outer_axis_strip: Fraction = Fraction(1,5),
    outer_mixed_strip: Fraction = Fraction(1,10),
    progress: bool = False,
) -> dict:
    """Certify any selection of the risk and four odd charge integrals."""
    eta = rational_iv(eta_q)
    hq=Fraction(1,outer_denominator); h=rational_iv(hq)
    av=_grid(a_lo_index,a_hi_index,outer_denominator)
    bv=_grid(b_lo_index,b_hi_index,outer_denominator)
    bgrid=IV(bv)
    rb,bbf=None,None
    accum={key:IV(0) for key in kinds}
    started=time.time()
    for start in range(0,len(av),inner_batch):
        aa=np.repeat(av[start:start+inner_batch],len(bv))
        bb=np.tile(bv,min(inner_batch,len(av)-start))
        ai,bi=IV(aa),IV(bb)
        H=inner_haar_sinc(ai,bi,eta,c_lo_index=inner_lo_index,
                          c_hi_index=inner_hi_index,
                          c_denominator=inner_denominator,
                          strip=inner_strip)
        rhoa,rhob,af,bf=_outer_density_lattices(ai,bi,eta)
        wo=IV(1)/(IV(1)+eta); wg=iv_exp(bi)/(iv_exp(bi)+eta)
        V=(IV(1)+eta)/IV(11)
        for kind,parity in kinds:
            if kind=="risk":
                val=V*rhoa*rhob*((wg-wo).sq()-(H-wo).sq())
            else:
                qk=H*(IV(1)-H)*(H-IV(.5)).ipow(parity)
                base=(H-wo)*qk
                if kind=="charge_minus": val=-V*rhoa*rhob*base
                elif kind=="charge_F":
                    fstar=IV(10)*(IV(1)+eta)*iv_exp(ai)*(IV(1)+iv_exp(bi))/(eta+iv_exp(bi))
                    val=V*rhoa*rhob*base*fstar
                else: raise ValueError(kind)
            accum[(kind,parity)]=accum[(kind,parity)]+_scalar_sum(val)
        if progress and (start==0 or start+inner_batch>=len(av) or
                         (start//inner_batch)%16==0):
            print(f"  eta={eta_q} a={min(start+inner_batch,len(av))}/{len(av)}",flush=True)
    # Multiply the finite double lattice by h^2.
    for key in accum: accum[key]=accum[key]*h*h

    # Scalar lattice masses and exact geometric omitted-lattice tails.
    ag=IV(av); rhoa,_,af,_=_outer_density_lattices(ag,IV(np.zeros_like(av)),eta)
    _,rhob,_,bf=_outer_density_lattices(IV(np.zeros_like(bv)),bgrid,eta)
    ain=h*_scalar_sum(rhoa); afin=h*_scalar_sum(af)
    bin_=h*_scalar_sum(rhob); bfin=h*_scalar_sum(bf)
    ot=_geometric_outer_tails(eta,a_lo_index=a_lo_index,a_hi_index=a_hi_index,
                              b_lo_index=b_lo_index,b_hi_index=b_hi_index,
                              denominator=outer_denominator)
    a0out,afout,b0out,bfout=(ot[x] for x in
                              ("a0_out","af_out","b0_out","bf_out"))
    a0full=ain+a0out; affull=afin+afout
    b0full=bin_+b0out; bffull=bfin+bfout

    V=(IV(1)+eta)/IV(11)
    balls={}; ledgers={}
    for kind,parity in kinds:
        if kind=="risk":
            tail=(V*(a0out*b0full+ain*b0out)).hi
        elif kind=="charge_minus":
            tail=(V*qmax(parity)*(a0out*b0full+ain*b0out)).hi
        else:
            factor=IV(10)*(IV(1)+eta)
            tail=(V*qmax(parity)*factor*(afout*bffull+afin*bfout)).hi
        poisson=outer_poisson_error(eta_q,kind,parity,hq,
                                    outer_axis_strip,outer_mixed_strip)
        error=_up(tail+poisson)
        balls[f"{kind}:{parity}"]=accum[(kind,parity)]+sym(error)
        ledgers[f"{kind}:{parity}"]={"lattice_tail":float(tail),
                                      "poisson":float(poisson),
                                      "total_external_error":float(error)}
    return dict(eta=str(eta_q),balls=balls,ledger=ledgers,
                seconds=time.time()-started,
                grid=dict(outer_step=str(hq),a_indices=[a_lo_index,a_hi_index],
                          b_indices=[b_lo_index,b_hi_index],
                          inner_step=str(Fraction(1,inner_denominator)),
                          inner_indices=[inner_lo_index,inner_hi_index],
                          inner_strip=str(inner_strip),
                          outer_axis_strip=str(outer_axis_strip),
                          outer_mixed_strip=str(outer_mixed_strip)))


def certify_fast_risk(eta_q: Fraction, *, inner_batch: int=8,
                      progress: bool=False) -> dict:
    """Lower-cost point certificate used by the continuum compiler."""
    return certify_fixed_eta(
        eta_q,kinds=(("risk",1),),outer_denominator=16,
        a_lo_index=-224,a_hi_index=56,b_lo_index=-80,b_hi_index=80,
        inner_batch=inner_batch,inner_lo_index=-64,inner_hi_index=64,
        inner_denominator=4,inner_strip=Fraction(11,10),
        outer_axis_strip=Fraction(7,25),outer_mixed_strip=Fraction(7,50),
        progress=progress)


def serializable(result: dict) -> dict:
    out={k:v for k,v in result.items() if k!="balls"}
    out["balls"]={k:{"lower":repr(float(v.lo)),"upper":repr(float(v.hi)),
                       "width":repr(float(v.hi-v.lo))}
                  for k,v in result["balls"].items()}
    out["script_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return out


def selftest() -> None:
    c=inner_sinc_constants(Fraction(1,8),Fraction(3,4))
    assert c["epsilon_upper"] < 1e-14
    eta=rational_iv(Fraction(11,10))
    H=inner_haar_sinc(IV(np.array([-2.0,0.0,2.0])),
                       IV(np.array([-1.0,0.0,1.0])),eta)
    assert np.all(H.lo>0) and np.all(H.hi<1)
    assert np.max(H.hi-H.lo)<1e-8
    for kind in ("charge_F","charge_minus","risk"):
        assert outer_poisson_error(Fraction(145),kind,3)<1e-8
    print("Certificate0003_SINC_INTERVAL_SELFTEST_PASS")


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--eta",default="11/10")
    ap.add_argument("--risk",action="store_true")
    ap.add_argument("--batch",type=int,default=4)
    ap.add_argument("--progress",action="store_true")
    ap.add_argument("--selftest",action="store_true")
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    if args.selftest:
        selftest();return
    kinds=(("risk",1),) if args.risk else (("charge_F",1),("charge_minus",1),
                                            ("charge_F",3),("charge_minus",3))
    result=(certify_fast_risk(Fraction(args.eta),inner_batch=args.batch,
                              progress=args.progress) if args.risk else
            certify_fixed_eta(Fraction(args.eta),kinds=kinds,
                               inner_batch=args.batch,progress=args.progress))
    data=serializable(result)
    text=json.dumps(data,indent=2,sort_keys=True)
    print(text)
    if args.output: args.output.write_text(text+"\n")


if __name__=="__main__":
    main()
