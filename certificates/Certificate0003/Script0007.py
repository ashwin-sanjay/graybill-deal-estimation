#!/usr/bin/env python3
"""Development certifier for the compact double-Haar far-wall field.

This file is deliberately separate from the frozen point/charge sinc engine.
It evaluates the exact compact wall formula for e=1/eta, including an
interval e-cell.  The current command reports the finite outer lattice and
inner sinc ledger; promotion additionally requires the outer Poisson and
omitted-lattice bounds implemented below.
"""

from __future__ import annotations

import argparse,json,math,time
from fractions import Fraction
import numpy as np

from Script0001 import IV,_dn,_up,sum_iv,sym,U
from Script0002 import (iv_exp,rational_iv,inner_sinc_constants,
                                         _grid,_scalar_sum,_geometric_outer_tails,
                                         arb_upper,CT_NUM,CT_DEN,CS)


MOMENT_INDICES=((0,1),(1,0),(2,0),(1,1),(0,2),(1,2),(2,1),(3,0))


def sum_nonnegative_iv(v,axis=-1):
    """Finite-sum enclosure using separate lower/upper error ledgers.

    Every caller supplies nonnegative intervals.  The generic ``sum_iv``
    quite properly uses the largest endpoint for a sign-indefinite sum, but
    that can erase a tiny positive lower sum when the upper dependency width
    is enormous.  Higham's gamma bound applies separately to the lower and
    upper endpoint arrays.
    """
    if np.any(v.lo<0):raise ValueError("nonnegative summation received lo<0")
    n=v.lo.shape[axis];gamma=(n*U)/(1-n*U)*1.05
    slo=v.lo.sum(axis=axis);shi=v.hi.sum(axis=axis)
    elo=_up(gamma*np.abs(v.lo).sum(axis=axis))
    ehi=_up(gamma*np.abs(v.hi).sum(axis=axis))
    return IV(np.maximum(0,_dn(slo-elo)),_up(shi+ehi))


def wall_inner(a,b,e,*,c_denominator=4,c_lo_index=-128,c_hi_index=128,
               strip=Fraction(11,10)):
    rows=np.size(a.lo);c=_grid(c_lo_index,c_hi_index,c_denominator)
    hq=Fraction(1,c_denominator);h=rational_iv(hq);one=IV(1)
    aa=IV(a.lo.reshape(rows,1),a.hi.reshape(rows,1))
    bb=IV(b.lo.reshape(rows,1),b.hi.reshape(rows,1))
    ee=IV(np.broadcast_to(e.lo,(rows,)).reshape(rows,1),
          np.broadcast_to(e.hi,(rows,)).reshape(rows,1))
    ec=iv_exp(IV(c.reshape(1,-1)));ea=iv_exp(aa);eb=iv_exp(bb)
    l=ec/(one+ec);m=one/(one+ec)
    t=ea/(one+ea);s=eb/(one+eb)
    u=t;v=(one-t)*s;w=(one-t)*(one-s)
    pe=(v*m+w*l)*(m+ee*l)+(one+ee)*u*l*m
    lm=l*m
    f0=lm.ipow(5)*lm.sqrt()*(m+ee*l).ipow(10)/(pe.ipow(10)*pe.sqrt())
    f1=f0*l/(m+ee*l)
    s0=h*sum_nonnegative_iv(f0,axis=1);s1=h*sum_nonnegative_iv(f1,axis=1)

    cl=rational_iv(Fraction(c_lo_index-1,c_denominator))
    cr=rational_iv(Fraction(c_hi_index+1,c_denominator))
    ecl=iv_exp(cl);emcr=iv_exp(-cr)
    # v,w are row intervals after dropping the inner singleton axis.
    vv=IV(v.lo.reshape(rows),v.hi.reshape(rows));ww=IV(w.lo.reshape(rows),w.hi.reshape(rows))
    vp=one/(vv.ipow(10)*vv.sqrt());wp=one/(ww.ipow(10)*ww.sqrt())
    eh11=iv_exp(-rational_iv(Fraction(11,2))*hq)
    eh13=iv_exp(-rational_iv(Fraction(13,2))*hq)
    eh5=iv_exp(-rational_iv(5)*hq);eh4=iv_exp(-rational_iv(4)*hq)
    # Uniform cell tails supplied by the compact wall theorem.
    tl0=h*vp*(one+e.hi*ecl).ipow(10)*iv_exp(rational_iv(Fraction(11,2))*Fraction(c_lo_index-1,c_denominator))/(one-eh11)
    tl1=h*vp*(one+e.hi*ecl).ipow(9)*iv_exp(rational_iv(Fraction(13,2))*Fraction(c_lo_index-1,c_denominator))/(one-eh13)
    tr0=h*wp*(one+emcr).ipow(5)*iv_exp(-rational_iv(5)*Fraction(c_hi_index+1,c_denominator))/(one-eh5)
    tr1=h*wp*(one+emcr).ipow(4)*iv_exp(-rational_iv(4)*Fraction(c_hi_index+1,c_denominator))/(one-eh4)
    eps=IV(0,inner_sinc_constants(hq,strip)["epsilon_upper"])
    lo0=s0/(one+eps);lo1=s1/(one+eps)
    hi0=(s0+tl0+tr0)/(one-eps);hi1=(s1+tl1+tr1)/(one-eps)
    i0=IV(lo0.lo,hi0.hi);i1=IV(lo1.lo,hi1.hi)
    if np.any(i0.lo<=0):
        bad=np.flatnonzero(i0.lo<=0)
        raise RuntimeError(f"wall inner denominator failed rows={bad[:5].tolist()} "
                           f"a={a.lo[bad[:5]]} b={b.lo[bad[:5]]} s0={s0.lo[bad[:5]]}")
    return i1/i0


def wall_inner_moments(a,b,e,*,c_denominator=4,c_lo_index=-128,
                       c_hi_index=128,strip=Fraction(11,10)):
    """Enclose the positive raw moments needed by the exact wall curvature.

    This is a point/cell evaluator.  Each positive moment receives its own
    relative sinc error and its own explicit geometric tails; products are
    formed only after normalization, as required by the recurrence.
    """
    rows=np.size(a.lo);c=_grid(c_lo_index,c_hi_index,c_denominator)
    hq=Fraction(1,c_denominator);h=rational_iv(hq);one=IV(1)
    aa=IV(a.lo.reshape(rows,1),a.hi.reshape(rows,1))
    bb=IV(b.lo.reshape(rows,1),b.hi.reshape(rows,1))
    ee=IV(np.broadcast_to(e.lo,(rows,)).reshape(rows,1),
          np.broadcast_to(e.hi,(rows,)).reshape(rows,1))
    ec=iv_exp(IV(c.reshape(1,-1)));ea=iv_exp(aa);eb=iv_exp(bb)
    l=ec/(one+ec);m=one/(one+ec)
    t=ea/(one+ea);s=eb/(one+eb)
    u=t;v=(one-t)*s;w=(one-t)*(one-s)
    pe=(v*m+w*l)*(m+ee*l)+(one+ee)*u*l*m
    pe1=(v*m+w*l)*l+u*l*m
    lm=l*m
    f0=lm.ipow(5)*lm.sqrt()*(m+ee*l).ipow(10)/(pe.ipow(10)*pe.sqrt())
    z=l/(m+ee*l);rr=pe1/pe

    clq=Fraction(c_lo_index-1,c_denominator)
    crq=Fraction(c_hi_index+1,c_denominator)
    cl=rational_iv(clq);cr=rational_iv(crq)
    ecl=iv_exp(cl);emcr=iv_exp(-cr)
    vv=IV(v.lo.reshape(rows),v.hi.reshape(rows))
    ww=IV(w.lo.reshape(rows),w.hi.reshape(rows))
    base_left=(one+e.hi*ecl).ipow(10)
    base_right=(one+emcr).ipow(5)
    out={}
    for n,j in ((0,0),)+MOMENT_INDICES:
        integrand=f0*z.ipow(n)*rr.ipow(j) if n and j else (
            f0*z.ipow(n) if n else (f0*rr.ipow(j) if j else f0))
        ss=h*sum_nonnegative_iv(integrand,axis=1)
        degree=n+j
        rate_l=Fraction(11,2)+degree
        rate_r=Fraction(5)-degree
        if rate_r<=0: raise ValueError("moment tail is not summable")
        vl=one/(vv.ipow(10+j)*vv.sqrt())
        wr=one/(ww.ipow(10+j)*ww.sqrt())
        ql=iv_exp(-rational_iv(rate_l)*hq)
        qr=iv_exp(-rational_iv(rate_r)*hq)
        tl=h*vl*base_left*iv_exp(rational_iv(rate_l)*clq)/(one-ql)
        tr=h*wr*base_right*iv_exp(-rational_iv(rate_r)*crq)/(one-qr)
        # On the c-strip, |z_C|<=sec(d/2)z and
        # |R_C|<=sec(d)R.  Arb supplies the resulting relative error.
        oldprec=__import__('flint').ctx.prec;__import__('flint').ctx.prec=192
        try:
            from flint import arb
            dd=arb(strip.numerator)/strip.denominator
            hh=arb(hq.numerator)/hq.denominator
            kap=(1/dd.cos())**(arb(21)/2+j)
            kap*= (1/(dd/2).cos())**n
            er=2*kap/((2*arb.pi()*dd/hh).exp()-1)
            from Script0002 import arb_upper
            eps=IV(0,arb_upper(er))
        finally:__import__('flint').ctx.prec=oldprec
        lo=ss/(one+eps);hi=(ss+tl+tr)/(one-eps)
        out[(n,j)]=IV(lo.lo,hi.hi)
    den=out[(0,0)]
    if np.any(den.lo<=0): raise RuntimeError("moment denominator failed")
    return {ij:x/den for ij,x in out.items() if ij!=(0,0)}


def finite_wall_curvature(ea:Fraction,eb:Fraction,*,outer_denominator=16,
                          a_lo=-224,a_hi=56,b_lo=-128,b_hi=128,batch=8):
    """Finite outer lattice enclosure of K'' (diagnostic until outer audit)."""
    elo,ehi=rational_iv(ea),rational_iv(eb);e=IV(elo.lo,ehi.hi)
    h=rational_iv(Fraction(1,outer_denominator));one=IV(1);p=IV(21)/IV(2)
    av=_grid(a_lo,a_hi,outer_denominator);bv=_grid(b_lo,b_hi,outer_denominator)
    total=IV(0);start=time.time();ct=rational_iv(Fraction(CT_NUM,CT_DEN))
    for i in range(0,len(av),batch):
        aa=np.repeat(av[i:i+batch],len(bv));bb=np.tile(bv,min(batch,len(av)-i))
        ai,bi=IV(aa),IV(bb);exa,exb=iv_exp(ai),iv_exp(bi)
        t=exa/(one+exa);s=exb/(one+exb)
        rhoa=ct*t*t.sqrt()*(one-t).ipow(10)
        rhob=IV(CS)*s.ipow(5)*(one-s).ipow(5)
        mu=wall_inner_moments(ai,bi,e)
        m01,m10=mu[(0,1)],mu[(1,0)]
        m20,m11,m02=mu[(2,0)],mu[(1,1)],mu[(0,2)]
        m12,m21,m30=mu[(1,2)],mu[(2,1)],mu[(3,0)]
        hp=IV(9)*m20-p*m11-IV(10)*m10.sq()+p*m01*m10
        hpp=(IV(882)*m01.sq()*m10-IV(1680)*m01*m10.sq()
             -IV(882)*m01*m11+IV(756)*m01*m20-IV(483)*m02*m10
             +IV(800)*m10.ipow(3)+IV(1680)*m10*m11
             -IV(1080)*m10*m20+IV(483)*m12-IV(756)*m21
             +IV(288)*m30)/IV(4)
        oo=one/(one+e);gg=exb/(one+e*exb)
        A=gg-oo;Ap=-gg.sq()+oo.sq();App=IV(2)*gg.ipow(3)-IV(2)*oo.ipow(3)
        B=m10-oo;Bp=hp+oo.sq();Bpp=hpp-IV(2)*oo.ipow(3)
        fp=IV(2)*A*Ap-IV(2)*B*Bp
        fpp=IV(2)*(Ap.sq()+A*App)-IV(2)*(Bp.sq()+B*Bpp)
        val=rhoa*rhob*(IV(2)*fp+(one+e)*fpp)/IV(11)
        total=total+_scalar_sum(val)
    return total*h*h,time.time()-start


def wall_outer_poisson_error(ea:Fraction,eb:Fraction,step:Fraction,
                             axis_strip=Fraction(7,25),
                             mixed_strip=Fraction(7,50)) -> float:
    """Uniform outer trapezoid error on a positive wall-parameter cell.

    The elementary bounds Gbar,Hbar<=1/e_lo are combined with the exact
    sector comparison

      |Hbar(a+i alpha,b+i beta)|
        <= sec((|alpha|+|beta|)/2)^p
           sec(p(|alpha|+|beta|)/2) Hbar(a,b).
    """
    if ea<=0: raise ValueError("positive e lower endpoint required")
    from flint import arb,ctx
    old=ctx.prec;ctx.prec=192
    try:
        elo=arb(ea.numerator)/ea.denominator
        ehi=arb(eb.numerator)/eb.denominator
        h=arb(step.numerator)/step.denominator;p=arb(21)/2
        def env(aq,bq):
            aa=arb(aq.numerator)/aq.denominator
            bb=arb(bq.numerator)/bq.denominator;s=aa+bb
            dens=(1/(aa/2).cos())**(arb(23)/2)
            dens*= (1/(bb/2).cos())**10
            gf=1/(bb/2).cos()
            hf=(1/(s/2).cos())**p/(p*s/2).cos()
            return dens*(1+ehi)/11*((gf/elo+1)**2+(hf/elo+1)**2)
        ma=env(axis_strip,Fraction(0));mb=env(Fraction(0),axis_strip)
        mm=env(mixed_strip,mixed_strip)
        d0=arb(axis_strip.numerator)/axis_strip.denominator
        d1=arb(mixed_strip.numerator)/mixed_strip.denominator
        r0=(-2*arb.pi()*d0/h).exp();r1=(-2*arb.pi()*d1/h).exp()
        ans=2*(ma+mb)*r0/(1-r0)+4*mm*(r1/(1-r1))**2
        return arb_upper(ans)
    finally:ctx.prec=old


def wall_endpoint_external_error(eb:Fraction,step:Fraction,*,
                                 a_lo_index:int,a_hi_index:int,
                                 b_lo_index:int,b_hi_index:int) -> dict:
    """Outer error for a cell touching e=0, using the integrable wall envelope.

    This is intentionally independent of a pointwise 1/e bound.  The two
    envelope monomials factor in the beta-logit variables, so both the complex
    Poisson error and the omitted rectangle are finite explicit expressions.
    """
    from flint import arb,ctx
    old=ctx.prec;ctx.prec=256
    try:
        def aq(q):return arb(q.numerator)/q.denominator
        def beta(x,y):return x.gamma()*y.gamma()/(x+y).gamma()
        p=arb(21)/2;h=aq(step);ehi=aq(eb)
        ka=2**(arb(33)/2)*3**11*beta(arb(4),arb(13)/2)
        kb=arb(2)**7*arb(3)**9
        c1=1+ka;c2=kb**(arb(1)/5);tw=arb(2)**(arb(6)/5)
        ex2=arb(5)/2
        eat=beta(arb(37)/10,arb(39)/5)/beta(arb(3)/2,arb(10))
        ebt=beta(arb(7),arb(4)/5)/beta(arb(5),arb(5))
        et=eat*ebt

        def coeffs(aa,bb):
            s=aa+bb
            gf=1/(bb/2).cos()
            hf=(1/(s/2).cos())**p/(p*s/2).cos()
            dens=(1/(aa/2).cos())**(arb(23)/2)
            dens*= (1/(bb/2).cos())**10
            cx=2*gf**2+4*hf**2*c1**2+4*hf**2*c2**2*tw
            ct=4*hf**2*c2**2*tw
            return dens*(1+ehi)/11*(4+cx*ex2+ct*et)
        d0=arb(7)/25;d1=arb(7)/50
        ma=coeffs(d0,arb(0));mb=coeffs(arb(0),d0)
        mm=coeffs(d1,d1)
        r0=(-2*arb.pi()*d0/h).exp();r1=(-2*arb.pi()*d1/h).exp()
        poisson=2*(ma+mb)*r0/(1-r0)+4*mm*(r1/(1-r1))**2

        # Exact beta integrals plus their one-dimensional sinc errors bound
        # the full positive lattices tightly.
        def full_lattice(integral,total_power):
            d=arb(1)
            eps=2*(1/(d/2).cos())**total_power/((2*arb.pi()*d/h).exp()-1)
            return integral*(1+eps)
        a0full=full_lattice(arb(1),arb(23)/2)
        b0full=full_lattice(arb(1),arb(10))
        bxfull=full_lattice(ex2,arb(10))
        atfull=full_lattice(eat,arb(23)/2)
        btfull=full_lattice(ebt,arb(39)/5)

        al=aq(Fraction(a_lo_index-1)*step);ar=aq(Fraction(a_hi_index+1)*step)
        bl=aq(Fraction(b_lo_index-1)*step);br=aq(Fraction(b_hi_index+1)*step)
        C=arb(CT_NUM)/CT_DEN;S=arb(CS)
        def tails(coef,lr,rr,xl,xr):
            return h*coef*(lr*xl).exp()/(1-(-lr*h).exp()) \
                 + h*coef*(-rr*xr).exp()/(1-(-rr*h).exp())
        a0out=tails(C,arb(3)/2,arb(10),al,ar)
        b0out=tails(S,arb(5),arb(5),bl,br)
        bxout=tails(S,arb(7),arb(3),bl,br)
        atout=tails(C,arb(37)/10,arb(39)/5,al,ar)
        btout=tails(S,arb(7),arb(4)/5,bl,br)
        cx=2+4*c1**2+4*c2**2*tw;ct=4*c2**2*tw
        omitted=(1+ehi)/11*(
            4*(a0out*b0full+a0full*b0out)
            +cx*(a0out*bxfull+a0full*bxout)
            +ct*(atout*btfull+atfull*btout))
        return dict(poisson=arb_upper(poisson),tail=arb_upper(omitted),
                    c1_upper=arb_upper(c1),c2_upper=arb_upper(c2),
                    ex2_upper=arb_upper(ex2),et_upper=arb_upper(et))
    finally:ctx.prec=old


def finite_wall_lattice(ea:Fraction,eb:Fraction,*,outer_denominator=16,
                        a_lo=None,a_hi=None,b_lo=None,b_hi=None,batch=8,
                        include_external=False,endpoint_external=False):
    if a_lo is None:a_lo=-24*outer_denominator
    if a_hi is None:a_hi=Fraction(7,2)*outer_denominator
    if b_lo is None:b_lo=-8*outer_denominator
    if b_hi is None:b_hi=8*outer_denominator
    a_lo=int(a_lo);a_hi=int(a_hi);b_lo=int(b_lo);b_hi=int(b_hi)
    elo,ehi=rational_iv(ea),rational_iv(eb)
    e=IV(elo.lo,ehi.hi);h=rational_iv(Fraction(1,outer_denominator));one=IV(1)
    av=_grid(a_lo,a_hi,outer_denominator);bv=_grid(b_lo,b_hi,outer_denominator)
    total=IV(0);start=time.time()
    ct=rational_iv(Fraction(CT_NUM,CT_DEN))
    for i in range(0,len(av),batch):
        aa=np.repeat(av[i:i+batch],len(bv));bb=np.tile(bv,min(batch,len(av)-i))
        ai,bi=IV(aa),IV(bb);exa,exb=iv_exp(ai),iv_exp(bi)
        t=exa/(one+exa);s=exb/(one+exb)
        rhoa=ct*t*t.sqrt()*(one-t).ipow(10)
        rhob=IV(CS)*s.ipow(5)*(one-s).ipow(5)
        hb=wall_inner(ai,bi,e)
        gb=exb/(one+e*exb);ob=one/(one+e)
        val=(one+e)/IV(11)*rhoa*rhob*((gb-ob).sq()-(hb-ob).sq())
        total=total+_scalar_sum(val)
    finite=total*h*h
    if not include_external:return finite,time.time()-start
    if ea<=0 or endpoint_external:
        ext=wall_endpoint_external_error(eb,Fraction(1,outer_denominator),
            a_lo_index=a_lo,a_hi_index=a_hi,b_lo_index=b_lo,b_hi_index=b_hi)
        external=float(np.nextafter(ext["tail"]+ext["poisson"],math.inf))
        return finite+sym(external),time.time()-start,dict(
            finite=[float(finite.lo),float(finite.hi)],external=external,**ext)
    # Exact geometric tails of the two beta-logit lattice densities.
    aviv=IV(av);bviv=IV(bv)
    exa,exb=iv_exp(aviv),iv_exp(bviv)
    ta=exa/(one+exa);sb=exb/(one+exb)
    rhoa=ct*ta*ta.sqrt()*(one-ta).ipow(10)
    rhob=IV(CS)*sb.ipow(5)*(one-sb).ipow(5)
    ain=h*_scalar_sum(rhoa);bin_=h*_scalar_sum(rhob)
    ot=_geometric_outer_tails(rational_iv(Fraction(1)),
        a_lo_index=a_lo,a_hi_index=a_hi,b_lo_index=b_lo,b_hi_index=b_hi,
        denominator=outer_denominator)
    ao,bo=ot["a0_out"],ot["b0_out"]
    # |(G-O)^2-(H-O)^2| <= 2(1/e_lo+1)^2.
    cap=(one+e)/IV(11)*IV(2)*(one+one/rational_iv(ea)).sq()
    tail=(cap*(ao*(bin_+bo)+ain*bo)).hi
    poisson=wall_outer_poisson_error(ea,eb,Fraction(1,outer_denominator))
    external=float(np.nextafter(tail+poisson,math.inf))
    return finite+sym(external),time.time()-start,dict(
        finite=[float(finite.lo),float(finite.hi)],tail=float(tail),
        poisson=float(poisson),external=external)


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--e-lo",default="0")
    ap.add_argument("--e-hi",default="1/1000");ap.add_argument("--batch",type=int,default=8)
    ap.add_argument("--curvature",action="store_true")
    ap.add_argument("--external",action="store_true")
    ap.add_argument("--outer-denominator",type=int,default=16);args=ap.parse_args()
    fun=finite_wall_curvature if args.curvature else finite_wall_lattice
    ans=fun(Fraction(args.e_lo),Fraction(args.e_hi),batch=args.batch,
            **({} if args.curvature else
               {"outer_denominator":args.outer_denominator,
                "include_external":args.external}))
    x,sec,*rest=ans
    print(json.dumps(dict(e=[args.e_lo,args.e_hi],
                              enclosure=[float(x.lo),float(x.hi)],seconds=sec,
                              ledger=(rest[0] if rest else None)),indent=2))


if __name__=="__main__":main()
