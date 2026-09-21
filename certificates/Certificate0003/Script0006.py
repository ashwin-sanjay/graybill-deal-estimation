#!/usr/bin/env python3
"""Fail-closed Bernstein check of the double-Haar Chebyshev continuum compiler."""

from __future__ import annotations

import argparse
from fractions import Fraction
from Script0012 import check_binding
import hashlib
import json
import math
from pathlib import Path

from flint import arb, ctx
import numpy as np

from Script0001 import IV
from Script0002 import arb_lower,arb_upper,rational_iv


HERE=Path(__file__).resolve().parent
N=14
REMAINDER=Fraction(22,4**14)  # equation (68), h=1/14,n=13


def cos_table():
    old=ctx.prec;ctx.prec=256;ans=[]
    try:
        pi=arb.pi()
        for m in range(N):
            row=[]
            for k in range(N):
                x=(arb(m)*arb(2*k+1)*pi/arb(28)).cos()
                row.append(IV(arb_lower(x),arb_upper(x)))
            ans.append(row)
    finally:ctx.prec=old
    return ans


def add_poly(a,b):
    n=max(len(a),len(b));out=[]
    for i in range(n):
        out.append((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))
    return out


def mul_linear(p,c0,c1):
    out=[0]*(len(p)+1)
    for i,x in enumerate(p):
        out[i]+=c0*x;out[i+1]+=c1*x
    return out


def cheb_power_polys():
    # T_m(2u-1), with exact integer power coefficients.
    out=[[1],[-1,2]]
    for _ in range(2,N):
        twice=mul_linear(out[-1],-2,4)
        prev=out[-2]+[0]*(len(twice)-len(out[-2]))
        out.append([x-y for x,y in zip(twice,prev)])
    return out[:N]


def dct_coefficients(values,ctab):
    coeff=[]
    for m in range(N):
        s=IV(0)
        for k in range(N):s=s+values[k]*ctab[m][k]
        coeff.append(s*rational_iv(Fraction(1,N) if m==0 else Fraction(2,N)))
    return coeff


def to_bernstein(coeff):
    cheb=cheb_power_polys();power=[IV(0) for _ in range(N)]
    for a,p in zip(coeff,cheb):
        for j,c in enumerate(p):power[j]=power[j]+a*c
    bern=[]
    for k in range(N):
        b=IV(0)
        for j in range(k+1):
            b=b+power[j]*rational_iv(Fraction(math.comb(k,j),math.comb(N-1,j)))
        bern.append(b)
    return bern


def split_half(b):
    levels=[b]
    for _ in range(1,len(b)):
        prev=levels[-1]
        levels.append([(prev[i]+prev[i+1])*rational_iv(Fraction(1,2))
                       for i in range(len(prev)-1)])
    return [row[0] for row in levels],[row[-1] for row in levels[::-1]]


def subdivide_all(b,depth):
    work=[b]
    for _ in range(depth):
        nxt=[]
        for x in work:nxt.extend(split_half(x))
        work=nxt
    return work


def interpolation_leaf_maps(ctab,depth):
    """Node-value to local-Bernstein maps, with correlations preserved.

    Converting interval-valued DCT coefficients to a global power basis loses
    the cancellations that make interpolation stable.  We instead transform
    each of the fourteen cardinal basis vectors separately, subdivide those
    exact linear images, and only then apply the statistical node balls.
    """
    bases=[]
    for k in range(N):
        values=[IV(int(i==k)) for i in range(N)]
        bases.append(subdivide_all(to_bernstein(dct_coefficients(values,ctab)),depth))
    # maps[leaf][bernstein_index][node]
    return [[[bases[k][leaf][i] for k in range(N)] for i in range(N)]
            for leaf in range(2**depth)]


def mapped_bernstein_lower(values,maps):
    ans=math.inf
    for leaf in maps:
        for weights in leaf:
            x=IV(0)
            for w,v in zip(weights,values):x=x+w*v
            ans=min(ans,float(x.lo))
    return ans


def main():
    ap=argparse.ArgumentParser();ap.add_argument("input",nargs="?",type=Path,
        default=HERE/"Data0007.json")
    ap.add_argument("--depth",type=int,default=8)
    ap.add_argument("--output",type=Path,
        default=HERE/"Data0008.json")
    args=ap.parse_args();data=json.loads(args.input.read_text())
    if data.get("format")!="certificate0003-continuum-chebyshev-node-balls-v1":
        raise RuntimeError("wrong node-ball format")
    expected={"blocks":28,"degree":13,"halfwidth":"1/14",
              "interpolation_remainder_upper":str(REMAINDER),
              "derivative_bound":"77"}
    for key,value in expected.items():
        if data.get(key)!=value:
            raise RuntimeError(f"bad continuum metadata {key}: {data.get(key)!r}")
    sha=hashlib.sha256((HERE/"Script0002.py").read_bytes()).hexdigest()
    check_binding(data,{"sinc_script_sha256":HERE/"Script0002.py","node_replay_script_sha256":HERE/"Script0005.py"})
    nodes=data["nodes"];ctab=cos_table();blocks=[]
    ids=[(x.get("block"),x.get("node")) for x in nodes]
    expected_ids=[(j,k) for j in range(28) for k in range(N)]
    if len(ids)!=392 or sorted(ids)!=expected_ids:
        raise RuntimeError("node IDs are missing, duplicated, or out of range")
    maps=interpolation_leaf_maps(ctab,args.depth)
    rem=float(REMAINDER)
    for j in range(28):
        row=[x for x in nodes if x["block"]==j]
        row.sort(key=lambda x:x["node"])
        if len(row)!=N:raise RuntimeError(f"block {j} is incomplete")
        vals=[IV(float(x["J"]["lower"]),float(x["J"]["upper"])) for x in row]
        plower=mapped_bernstein_lower(vals,maps)
        certified=float(np.nextafter(plower-rem,-math.inf))
        if not certified>0:
            raise RuntimeError(f"block {j} positivity failed: {certified}")
        blocks.append(dict(block=j,polynomial_lower=repr(plower),
                           remainder=str(REMAINDER),certified_lower=repr(certified),
                           maximum_node_width=repr(max(float(v.hi-v.lo) for v in vals))))
    result={"format":"certificate0003-continuum-bernstein-certificate-v1",
            "subdivision_depth":args.depth,"blocks":blocks,
            "global_certified_lower":repr(min(float(x["certified_lower"]) for x in blocks)),
            "node_file_sha256":hashlib.sha256(args.input.read_bytes()).hexdigest(),
            "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"inputScope":"Finite interpolation from supplied authenticated node enclosures."}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
    print("Certificate0003_CONTINUUM_POSITIVITY_CERTIFIED")


if __name__=="__main__":main()
