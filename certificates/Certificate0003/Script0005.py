#!/usr/bin/env python3
"""Replay the 28 by 14 double-Haar continuum-compiler node certificates.

Each exact interpolation node is

    x[j,k]=(2j+1)/14 + cos((2k+1)pi/28)/14.

The statistical sinc evaluator is run at a nearby exact decimal-rational
eta.  Arb certifies the displacement in log eta, and the global analytic
bound |J'|<=77 transfers the risk ball back to the exact Chebyshev node.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import time

from flint import arb, ctx
import numpy as np

from Script0002 import certify_fast_risk, rational_iv


HERE=Path(__file__).resolve().parent


def au(x: arb) -> float:
    return float(np.nextafter(float(x.abs_upper()),math.inf))


def make_nodes(digits: int=17):
    old=ctx.prec;ctx.prec=256
    nodes=[]
    try:
        pi=arb.pi()
        for j in range(28):
            center=arb(2*j+1)/14
            for k in range(14):
                theta=arb(2*k+1)*pi/28
                x=center+theta.cos()/14
                eta=x.exp()
                # repr(float(.)) is the shortest exact decimal for a binary64
                # nearest the high-precision node; it becomes an exact
                # Fraction input to the statistical evaluator.
                q=Fraction(repr(float(eta.mid())))
                qarb=arb(q.numerator)/q.denominator
                dx=au(qarb.log()-x)
                nodes.append(dict(block=j,node=k,eta=str(q),
                                  x_center=str(x.mid()),x_radius=str(x.rad()),
                                  log_eta_displacement_upper=repr(dx)))
    finally:ctx.prec=old
    return nodes


def worker(item):
    q=Fraction(item["eta"])
    r=certify_fast_risk(q,inner_batch=16,progress=False)
    ball=r["balls"]["risk:1"]
    # J=11D/(1+eta), followed by the exact-node displacement allowance.
    scale=11.0/(1.0+float(q))
    # The binary multiplication is widened by two ulps.  The exact rational
    # calculation is recovered more directly in the integer-ratio path below.
    exact_scale=rational_iv(Fraction(11,1)/(1+q))
    J=ball*exact_scale
    move=np.nextafter(77.0*float(item["log_eta_displacement_upper"]),math.inf)
    Jlo=float(np.nextafter(J.lo-move,-math.inf))
    Jhi=float(np.nextafter(J.hi+move,math.inf))
    return {**item,"J":{"lower":repr(Jlo),"upper":repr(Jhi),
                         "width":repr(Jhi-Jlo)},
            "D":{"lower":repr(float(ball.lo)),"upper":repr(float(ball.hi))},
            "ledger":r["ledger"]["risk:1"],"seconds":r["seconds"],
            "unused_float_scale":scale}


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--workers",type=int,default=8)
    ap.add_argument("--output",type=Path,
                    default=HERE/"Data0007.json")
    args=ap.parse_args();nodes=make_nodes();started=time.time();out=[]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(worker,x):(x["block"],x["node"]) for x in nodes}
        done=0
        for f in as_completed(futures):
            out.append(f.result());done+=1
            if done%14==0:print(f"nodes {done}/392",flush=True)
    out.sort(key=lambda x:(x["block"],x["node"]))
    sinc=HERE/"Script0002.py"
    data={"format":"certificate0003-continuum-chebyshev-node-balls-v1",
          "blocks":28,"degree":13,"halfwidth":"1/14",
          "interpolation_remainder_upper":"11/134217728",
          "derivative_bound":"77","nodes":out,
          "sinc_script_sha256":hashlib.sha256(sinc.read_bytes()).hexdigest(),
          "node_replay_script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          "seconds":time.time()-started}
    args.output.write_text(json.dumps(data,indent=2)+"\n")
    print(args.output)


if __name__=="__main__":main()
