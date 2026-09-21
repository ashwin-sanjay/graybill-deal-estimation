#!/usr/bin/env python3
"""Assemble double-Haar sinc charge balls into the exact simplex-checker schema."""

from __future__ import annotations

from fractions import Fraction
from Script0012 import check_binding
import hashlib
import json
from pathlib import Path

from Script0001 import IV


HERE=Path(__file__).resolve().parent
ETAS=("11/10","2","11/2","18","145")
FILES=("Data0001.json","Data0002.json",
       "Data0003.json","Data0004.json",
       "Data0005.json")
KEYS=("charge_F:1","charge_minus:1","charge_F:3","charge_minus:3")
SCALES=tuple(map(Fraction,("1/7","4/7","7/4","7")))


def riv(q: Fraction) -> IV:
    return IV(q.numerator)/IV(q.denominator)


def load_ball(data,key):
    x=data["balls"][key]
    # The sinc JSON is a binary64 round-trip format: parsing recovers the
    # outward endpoints bit-for-bit.
    return IV(float(x["lower"]),float(x["upper"]))


def exact_float_string(x) -> str:
    """Serialize a binary64 endpoint as the exact rational it represents."""
    n,d=float(x).as_integer_ratio()
    return str(Fraction(n,d))


def main():
    sinc=HERE/"Script0002.py"
    sha=hashlib.sha256(sinc.read_bytes()).hexdigest()
    columns=[]
    for eta,name in zip(ETAS,FILES):
        data=json.loads((HERE/name).read_text())
        if data["eta"]!=eta: raise RuntimeError(f"eta mismatch in {name}")
        check_binding(data,{"script_sha256":sinc})
        raw=[load_ball(data,key) for key in KEYS]
        scaled=[riv(d)*g for d,g in zip(SCALES,raw)]
        norm=sum((x.sq() for x in scaled[1:]),scaled[0].sq()).sqrt()
        normalized=[x/norm for x in scaled]
        columns.append([{"lower":exact_float_string(x.lo),
                         "upper":exact_float_string(x.hi)}
                        for x in normalized])
    out={"format":"certificate0003-parity-preconditioned-normalized-v1",
         "eta":list(ETAS),"row_scale":[str(x) for x in SCALES],
         "columns":columns,
         "source":{"normalizer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"files":{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in FILES},"scope":"Fresh finite normalization of authenticated retained or regenerated charge enclosures."}}
    target=HERE/"Data0006.json"
    target.write_text(json.dumps(out,indent=2)+"\n")
    print(target)


if __name__=="__main__":main()
