"""Rational enclosures of the inert-prime and node-diameter bounds.

Only integer arithmetic, Fraction, and isqrt are used. Every radical is
bounded outward by integer inequalities; no floating transcendental call.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
T=10**40

def root_bounds(q):
    q=Q(q)
    assert q>=0
    k=isqrt(q.numerator*T*T//q.denominator)
    lo,hi=Q(k,T),Q(k+1,T)
    assert lo*lo<=q<hi*hi
    return lo,hi

def sieve(b):
    a=bytearray(b'\1')*(b+1);a[:2]=b'\0\0'
    for p in range(2,isqrt(b)+1):
        if a[p]:a[p*p::p]=bytes((b-p*p)//p+1)
    return a

def ceiling_decimal(q,places=12):
    scale=10**places;n=-((-q.numerator*scale)//q.denominator)
    return f'{n//scale}.{n%scale:0{places}d}'

# The displayed lower bound for pi is classical and far more precise than needed.
pi_lo=Q('3.14159265358979323846264338327950288419716939937510')
contracts=[(312000000,43,125,35155200,200000,228000,[419,443,467,491],False),
           (312000000,17,128,86265600,500000,515000,[379],True),
           (756000000,17,128,208919200,800000,820000,[347],True)]
out=[]
for P,K,eps,n,A,B,ds,parity in contracts:
    prime=sieve(B);count=sum(prime[A+1:B+1]);geometry=[]
    for D in ds:
        split_hi=Q(0)
        for y in range(1,isqrt(4*B//D)+1):
            upper=root_bounds(Q(B)-Q(D*y*y,4))[1]
            lower=root_bounds(max(Q(0),Q(A)-Q(D*y*y,4)))[0]
            split_hi+=1+(upper-lower)/(2 if parity and y%2==0 else 1)
        sqrt_D_hi=root_bounds(D)[1]
        diam_hi=2*root_bounds(n*sqrt_D_hi/(2*pi_lo))[1]+root_bounds(D+4)[1]/2
        assert split_hi<count and diam_hi<A
        geometry.append(dict(D=D,split_count_upper=ceiling_decimal(split_hi),
                             diameter_upper=ceiling_decimal(diam_hi),passed=True))
    out.append(dict(P=P,K=K,epsilon_numerator=eps,n=n,prime_window=[A,B],prime_count=count,
                    even_y_parity=parity,geometry=geometry))
result=dict(passed=True,method='Exact rational arithmetic with 40-decimal outward radical bounds',contracts=out)
expected=json.loads((Path(__file__).resolve().parent/'results/geometry.json').read_text())
assert result==expected
print(json.dumps(result,indent=2))
