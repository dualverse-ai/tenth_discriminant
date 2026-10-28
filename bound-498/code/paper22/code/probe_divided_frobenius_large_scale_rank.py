"""Directed auxiliary-prime existence and exact mixed rank at large support.

Rank-only exploration at one discriminant or a closed interval. This program
does not compute the determinant's arithmetic/metric costs or an endpoint.
"""
import argparse,json,time
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
from sympy import primerange
from flint import arb,ctx

ROOT=Path(__file__).resolve().parents[1]


def sum_degrees(p,K,R,d):
    # D_m=(p/K)(R-mp-1)+(1-p/K)*((R-mp-1) mod K).
    # Residues have period K because p>K is prime.
    count=d+1;period=[(R-1-m*p)%K for m in range(K)]
    blocks,rem=divmod(count,K)
    residue_sum=blocks*sum(period)+sum(period[:rem])
    numerator=p*(count*(R-1)-p*d*count//2)+(K-p)*residue_sum
    assert numerator%K==0
    return numerator//K


def top_budget(p,K,R,J):
    d=(R-1)//p;Q0,v=divmod(J,p)
    if d>=p or Q0>d:return None
    # Fast formula, still checking all e below in the final certificate.
    full=Q0
    mu=full*(p-d)+full*(full-1)//2+max(0,v-d+full)
    B=sum_degrees(p,K,R,d)-d*(d+1)//2
    return B//mu+1,d,mu,B


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--Dlo',type=int,default=499)
    ap.add_argument('--Dhi',type=int);ap.add_argument('--Pmax',type=int,default=312000000)
    ap.add_argument('--alo',type=int,default=150000);ap.add_argument('--width',type=int,default=20000)
    args=ap.parse_args();ctx.prec=256;start=time.monotonic()
    Dhi=args.Dhi or args.Dlo;K=43;S=12*args.Pmax//(10*K);R=K*S;J=125*R//1000;M=R*(S+1)//2
    A=args.alo;B=A+args.width
    primes=list(map(int,primerange(A+1,B+1)))
    assert K<min(primes)<max(primes)<R and R<min(primes)**2
    # Bound each possible fixed-y norm interval uniformly on [Dlo,Dhi].
    # For any actual D the allowed nonnegative x lie on one grid of spacing
    # one; the interval below encloses that grid's admissible segment.
    norm_upper=arb(0);norm_records=[]
    for y in range(1,isqrt(4*B//args.Dlo)+1):
        hi=Q(B)-Q(args.Dlo*y*y,4)
        lo=max(Q(0),Q(A)-Q(Dhi*y*y,4))
        assert hi>=lo>=0
        val=1+arb(hi.numerator,0).sqrt()/arb(hi.denominator).sqrt()-arb(lo.numerator,0).sqrt()/arb(lo.denominator).sqrt()
        norm_upper+=val
        norm_records.append(dict(y=y,upper=str(val)))
    inert=bool(norm_upper<len(primes))
    candidates=[(p,top_budget(p,K,R,J)) for p in primes]
    required=max(v[0] for _,v in candidates)
    # The top-degree budget only proposes n. Certify every actual e for every
    # candidate using running sums and O(1) multiplicity formulas.
    n=(required+799)//800*800
    minmargin=None;checks=0
    for p,_ in candidates:
        d=(R-1)//p;Q0,v=divmod(J,p);total=0
        for e in range(d+1):
            cap=R-e*p-1;total+=p*(cap//K)+cap%K
            degree=total-e*(e+1)//2
            k=min(Q0,e+1)
            mu=k*(p-e)+k*(k-1)//2
            if e>=Q0:mu+=max(0,v-e+Q0)
            margin=n*mu-degree
            if minmargin is None or margin<minmargin:minmargin=margin
            checks+=1
    rho=(arb(n)*arb(Dhi).sqrt()/(2*arb.pi())).sqrt()+arb(Dhi+4).sqrt()/4
    out=dict(D_interval=[args.Dlo,Dhi],Pmax=args.Pmax,K=K,S=S,R=R,J=J,n=n,M=M,
        prime_interval=[A,B],prime_count=len(primes),max_non_inert_bound=str(norm_upper),
        norm_count_method='Fixed-y enclosing intervals at Dlo,Dhi',
        norm_records=norm_records,inert_prime_certified=inert,minimum_degree_margin=minmargin,
        degree_checks=checks,diameter=str(2*rho),distinct_residues=bool(2*rho<min(primes)),
        column_to_dimension_ratio=str(Q(n*J,M)),theta=str(Q(M,n*J)),
        wronskian_nodes=((max(S,(K-1)*S*(S+1)//(2*(J-S+1))+1)+799)//800)*800,
        seconds=time.monotonic()-start,
        scope='Author directed auxiliary-prime and exact rank budget only; complete determinant costs not computed.')
    out['passed']=inert and minmargin>0 and out['distinct_residues']
    path=ROOT/f'results/divided_frobenius_large_rank_D{args.Dlo}_{Dhi}_P{args.Pmax}_a{A}_b{B}_20261027.json'
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
