"""Independent exact checks of rank and auxiliary-prime existence.

Uses Python integers only. Norm-count square roots are enclosed by integer
square roots after multiplying by 10**24. No published implementation imports.
"""
from pathlib import Path
from math import isqrt
import json,time
ROOT=Path(__file__).resolve().parent
SCALE=10**12

def prime_list(a,b):
    return [p for p in range(a+1,b+1) if all(p%q for q in range(2,isqrt(p)+1))]

def sqrt_quarter_bounds(num):
    assert num>=0
    t=isqrt(num*SCALE*SCALE//4)
    assert 4*t*t <= num*SCALE*SCALE < 4*(t+1)*(t+1)
    return t,t+1

def norm_count_numerator(Dlo,Dhi,a,b):
    numerator=0
    for y in range(1,isqrt(4*b//Dlo)+1):
        hi=4*b-Dlo*y*y
        lo=max(0,4*a-Dhi*y*y)
        assert hi>=lo>=0
        numerator += SCALE+sqrt_quarter_bounds(hi)[1]-sqrt_quarter_bounds(lo)[0]
    return numerator

def prove_rank(P,n,primes):
    K=43;S=6*P//(5*K);R=K*S;J=R//8;M=R*(S+1)//2
    assert n*J>=M
    minimum=None;checks=0;argmin=None;required=0
    for p in primes:
        assert K<p<R<=p*p
        d=(R-1)//p
        assert d<p
        Q,v=divmod(J,p)
        cumulative=0
        for e in range(d+1):
            t=R-e*p-1
            cumulative+=p*(t//K)+t%K
            B=cumulative-e*(e+1)//2
            full=min(e+1,Q)
            mu=full*(p-e)+full*(full-1)//2
            if e>=Q:mu+=max(0,v-e+Q)
            assert mu>0
            if e in (0,1,Q-1,Q,Q+1,d):
                direct=sum(max(0,min(p,max(0,J-l*p))-e+l) for l in range(e+1))
                assert direct==mu
            margin=n*mu-B
            required=max(required,B//mu+1)
            if minimum is None or margin<minimum:minimum=margin;argmin=[p,e]
            checks+=1
    assert minimum>0
    return dict(P=P,K=K,S=S,R=R,J=J,M=M,n=n,degree_checks=checks,minimum_margin=minimum,argmin=argmin,minimum_sufficient_n=required)

def main():
    start=time.monotonic();a,b=150000,170000;primes=prime_list(a,b)
    assert len(primes)==1649
    candidates=prime_list(499,875);candidates=[d for d in candidates if d%8==3]
    published=[523,547,563,571,587,619,643,659,683,691,739,787,811,827,859]
    assert candidates==published
    ranks=[]
    for P in (36000000,169000000,312000000):
        S=6*P//(5*43);R=43*S;J=R//8
        floor_A=42*S*(S+1)//(2*(J-S+1))
        n=(floor_A//800+1)*800
        ranks.append(prove_rank(P,n,primes))
    mixed=prove_rank(312000000,35394400,primes)
    assert mixed['minimum_margin']==23702027808 and mixed['degree_checks']==3867213
    norms=[]
    for lo,hi in [(499,503)]+[(D,D) for D in candidates]:
        upper=norm_count_numerator(lo,hi,a,b)
        assert upper<len(primes)*SCALE
        # Radius: pi>3; sqrt(D)<=ceil sqrt(D), all upper bounds integral.
        nmax=max(r['n'] for r in ranks)
        ceil_sqrtD=isqrt(hi)+1
        # sqrt(n*sqrt(D)/(2*pi)) < ceil_sqrt(n*ceil_sqrtD/6).
        radius_base=isqrt(nmax*ceil_sqrtD//6)+1
        twice_diameter_upper=4*radius_base+isqrt(hi+4)+1
        assert twice_diameter_upper<2*a
        norms.append(dict(D_interval=[lo,hi],non_inert_upper_numerator=upper,denominator=SCALE,diameter_upper_numerator=twice_diameter_upper,diameter_upper_denominator=2))
    out=dict(passed=True,prime_interval=[a,b],prime_count=len(primes),admissible_candidates=candidates,mixed_rank_499=mixed,old_node_counts_with_mixed_rank=ranks,norm_bounds=norms,seconds=time.monotonic()-start,scope='Independent integer reconstruction of auxiliary-prime count, degree and multiplicity inequalities. Published determinant arithmetic and metric costs are not reimplemented.')
    (ROOT/'results/independent_rank.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
