"""A short rational certificate for the sufficient mixed-rank criterion.

Every prime in (160000,170000] satisfies the sufficient inequality (1.3)
of paper22. Existence of an inert prime follows from a rational enclosure
of the norm counts. No published verification implementation is imported.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import isqrt
import json,time
ROOT=Path(__file__).resolve().parent
A,B=160000,170000
SCALE=10**6

def primes(a,b):return [p for p in range(a+1,b+1) if all(p%q for q in range(2,isqrt(p)+1))]

def norm_upper(Dlo,Dhi):
    total=0;terms=[]
    for y in range(1,isqrt(4*B//Dlo)+1):
        hi=4*B-Dlo*y*y;lo=max(0,4*A-Dhi*y*y)
        assert hi>=lo>=0
        hlo=isqrt(hi*SCALE*SCALE//4);llo=isqrt(lo*SCALE*SCALE//4)
        assert 4*hlo*hlo<=hi*SCALE*SCALE<4*(hlo+1)**2
        assert 4*llo*llo<=lo*SCALE*SCALE<4*(llo+1)**2
        term=SCALE+hlo+1-llo;total+=term
        terms.append(dict(y=y,sqrt_upper_numerator=hlo+1,sqrt_lower_numerator=llo,term_upper_numerator=term))
    return total,terms

def main():
    start=time.monotonic();plist=primes(A,B);assert len(plist)==814
    records=[]
    for P,n in [(312000000,35394400),(36000000,4822400),(169000000,22638400),(312000000,41793600)]:
        K=43;S=6*P//(5*K);R=K*S;J=R//8;M=R*(S+1)//2
        assert K<A<B<R<A*A and 1<=J<=R and n>=2*S
        H=Q(J)-Q(R*J,A*A)-Q(R,A)
        margin=n*H-Q((R+B)**2,2*K)
        assert H>0 and margin>0
        records.append(dict(P=P,K=K,S=S,R=R,J=J,M=M,n=n,n_at_least_2S=n>=2*S,H=str(H),margin=str(margin),margin_numerator=margin.numerator,margin_denominator=margin.denominator))
    candidates=[d for d in primes(499,875) if d%8==3]
    counts=[]
    for Dlo,Dhi in [(499,503)]+[(D,D) for D in candidates]:
        upper,terms=norm_upper(Dlo,Dhi)
        assert upper<765*SCALE<len(plist)*SCALE
        nmax=max(r['n'] for r in records)
        base=isqrt(nmax*(isqrt(Dhi)+1)//6)+1
        twice_diam=4*base+isqrt(Dhi+4)+1
        assert twice_diam<2*A
        counts.append(dict(D_interval=[Dlo,Dhi],norm_upper_numerator=upper,denominator=SCALE,diameter_upper_numerator=twice_diam,diameter_upper_denominator=2,terms=terms))
    result=dict(passed=True,prime_interval=[A,B],prime_count=len(plist),first_prime=plist[0],last_prime=plist[-1],primes=plist,rank_conditions=records,norm_counts=counts,sqrt_rounding_denominator=SCALE,all_non_inert_counts_below=765,seconds=time.monotonic()-start,method='Use n>=2S and n[J-RJ/A^2-R/A]>(R+B)^2/(2K), which imply paper22 sufficient criterion for every A<p<=B. Integer trial division counts primes; rational square-root brackets bound possible non-inert norm primes. Diameter bounds use pi>3 and integer square-root upper bounds.',scope='Independent exact arithmetic checks of the sufficient mixed-rank condition. Its mathematical implication of full rank is supplied by the proved sufficient-criterion lemma, not by these arithmetic checks.')
    (ROOT/'results/simplified-rank-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('primes','norm_counts')},indent=2))
    print('Norm upper at [499,503]:',Q(counts[0]['norm_upper_numerator'],SCALE))
    print('Maximum upper:',Q(max(r['norm_upper_numerator'] for r in counts),SCALE))
if __name__=='__main__':main()
