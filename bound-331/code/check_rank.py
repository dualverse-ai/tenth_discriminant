"""Check every degree inequality in the three mixed-Frobenius rank contracts."""
from pathlib import Path
from math import isqrt
import json
ROOT=Path(__file__).resolve().parent

def primes_between(a,b):
    sieve=bytearray(b'\1')*(b+1);sieve[:2]=b'\0\0'
    for p in range(2,isqrt(b)+1):
        if sieve[p]:sieve[p*p::p]=bytes((b-p*p)//p+1)
    return [p for p in range(a+1,b+1) if sieve[p]]

def main():
    parameters=json.loads((ROOT/'results/parameters.json').read_text())
    expected=json.loads((ROOT/'results/rank.json').read_text())['contracts']
    assert len(parameters)==len(expected)==3
    for c,want in zip(parameters,expected):
        K,R,J,n=c['K'],c['R'],c['J'],c['n'];a,b=c['window']
        primes=primes_between(a,b);minimum=None;checks=0
        for p in primes:
            assert K<p<R<p*p
            q,r=divmod(J,p);degree_bound=0
            for e in range((R-1)//p+1):
                t=R-e*p-1
                degree_bound+=p*(t//K)+t%K-e
                full=min(e+1,q)
                multiplicity=full*(p-e)+full*(full-1)//2
                if e>=q:multiplicity+=max(0,r-e+q)
                margin=n*multiplicity-degree_bound
                assert margin>0
                minimum=margin if minimum is None else min(minimum,margin)
                checks+=1
        assert (len(primes),checks,minimum)==(want['prime_count'],want['checks'],want['min_margin'])
        print(f'K={K}, P={c["P"]}: {checks} inequalities; minimum margin {minimum}.')
    print('All mixed-Frobenius rank conditions passed.')

if __name__=='__main__':main()
