"""Enumerate the six prime discriminants between the established bound and 331."""
from pathlib import Path
from math import isqrt
import json
ROOT=Path(__file__).resolve().parent

def prime(n):return n>=2 and all(n%a for a in range(2,isqrt(n)+1))

def main():
    expected=json.loads((ROOT/'results/coverage.json').read_text())
    candidates=[d for d in range(332,499) if d%8==3 and prime(d)]
    certificates=json.loads((ROOT/'results/six-cases.json').read_text())['certificates']
    assert candidates==expected['required_prime_cases']==sorted(r['D'] for r in certificates)
    remaining=[d for d in range(164,332) if d%8==3 and prime(d)]
    assert remaining==expected['remaining_prime_cases']
    print('Exactly the six required cases:',', '.join(map(str,candidates)))
    print('Remaining primes above 163:',', '.join(map(str,remaining)))

if __name__=='__main__':main()
