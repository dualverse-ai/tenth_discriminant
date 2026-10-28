"""Fresh replay of the published 875 bound, excluding the later finite sieve."""
from pathlib import Path
import sys,time,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'paper2/supplement'))
import verify_jet_disk as v
start=time.monotonic()
v.verify_lemmas()
v.certify_thresholds()
out={'passed':True,'seconds':time.monotonic()-start,'scope':'Published algebraic controls and complete determinant-based bound 875; finite small-prime elimination was not run.'}
(ROOT/'results/baseline875.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
