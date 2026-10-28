"""Verify the six determinant comparisons extending the bound 498 to 331."""
from pathlib import Path
import argparse,json,sys,subprocess
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'lib'))
import verify_euler_window_and_863_ladders as estimator

CASES={d:(312000000,43,125,105,(200000,228000)) for d in (419,443,467,491)}
CASES.update({379:(312000000,17,128,95,(500000,515000)),347:(756000000,17,128,87,(800000,820000))})

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case',type=int,choices=sorted(CASES),help='Run one discriminant only.')
    args=ap.parse_args()
    expected=json.loads((ROOT/'results/six-cases.json').read_text())
    expected={r['D']:r['gap'] for r in expected['certificates']}
    if args.case is None:
        for d in [491,467,443,419,379,347]:
            subprocess.run([sys.executable,'-B',str(Path(__file__).resolve()),'--case',str(d)],check=True)
        print('All six comparisons passed in separate Python processes.',flush=True)
        return
    selected=[args.case]
    for d in selected:
        P,K,eps,cache,window=CASES[d]
        J=eps*(K*(12*P//(10*K)))//1000
        print(f'Checking D={d}',flush=True)
        ok,_,iv,detail=estimator.certify_hybrid_k3_interval(
            d,d,P_max=P,K=K,c_R_num=12,eps_J_num=eps,Q_guar=J,
            cls=estimator.vjd.DInterval,M_min_cache=cache,use_k4=False,
            clamp_m3=False,use_meixner_schur=True,use_wronskian=window,
            ms_params=(195,200,38,100,-5,5,1,200))
        gap=[str(iv.lo),str(iv.hi)]
        assert ok and iv.lo>0 and detail['save_k4']==0
        assert gap==expected[d],(d,gap,expected[d])
        print(f'D={d}: [{gap[0]}, {gap[1]}] > 0',flush=True)
    print(f'All {len(selected)} requested comparisons passed.',flush=True)

if __name__=='__main__':main()
