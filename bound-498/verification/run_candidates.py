"""Focused published determinant certificates at every admissible prime above 499."""
from pathlib import Path
import sys,json,time,math
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'paper2/supplement'))
import verify_euler_window_and_863_ladders as v
P=int(sys.argv[1]);Dlist=list(map(int,sys.argv[2:]))
S=12*P//430;R=43*S;J=125*R//1000
cache={36000000:145,169000000:137,312000000:129}[P]
records=[];start=time.monotonic()
for D in Dlist:
 assert 499<D<875 and D%8==3
 assert all(D%d for d in range(2,math.isqrt(D)+1))
 ok,gap,interval,details=v.certify_hybrid_k3_interval(D,D,P_max=P,K=43,c_R_num=12,eps_J_num=125,Q_guar=J,cls=v.vjd.DInterval,M_min_cache=cache,use_k4=False,clamp_m3=False,use_meixner_schur=True,use_wronskian=True,ms_params=(40,200,70,100,-4,5,12,200))
 rec=dict(D=D,P=P,ok=ok,gap=[str(interval.lo),str(interval.hi)],details=details)
 print(json.dumps(rec),flush=True);records.append(rec)
 (ROOT/'results'/f'remaining_{P}.json').write_text(json.dumps({'passed':all(r['ok'] for r in records),'records':records,'seconds':time.monotonic()-start},indent=2)+'\n')
 assert ok and interval.lo>0
print('ALL PASSED',time.monotonic()-start,flush=True)
