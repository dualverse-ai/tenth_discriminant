"""Replay the global875 proof while retaining every finite-interval certificate.

The published comparison functions are unchanged. Return-value wrappers record
all calls. For the tail only, two copies of published functions receive a single
extra assignment immediately before return, to retain the mathematical constants
and the rational convex-duality witness used in the successful certificate.
"""
from pathlib import Path
import sys,json,inspect,time,csv
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'paper2/code'))
import verify_jet_disk as v

def serialize(x):
    if isinstance(x,(v.FInterval,v.DInterval)):return dict(lo=str(x.lo),hi=str(x.hi))
    if isinstance(x,(str,int,bool)) or x is None:return x
    if isinstance(x,float):return repr(x)
    if isinstance(x,(list,tuple)):return [serialize(y) for y in x]
    if isinstance(x,dict):return {str(k):serialize(y) for k,y in x.items()}
    return str(x)

def main():
    start=time.monotonic();calls=[];tail_captures=[]
    original_tail=v.certify_infinite_tail
    tail_source=inspect.getsource(original_tail)
    var_source=inspect.getsource(v.solve_variational_hockey_staircase_iv)
    tail_return='    return gap_iv.lo > 0 and float(log_slope_iv.lo) > 0.12, float(gap_iv.lo), float(log_slope_iv.lo), gap_iv, details'
    var_return='    return F_w_iv, cls(duality_gap_ub.hi, duality_gap_ub.hi), cls(F_rigorous_lb.lo, F_rigorous_lb.lo)'
    assert tail_source.count(tail_return)==var_source.count(var_return)==1
    namespace=dict(vars(v));tc={};vc={};namespace['TAIL_CAPTURE']=tc;namespace['VAR_CAPTURE']=vc
    exec(compile(var_source.replace(var_return,'    VAR_CAPTURE.update(locals())\n'+var_return),'<capture-variational-return>','exec'),namespace)
    exec(compile(tail_source.replace(tail_return,'    TAIL_CAPTURE.update(locals())\n'+tail_return),'<capture-tail-return>','exec'),namespace)
    def tail(*args,**kwargs):
        tc.clear();vc.clear();ret=namespace['certify_infinite_tail'](*args,**kwargs)
        kept_tail={k:val for k,val in tc.items() if not callable(val) and k not in ['details']}
        var_keys=['M_steps','N_num','D_den','R','J','n','j_q','b0','k_w','theta_iv','u0_joint_iv','pref_iv','Delta0_iv','L_b0_hi_iv','L_iv','dL_iv','F_w_iv','duality_gap_ub','F_rigorous_lb','grad_iv','k_vmin','ramps_iv']
        tail_captures.append(dict(mode=kwargs.get('cls',v.FInterval).__name__,constants=serialize(kept_tail),variational=serialize({k:vc[k] for k in var_keys if k in vc})))
        return ret
    v.certify_infinite_tail=tail
    def wrap(name):
        fn=getattr(v,name);signature=inspect.signature(original_tail if name=='certify_infinite_tail' else fn)
        def record(*args,**kwargs):
            bound=signature.bind(*args,**kwargs);bound.apply_defaults();mode=bound.arguments.pop('cls').__name__
            tick=time.monotonic();ret=fn(*args,**kwargs)
            if name=='certify_infinite_tail':ok,_,slope,gap,details=ret
            else:ok,_,gap,details=ret;slope=None
            rec=dict(function=name,parameters=serialize(bound.arguments),mode=mode,passed=bool(ok),gap=serialize(gap),details=serialize(details),seconds=time.monotonic()-tick)
            if slope is not None:rec['log_slope']=repr(slope)
            calls.append(rec)
            print(json.dumps(dict(function=name,parameters=rec['parameters'],mode=mode,passed=ok,gap=rec['gap'])),flush=True)
            return ret
        setattr(v,name,record)
    for name in ['certify_infinite_tail','certify_fixed_param_interval','certify_hybrid_interval']:wrap(name)
    v.certify_thresholds()
    finite=[r for r in calls if r['function']!='certify_infinite_tail' and r['mode']=='FInterval' and r['parameters'].get('D_lo')!=163]
    assert len(finite)==101 and all(r['passed'] for r in finite)
    finite.sort(key=lambda r:r['parameters']['D_lo'])
    assert finite[0]['parameters']['D_lo']==875 and finite[-1]['parameters']['D_hi']==5760000
    assert all(a['parameters']['D_hi']==b['parameters']['D_lo'] for a,b in zip(finite,finite[1:]))
    out=dict(passed=True,tail_capture_change='One locals-copy assignment immediately before each original return; no numeric expression changed.',calls=calls,finite_schedule=finite,tail_certificates=tail_captures,seconds=time.monotonic()-start)
    (ROOT/'results/global875-full-schedule.json').write_text(json.dumps(out,indent=2)+'\n')
    decimal_tail=next(row for row in tail_captures if row['mode']=='DInterval')
    (ROOT/'results/global875-tail-witness.json').write_text(json.dumps(decimal_tail,indent=2)+'\n')
    fields=['index','method','D_lo','D_hi','P_max','K','S','R','J','n','c_R','eps_J','Q_guar','gap_lo','gap_hi']
    with (ROOT/'results/global875-schedule.csv').open('w',newline='') as handle:
        writer=csv.DictWriter(handle,fieldnames=fields)
        writer.writeheader()
        for index,record in enumerate(finite,1):
            p=record['parameters'];d=record['details']
            hybrid=record['function']=='certify_hybrid_interval'
            writer.writerow(dict(index=index,method='hybrid' if hybrid else p['mode'],
                D_lo=p['D_lo'],D_hi=p['D_hi'],P_max=d['P_max'],K=p['K'],
                S=d['S'],R=d['R'],J=d['J'],n=d['n'],
                c_R=p['c_R_num']/10 if hybrid else 2.3,
                eps_J=p['eps_J_num']/1000 if hybrid else .058,
                Q_guar=p.get('Q_guar',''),gap_lo=record['gap']['lo'],gap_hi=record['gap']['hi']))
    print('Complete schedule captured',len(finite),time.monotonic()-start,flush=True)
if __name__=='__main__':main()
