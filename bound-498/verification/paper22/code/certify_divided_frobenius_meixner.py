"""Replace the published v11 Wronskian node rule by a certified mixed rank rule.

The public arithmetic and Meixner functions remain their author implementation.
Only the node rule changes, and all n-dependent costs are recomputed. This is
an author adaptation, not an independent implementation or scientific review.
"""
import os
for variable in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[variable]='1'
import argparse
import inspect
import json
from pathlib import Path
import sys
import time
from flint import arb,ctx

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'literature/severi_paper2_v11_sources_20261027'
sys.path.insert(0,str(SOURCE))
import verify_euler_window_and_863_ladders as source


def build(rank_certificate,baseline=False):
    original=inspect.getsource(source.certify_hybrid_k3_interval)
    start=original.index('    if use_wronskian:\n')
    end=original.index('    m_bin = n // M_steps',start)
    replacement='''    assert use_wronskian and use_meixner_schur
    n = RANK_CERTIFICATE['n']
    assert (D_lo,D_hi,P_max,K,S,R,J,M_tri)==tuple(RANK_CERTIFICATE[k] for k in
        ('D_lo','D_hi','Pmax','K','S','R','J','M'))
    assert n % M_steps == 0 and M_tri < n*J
'''
    modified=original if baseline else original[:start]+replacement+original[end:]
    fields={k:k for k in ('D_lo','D_hi','P_max','Q_guar','K','S','R','J','n','M_tri','q_cols_c','low_cut_cache')}
    ivfields=dict(theta='theta_iv',eps='actual_eps_J_iv',rho_lo='rho_n_lo_iv',
        rho_hi='rho_n_hi_iv',eta='eta_box_iv',slope_lo='slope_j_lo_iv',
        slope_hi='slope_j_hi_iv',column_constant='const_j_iv',
        radius_coefficient='W12_norm_iv',arithmetic='total_padic_iv',
        variable_upper='arch_var_ms_iv',
        common_upper='W12_norm_iv*rho_n_hi_iv.ln()+(iv_M_tri*const_j_iv+iv_2*iv_M_tri*iv_M_tri.ln())/W_main_iv')
    lines=[f'            {k!r}: {v},' for k,v in fields.items()]
    lines += [f'            {k!r}: [str(({v}).lo),str(({v}).hi)],' for k,v in ivfields.items()]
    marker='        "n_composites": n_comp_total,\n';assert modified.count(marker)==1
    modified=modified.replace(marker,marker+'        "captured_contract": {\n'+'\n'.join(lines)+'\n        },\n')
    namespace=dict(vars(source));namespace['RANK_CERTIFICATE']=rank_certificate
    exec(compile(modified,'<divided-Frobenius-v11-node-rule>','exec'),namespace)
    return namespace['certify_hybrid_k3_interval'],original,modified


def main():
    ap=argparse.ArgumentParser();ap.add_argument('rank_file',type=Path)
    ap.add_argument('--mode',choices=('float','decimal','both'),default='both')
    ap.add_argument('--baseline',action='store_true',help='Retain the published Wronskian node rule for a matched comparison.')
    args=ap.parse_args();rank=json.loads(args.rank_file.read_text())
    assert rank['passed'] and rank['inert_prime_certified'] and rank['minimum_degree_margin']>0
    rank['D_lo'],rank['D_hi']=rank['D_interval']
    ctx.prec=256
    diameter=2*(arb(rank['n'])*arb(rank['D_hi']).sqrt()/(2*arb.pi())).sqrt()+arb(rank['D_hi']+4).sqrt()/2
    assert diameter<rank['prime_interval'][0]
    fn,original,modified=build(rank,baseline=args.baseline)
    modes=('float','decimal') if args.mode=='both' else (args.mode,)
    records=[];start=time.monotonic()
    for mode in modes:
        tick=time.monotonic();cls=source.vjd.FInterval if mode=='float' else source.vjd.DInterval
        print('Starting '+mode+' complete comparison',flush=True)
        ok,gap,interval,details=fn(rank['D_lo'],rank['D_hi'],P_max=rank['Pmax'],
            K=rank['K'],c_R_num=12,eps_J_num=125,Q_guar=rank['J'],
            cls=cls,M_min_cache=max(1,(rank['D_lo']+1)//4),use_k4=False,clamp_m3=False,
            use_meixner_schur=True,use_wronskian=True,
            ms_params=(40,200,70,100,-4,5,12,200))
        rec=dict(mode=mode,positive=ok,gap=[str(interval.lo),str(interval.hi)],
                 details=details,seconds=time.monotonic()-tick)
        records.append(rec);print(json.dumps(rec,indent=2),flush=True)
    positive=all(record['positive'] for record in records)
    out=dict(execution_complete=True,passed=positive,positive=positive,
        baseline=args.baseline,rank_certificate=rank,
        node_rule_change=('Retain the original Wronskian rank/node-choice block; add output capture only.' if args.baseline else 'Replace only the original rank/node-choice block by the certified n; retain the high-occupancy arithmetic branches and n-dependent caches.'),
        records=records,seconds=time.monotonic()-start,
        scope='Author adaptation/replay of published paper2/v11 local arithmetic and Meixner comparison. A positive gap excludes class-number-one fundamental discriminants D congruent to 3 modulo 4 in the stated closed interval; discrete norm-product exclusions use that congruence. No independent implementation, review, global bound, census or classification.')
    suffix='_baseline' if args.baseline else ''
    path=ROOT/f'results/divided_frobenius_meixner_D{rank["D_lo"]}_{rank["D_hi"]}_P{rank["Pmax"]}_{args.mode}{suffix}_20261027.json'
    path.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
