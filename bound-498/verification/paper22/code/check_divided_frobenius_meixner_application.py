"""Check the rank parameters and the two numerical comparisons at 499."""
from decimal import Decimal as D
from fractions import Fraction as Q
import json
from pathlib import Path
from flint import arb,ctx

ROOT=Path(__file__).resolve().parents[1]


def main():
    ctx.prec=256
    rank_path=ROOT/'results/divided_frobenius_large_rank_D499_503_P312000000_a150000_b170000_20261027.json'
    rank=json.loads(rank_path.read_text())
    assert rank['passed'] and rank['inert_prime_certified'] and rank['distinct_residues']
    assert rank['D_interval']==[499,503] and rank['prime_interval']==[150000,170000]
    assert rank['prime_count']==1649 and rank['degree_checks']==3867213
    assert rank['minimum_degree_margin']==23702027808
    assert (rank['K'],rank['S'],rank['R'],rank['J'],rank['M'],rank['n'])==(43,8706976,374399968,46799996,1629945955088368,35394400)
    rows=[]
    for baseline in (False,True):
        suffix='_baseline' if baseline else ''
        path=ROOT/f'results/divided_frobenius_meixner_D499_503_P312000000_both{suffix}_20261027.json'
        result=json.loads(path.read_text())
        assert result['execution_complete'] and result['baseline']==baseline
        assert result['passed']==result['positive']==(not baseline)
        n=rank['wronskian_nodes'] if baseline else rank['n']
        assert len(result['records'])==2
        for record in result['records']:
            c=record['details']['captured_contract']
            assert (c['D_lo'],c['D_hi'],c['P_max'],c['Q_guar'],c['K'],c['S'],c['R'],c['J'],c['M_tri'],c['n'])==(499,503,312000000,46799996,43,8706976,374399968,46799996,1629945955088368,n)
            assert c['q_cols_c']==rank['M']//n and c['low_cut_cache']>=max(c['J']-1,c['q_cols_c'])
            assert D(c['theta'][0])<=D(rank['M'])/D(n*rank['J'])<=D(c['theta'][1])
            if baseline:
                assert D(record['gap'][1])<D('-.12343') and not record['positive']
            else:
                assert D(record['gap'][0])>D('.05119') and record['positive']
            # Conservative cross-check of the complete captured sum; allow only
            # the final decimal context's rounding, far below the stated margin.
            calculated=D(c['arithmetic'][0])-D(c['common_upper'][1])-D(c['variable_upper'][1])
            assert abs(calculated-D(record['gap'][0]))<D('1e-12')
            rows.append(dict(baseline=baseline,mode=record['mode'],n=n,gap=record['gap']))
    # Both additional source-flag guards hold without the old rank theorem.
    assert 312000000//125<125**4
    assert rank['M']<rank['n']*rank['J']
    assert 2*(arb(rank['n'])*arb(503).sqrt()/(2*arb.pi())).sqrt()+arb(507).sqrt()/2<150000
    out=dict(passed=True,rows=rows,relative_node_count=str(Q(35394400,41793600)))
    (ROOT/'results/divided_frobenius_meixner_application_checked_20261027.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
