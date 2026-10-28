"""Check the saved interval coverage, rank margins and comparisons at 499."""
from pathlib import Path
from decimal import Decimal
from fractions import Fraction
from math import isqrt
import csv
import json

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / 'results'


def read(path):
    return json.loads(path.read_text())


def main():
    assert read(RESULTS / 'baseline875.json')['passed']
    candidates = [d for d in range(500, 875) if d % 8 == 3
                  and all(d % q for q in range(2, isqrt(d) + 1))]
    records = []
    for cutoff in (36000000, 169000000, 312000000):
        result = read(RESULTS / f'remaining_{cutoff}.json')
        assert result['passed']
        for row in result['records']:
            assert row['P'] == cutoff and row['ok']
            assert 0 < Decimal(row['gap'][0]) <= Decimal(row['gap'][1])
            records.append({key: row[key] for key in ('D', 'P', 'gap')})
    records.sort(key=lambda row: row['D'])
    assert [row['D'] for row in records] == candidates

    simple = read(RESULTS / 'simplified-rank-certificate.json')
    assert simple['passed'] and simple['prime_interval'] == [160000, 170000]
    assert simple['prime_count'] == 814
    for row in simple['rank_conditions']:
        K, R, J, n = (row[key] for key in ('K', 'R', 'J', 'n'))
        assert K < 160000 < 170000 < R < 160000**2
        assert J <= R and n >= 2 * row['S'] and row['M'] < n * J
        margin = n * (J - Fraction(R * J, 160000**2) - Fraction(R, 160000))
        margin -= Fraction((R + 170000)**2, 2 * K)
        assert margin == Fraction(row['margin_numerator'], row['margin_denominator']) > 0
    assert [row['D_interval'] for row in simple['norm_counts']] == [[499, 503]] + [[d, d] for d in candidates]
    for row in simple['norm_counts']:
        assert row['norm_upper_numerator'] < 765 * row['denominator']
        assert row['diameter_upper_numerator'] < 160000 * row['diameter_upper_denominator']

    rank = read(RESULTS / 'independent_rank.json')
    assert rank['passed'] and rank['admissible_candidates'] == candidates
    assert rank['prime_count'] == 1649 and rank['prime_interval'] == [150000, 170000]
    assert rank['mixed_rank_499']['minimum_margin'] > 0
    assert all(row['minimum_margin'] > 0 for row in rank['old_node_counts_with_mixed_rank'])

    schedule = read(RESULTS / 'global875-full-schedule.json')
    assert schedule['passed']
    intervals = schedule['finite_schedule']
    assert len(intervals) == 101
    assert intervals[0]['parameters']['D_lo'] == 875
    assert intervals[-1]['parameters']['D_hi'] == 5760000
    assert all(a['parameters']['D_hi'] == b['parameters']['D_lo']
               for a, b in zip(intervals, intervals[1:]))
    assert all(row['passed'] and 0 < Decimal(row['gap']['lo']) <= Decimal(row['gap']['hi'])
               for row in intervals)
    with (RESULTS / 'global875-schedule.csv').open(newline='') as handle:
        table = list(csv.DictReader(handle))
    assert len(table) == len(intervals)
    for row, interval in zip(table, intervals):
        assert [int(row[key]) for key in ('D_lo', 'D_hi')] == [interval['parameters'][key] for key in ('D_lo', 'D_hi')]
        assert Decimal(row['gap_lo']) == Decimal(interval['gap']['lo'])
        assert Decimal(row['gap_hi']) == Decimal(interval['gap']['hi'])
    stages = []
    for lo, hi, count in [(875, 3968539, 28), (3968539, 4894699, 37), (4894699, 5760000, 36)]:
        rows = [row for row in intervals if lo <= row['parameters']['D_lo'] < hi]
        assert len(rows) == count and rows[-1]['parameters']['D_hi'] == hi
        stages.append(dict(range=[lo, hi], intervals=count,
                           minimum_gap=str(min(Decimal(row['gap']['lo']) for row in rows))))
    tails = [row for row in schedule['calls'] if row['function'] == 'certify_infinite_tail']
    assert len(tails) == 2
    assert all(row['parameters']['D_lo'] == 5760000 and row['passed']
               and Decimal(row['gap']['lo']) > 0 and Decimal(row['log_slope']) > 0 for row in tails)
    witness = read(RESULTS / 'global875-tail-witness.json')
    constants = witness['constants']
    assert constants['D_lo'] == 5760000
    assert Decimal(constants['gap_iv']['lo']) > Decimal('0.00031743')
    assert Decimal(constants['log_slope_iv']['lo']) > Decimal('0.127829')
    assert sum(witness['variational']['k_w']) == witness['variational']['N_num']

    results22 = ROOT / 'paper22/results'
    rank499 = read(results22 / 'divided_frobenius_large_rank_D499_503_P312000000_a150000_b170000_20261027.json')
    mixed = read(results22 / 'divided_frobenius_meixner_D499_503_P312000000_both_20261027.json')
    control = read(results22 / 'divided_frobenius_meixner_D499_503_P312000000_both_baseline_20261027.json')
    checked = read(results22 / 'divided_frobenius_meixner_application_checked_20261027.json')
    assert rank499['passed'] and checked['passed'] and mixed['passed'] and control['execution_complete']
    assert rank499['minimum_degree_margin'] == rank['mixed_rank_499']['minimum_margin']
    assert rank499['D_interval'] == [499, 503]
    for result, baseline in [(mixed, False), (control, True)]:
        assert result['baseline'] == baseline
        assert {row['mode'] for row in result['records']} == {'float', 'decimal'}
        for key in ('K', 'S', 'R', 'J', 'M', 'n', 'minimum_degree_margin'):
            assert result['rank_certificate'][key] == rank499[key]
        for row in result['records']:
            assert Decimal(row['gap'][0]) <= Decimal(row['gap'][1])
            assert row['positive'] == (not baseline)
            if baseline:
                assert Decimal(row['gap'][1]) < 0
            else:
                assert Decimal(row['gap'][0]) > 0

    out = dict(passed=True, finite_coverage=stages, tail_start=5760000,
               tail_gap=constants['gap_iv'], tail_log_coefficient=constants['log_slope_iv'],
               candidates=records, candidate_count=len(candidates),
               mixed499={row['mode']: row['gap'] for row in mixed['records']},
               earlier_node_count={row['mode']: row['gap'] for row in control['records']})
    (RESULTS / 'complete-coverage.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Numerical coverage: 101 adjoining intervals, positive tail, 15 remaining candidates, and 499.')
    print('499 decimal gap:', out['mixed499']['decimal'])


if __name__ == '__main__':
    main()
