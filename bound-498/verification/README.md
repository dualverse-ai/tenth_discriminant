# Numerical calculations

Run these commands from `bound-498/`. Python 3 is required. The
comparison at 499 also uses the packages listed in `paper22/requirements.txt`:

```sh
python -m pip install -r verification/paper22/requirements.txt
```

Check the saved numerical records and interval coverage:

```sh
python verification/summarize.py
```

Recompute the range from 875 to infinity and its interval schedule:

```sh
python verification/run_baseline.py
python verification/capture_global875.py
```

Recompute the fifteen comparisons between 499 and 875:

```sh
python verification/run_candidates.py 312000000 523 547
python verification/run_candidates.py 169000000 563 571
python verification/run_candidates.py 36000000 587 619 643 659 683 691 739 787 811 827 859
```

Check the simplified rank inequalities and the original degree inequalities:

```sh
python verification/simplified_rank.py
python verification/independent_rank.py
```

Recompute the rank parameters at 499, the improved comparison, and the control
with the earlier node count:

```sh
python verification/paper22/code/probe_divided_frobenius_large_scale_rank.py --Dlo 499 --Dhi 503 --Pmax 312000000 --alo 150000 --width 20000
python verification/paper22/code/certify_divided_frobenius_meixner.py verification/paper22/results/divided_frobenius_large_rank_D499_503_P312000000_a150000_b170000_20261027.json --mode both
python verification/paper22/code/certify_divided_frobenius_meixner.py verification/paper22/results/divided_frobenius_large_rank_D499_503_P312000000_a150000_b170000_20261027.json --mode both --baseline
python verification/paper22/code/check_divided_frobenius_meixner_application.py
python verification/summarize.py
```

Results are saved in `results/` and `paper22/results/`. The finite schedule is
`results/global875-schedule.csv`; the tail formulas are in
`uniform-tail-formulas.txt` and the numerical witness in
`results/global875-tail-witness.json`.
