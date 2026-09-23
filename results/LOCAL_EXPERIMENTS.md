# Local experiment log

Date: 2026-09-23

## Environment

- Python: standard library only
- Random seed: `20260923` for Monte Carlo run
- No wall-clock speed claims are made; these tests target the combinatorial
  re-selection count that enters the asymptotic proof.

## Experiment 1: exhaustive group/home states

Configuration used in the committed local run:

```text
max group size:    7
max child homes:   4
```

Result:

```text
cases checked: 123,004
violations:    0
```

Target inequality:

```text
maximum possible expensive BM.23 reselections
    <= number of represented homes - 1
```

The pivot chosen after each re-selection was allowed to be arbitrary. This
is more permissive than the C-HD program.

## Experiment 2: exhaustive tree colourings

Configuration:

```text
max tree vertices: 7
number of colours: 3
```

Result:

```text
tree/colour instances: 1,668,504
violations:            0
```

Target inequality:

```text
number of colours - 1
    <= number of bichromatic parent edges
```

The corresponding combinatorial statement is already present in C-HD's Lean
development; this was an independent checker.

## Experiment 3: random stress test

Configuration:

```json
{
  "seed": 20260923,
  "requested_trials": 50000,
  "completed_trials": 50000,
  "violations": 0,
  "max_n": 24,
  "max_homes": 8,
  "mean_current_slack": 8.4919,
  "mean_proposed_slack": 7.4919,
  "tight_proposed_fraction": 0.02196,
  "mean_current_ratio_when_actual_positive": 5.427152468887296,
  "mean_proposed_ratio_when_actual_positive": 4.877526737778302
}
```

The random experiment compares the actual adversarial re-selection count with
both the current generic `1 + bich` charge and the candidate `bich`-only
charge.

No candidate-bound violation was observed.


## Experiment 4: direct loop-telescope stress test

Configuration:

```json
{
  "seed": 20260923,
  "requested_trials": 200000,
  "completed_trials": 200000,
  "violations": 0,
  "mean_aggregate_slack": 23.318355,
  "max_aggregate_slack": 102,
  "tight_fraction": 0.014585,
  "mean_marked_events": 11.79706,
  "mean_child_group_meetings": 38.3359
}
```

The test simulates multiple pivot groups across an ordered sequence of child
returns and checks four structural properties directly:

```text
marked_i + emptied_i <= meetings_i
final_nonempty + total_emptied == p
final_nonempty == own_groups
total_marked + p <= total_meetings + own_groups
```

No violation was observed in 200,000 sampled loop states.

This is the aggregate inequality that the proposed Lean telescope needs
before the existing home-colour and Cr/Be charging lemmas can cancel the
once-per-group term.

## Interpretation

The experiments support a narrow claim: the candidate full-call
re-selection charge survived these finite tests.

They do **not** establish:

- the refined C-HD master theorem;
- the `O(sqrt(m n log n))` bound;
- that all data-structure logarithms remain absorbed after retuning `t`;
- that `k = 4` is valid in every formal side condition without further work.

Those are explicit proof obligations in `notes/analysis.md`.
