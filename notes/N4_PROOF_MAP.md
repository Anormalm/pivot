# N4 tightening: kernel-checked proof map

Pinned upstream snapshot:

```text
spicylemonade/c-hd-proof
98c53accb47a505482a1781597ae14bf67e81cec
```

Green integration run:

```text
Lean candidate checks
run 36021686384
```

The following chain contains the actual N4-side argument.  It is separate
from the speculative BM.6 / 7/8 work.

## 1. Exact emptying bookkeeping

`drafts/LoopCostFiniteCandidates.lean`

- `card_nonempty_next_eq_candidate`
- `emptied_sub_meeting_candidate`
- `marked_disjoint_emptied_candidate`
- `marked_emptied_card_le_meeting_candidate`

These replace the one-sided nonempty-group inequality by an exact partition
and show:

```text
marked_i + emptied_i <= child/group meetings_i.
```

## 2. Separate cheap group work from expensive insertion work

`drafts/IterCostRefinedCandidate.lean`

- `iterCost_le_with_empty_credit_candidate`
- `nonemptyCount_initState_eq_candidate`

The key one-step shape is:

```text
iterCost_i + I * emptied_i
  <= ordinary_i + (2g+1+I) * meetings_i.
```

## 3. Telescope the insertion credit through the actual loop relation

`drafts/LoopCostInsertCreditCandidate.lean`

- `loopC_cost_insert_credit_candidate`

Using

```text
nonempty_{i+1} + emptied_i = nonempty_i,
```

the I-weighted emptying credit telescopes over `LoopC`.

## 4. Identify the terminal home

`drafts/FinalResidualCandidate.lean`

- `final_nonempty_le_groups_meeting_W'_candidate`

Any pivot group still nonempty after the child loop of a full call meets the
parent's final `W'` region.

`drafts/HomeOwnColourCandidate.lean`

- `card_children_meeting_add_one_le_of_none_candidate`

A group meeting `W'` contributes the additional `none` home, distinct
from every child home.

## 5. Strengthen the existing home-colour / Cr-Be charge

`drafts/MkOwnColourCandidate.lean`

- `mkOwn_full_le_of_W'_none_candidate`
- `mk_add_own_full_le_of_W'_none_candidate`

This gives the full-call bridge:

```text
mkOf + ownGroups <= p + |Cr| + |Be|.
```

The existing upstream PT-piece colour and bichromatic-edge charging lemmas
are reused.

## 6. Full-call terminal credit

`drafts/FullTerminalCreditCandidate.lean`

- `loopC_cost_full_terminal_credit_candidate`

Combines the loop telescope with the terminal own-home counter.

## 7. Cancel the once-per-group expensive term

`drafts/FullCreditCancellationCandidate.lean`

- `full_credit_cancel_candidate`

Schematic arithmetic:

```text
cost + I*p
  <= base + C*mk + I*mk + I*own

mk + own <= p + Cr + Be
```

therefore

```text
cost
  <= base + C*(p+Cr+Be) + I*(Cr+Be).
```

The expensive insertion coefficient `I` no longer multiplies the
once-per-group `p` term in the full-call BM.23 accounting.

## Paper-level interpretation

This formal chain is the source-aligned version of the simple Appendix N4
observation:

```text
current:   g_j <= c_j + 1
tightened: g_j <= c_j
```

because BM.23 re-selects only if the residual group is nonempty, leaving one
terminal home/component beyond the homes that caused re-selection.

## Claim boundary

This proof map establishes the N4-side tightening only.  It does **not**
remove the independent BM.6 ordered-pivot/amortized-potential term, so it
does not by itself prove a better final SSSP exponent.
