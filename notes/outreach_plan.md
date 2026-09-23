# Outreach plan for C-HD authors

Target: 2026-09-23 evening, Singapore time.

## Recipient

Primary route:

```text
contact@vals.ai
Attn: Geby Jaff
```

Vals currently lists `contact@vals.ai` on its public About page:
https://www.vals.ai/about

Geby Jaff is the author/researcher associated with the C-HD Vals post:
https://www.vals.ai/blogs/faster-shortest-path-algorithm

Fallback: LinkedIn
https://www.linkedin.com/in/geby-jaff

Do not guess a personal Vals email pattern.

## First-message objective

Ask for a sanity check on one narrow paper-level point:

> In N4(i), can the terminal home/component sharpen
> `g_j <= c_j+1` to `g_j <= c_j`?

This is easier to inspect than leading with the eventual `7/8` exponent.

## Core argument to present

The existing N4 proof already says:

1. deleting `c_j` different-home edges leaves `c_j+1`
   monochromatic components;
2. pivots removed by distinct re-selection iterations have distinct homes.

The missing observation is that BM.23 only re-selects if the residual group
is nonempty. Therefore those `g_j` re-selection homes cannot use every
home-component:

- if a child eventually empties the group, that terminal home causes no
  re-selection;
- otherwise a final residual member lies in `W'_X`, home 0.

Thus the group touches at least `g_j+1` components and

```text
g_j+1 <= c_j+1
=> g_j <= c_j.
```

## Secondary observation

BM.6 initial pivots are inserted into a fresh one-block DLazy structure.
Insert does not split. Existing upstream lemmas imply constant insertion cost
there, while `BMCost.initCost` uses the generic evolved `O(t)` insert
charge.

Both observations are needed for the exponent to move.

## Conditional consequence

Only after the mechanism:

```text
k = 4
t ~ sqrt(N log N / m)
T_core ~ N log N/t + m t
       = O(sqrt(m N log N)).
```

At `m=n log^(3/4)n`:

```text
11/12 -> 7/8.
```

Do not frame this as proved.

## Formal status to disclose

Closed at paper/source level:
- direct N4 terminal-component argument;
- fresh one-block initial-insert audit;
- exact emptying telescope arithmetic;
- residual/own home interpretation;
- lower-order/master-term exponent audit.

Still open:
- actual Lean compilation of candidate lemmas;
- carrying `I*p` credit through `CostLog.RecCost`;
- refined `CostLe` / `CostAggregate.Valid` without unconditional `t*p`;
- new parameter program and master arithmetic;
- full RAM refinement rebuild and kernel audit.

## Evidence

Repo:
https://github.com/Anormalm/pivot

PR:
https://github.com/Anormalm/pivot/pull/2

Best files for an author:
- `notes/direct_N4_sharpening.md`
- `drafts/paper_patch.md`
- `notes/fresh_insert_audit.md`
- `notes/costlog_credit.md`
- `notes/blocker_audit.md`
- `results/LOCAL_EXPERIMENTS.md`

The experiments are falsification checks, not theorem evidence.

## Subject

Preferred:

```text
C-HD N4: can the full-call +1 per pivot group be removed?
```

Less technical fallback:

```text
Possible tightening in C-HD pivot re-selection accounting
```
