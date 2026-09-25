# Two-phase dormant FindPivots

## Motivation

Immediate repair after every strict contact can reproduce the old quadratic
local-search cost.  A dormant tail may receive several strict label decreases
before its closure is actually needed.

Because FindPivots only has to return a correct final FPContract, closure does
not have to be restored after every intermediate contact.

This suggests separating the invocation into two phases.

## Phase 1: structural discovery / root assignment

Process S roots using bounded local searches.

Retained dormant regions are globally visible.

On contact with a dormant region:

- relax the contact edge normally;
- if the target label/version is unchanged, its old closure remains valid by
  upstream `Closed.grows`;
- if the target strictly decreases, mark the target dirty;
- merge/associate the root search with the dormant component;
- do **not** immediately rescan the dirty target's outgoing edges.

Later strict decreases of the same dirty target only update its label.  They
do not trigger additional scans.

Roots already in a dormant final `val` may be assigned directly to that
region by the generalized failed-val theorem.

Goal of Phase 1:

```
collect roots + structural ownership + final labels
without paying one closure rebuild per contact
```

## Phase 2: final closure

After all S roots have been assigned, repair each remaining sub-k dormant
component using the final labels/source set.

A repair:

- seeds all roots/dirty frontier entries known for that component;
- scans dirty/unclosed tails;
- reuses unchanged `Closed` tails;
- adds newly discovered vertices to the component;
- stops and emits a successful tree if discovered mass reaches k;
- otherwise exhausts the queue and emits one failed closed region serving all
  Q roots in the component.

This directly targets the candidate lemmas:

- `failed_val_qroots_candidate`;
- `frontier_from_failed_val_qroots_candidate`.

## Why batching can help

If one dormant tail receives r strict decreases during Phase 1, immediate
repair may scan its outgoing prefix r times.

Two-phase repair scans only its **final** version once.

Thus the relevant count becomes:

```
# tails dirty at finalization
```

rather than

```
# strict decrease events
```

provided Phase 1 never requires closure from those dirty tails.

## The difficult merge case

Phase-2 repair of component A may discover/contact component B.

Then A and B must share a final closure.

If B's roots are introduced only after A has already settled vertices, those
new sources can lower previously settled labels.  A standard Dijkstra-style
one-pass proof no longer applies automatically.

Options:

1. restart the merged component;
2. allow reopenings through a label-correcting heap;
3. process components in a globally compatible source order;
4. use a mergeable multi-source closure whose invariant tolerates newly added
   sources.

(1) can repeat expensive work.
(2) needs a bound on reopenings.
(3) risks the sorting barrier.
(4) is the most interesting open direction.

## Important observation

The merge problem disappears for an **unchanged-label contact**.

The contacted dormant closure is still valid, and if the contact lies on the
canonical path of a complete witness, the contact vertex is complete.  The
old failed-val closure can cut the canonical path there.

So only strict-decrease contacts need to participate in Phase-2 dirty repair.

## Current theorem target

A useful next interface is:

```
FinalRepairSpec(component):
  every recorded Q root q satisfies
    Complete(q) ->
    every below-B canonical descendant of q
      lies in final val and is complete
```

plus a cost field depending on:

```
distinct dirty tails
+ distinct scanned edges
+ component merges
```

rather than the number of historical strict decreases.

The correctness half is now largely covered by the candidate failed-val
lemmas.  The cost/merge half remains open.
