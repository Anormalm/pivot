# The same re-selection +1 appears removable in DMSY26

Primary source:

Ran Duan, Xiao Mao, Xinkai Shu, Longhui Yin,
"A Faster Directed Single-Source Shortest Path Algorithm", ICALP 2026.

## Algorithm-level match

DMSY26 Algorithm 3 says, after removing U_i from each pivot group:

  "For each non-empty P_j from j in J, re-select p_j ..."

So exactly as in C-HD, an iteration that empties P_j causes no subsequent
re-selection.

## Published running-time charge

In the full-call analysis, DMSY26 defines g_j as the number of old pivots of
P_{X,j} removed in distinct child-return sets U_{Y_i}.  It observes that the
number of tree vertices of F_{X,j} lying in distinct U_{Y_i}'s is bounded by

  one plus the number of cross-level tree edges,

and therefore carries an exception:

  "Except once for each P_{X,j}"

which contributes O(p_X t).

## Same terminal-component sharpening

The same logic used for C-HD applies.

The g_j removed pivots that actually trigger re-selection lie in g_j distinct
child homes/components.

But these cannot exhaust the homes/components touched by the group:

- if a child removes the last residual members, that final child causes no
  re-selection and supplies an additional terminal child home;
- if the group survives the child loop, the full-call terminal region supplies
  the additional parent/own home in the C-HD formulation.

Thus, in the connected-tree language,

  g_j + 1 <= (# cross-level edges) + 1,

so the re-selection count itself is bounded directly by the cross-level edge
count.

## What this changes in DMSY26

It appears to remove the once-per-group O(p_X t) exception from the
**re-selection/insertion item**.

However, DMSY26's stated total runtime remains dominated by FindPivots:

  O(m (t + log n log t / (delta t))).

The paper explicitly states this after summing the re-selection terms.

So this sharpening is conceptually useful and supports the claim that the
same +1 in C-HD is inherited analysis slack, but it does not by itself yield
a new DMSY26 asymptotic theorem.

## Separate empty-group scan term

DMSY26 also has a distinct O(k p_X) term for the iteration in which a group
becomes empty (the Line-13 brute-force/picking work that can no longer be
absorbed by re-selection).

Our sharpening does not remove that term.  This is important: the terminal
component eliminates an *expensive re-selection*, not all once-per-group
work.

This distinction matches the C-HD candidate proof, which keeps cheap O(k p)
group work while removing only the expensive insertion coefficient from p.
