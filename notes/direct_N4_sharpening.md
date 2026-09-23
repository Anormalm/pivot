# Direct sharpening of the paper's N4 argument

Upstream source: paper/appendices/S_N_handled_ranges.md, N4.

## Current argument

For a full call X and pivot group j, upstream defines g_j as the number of BM.23 re-selections and c_j as the number of different-home parent edges in the containing PT piece F_j.

The paper argues that re-selection pivots from different iterations have different homes, deleting c_j different-home edges leaves c_j+1 monochromatic components, and concludes

    g_j <= c_j + 1.

## Missing terminal component

BM.23 re-selects only when the residual group is nonempty. Therefore the g_j removed re-selection pivots cannot exhaust all home-components touched by the group.

Case A: the group eventually empties during a child iteration. The child that removes the final remaining members causes no re-selection, and its home is distinct from every previous re-selection home.

Case B: the group remains nonempty after the child loop. Because X is full, every original group vertex lies in S_X subset U_X. A residual group member is outside the accumulated child-return set, hence lies in W'_X and has home 0, distinct from all child homes that caused re-selection.

Thus the group touches at least g_j+1 distinct monochromatic components. Since deleting c_j bichromatic edges yields c_j+1 components,

    g_j + 1 <= c_j + 1

and therefore

    g_j <= c_j.

This removes the once-per-group term from the expensive BM.23 count:

    current:   sum_full_X sum_j g_j <= sum p + 2m
    candidate: sum_full_X sum_j g_j <= 2m.

The global crossing/foreign-leaf edge charging in N4(ii) is unchanged.

## Formal analogue

The Lean route reconstructs the same missing terminal component using markedGroups, emptiedGroups, nonemptyCount, and the final own/none home. The paper proof above is the cleanest conceptual statement; the loop-potential proof is the source-aligned formal implementation.