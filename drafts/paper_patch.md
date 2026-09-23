# Suggested paper-level patch

This is not an upstream PR yet. It is a minimal textual replacement for the two accounting points that drive the candidate exponent change.

## Patch 1: N4(i)

Replace the conclusion g_j <= c_j + 1 by g_j <= c_j.

Suggested proof paragraph:

Each re-selection of j at iteration r removes a pivot whose home is r, and there is at most one such event per (j,r). Re-selection occurs only if the residual group is nonempty. Hence the re-selection homes do not exhaust the home-components touched by P_j. If P_j is eventually emptied by a child, that terminal child causes no re-selection and contributes a further home distinct from every previous re-selection home. Otherwise P_j has a residual member after the child loop; since X is full, that member lies in W'_X and has home 0, again distinct from all child homes that caused re-selection. Deleting the c_j different-home edges of F_j leaves c_j+1 monochromatic components, while the g_j re-selection homes plus the terminal home occupy at least g_j+1 components. Thus g_j+1 <= c_j+1 and g_j <= c_j.

N4(ii) then changes from sum_full_X sum_j g_j <= sum p + 2m to sum_full_X sum_j g_j <= 2m.

## Patch 2: initial pivot insertion cost

The current N3 cost consequence prices initial pivot inserts at O(t) each. For the implemented DLazy structure, BM.5 creates a fresh one-block structure and Insert does not split. Existing upstream lemmas therefore give constant insertion cost while the block count remains one.

Suggested accounting: initial pivot insertion costs O(1) per pivot, plus the existing group-size work to choose/store the pivot; later inserts into evolved multi-block structures retain the generic O(t) charge.

This prevents initialization from reintroducing an O(t p) term after N4 is sharpened.