# Cross-tree supergroups: exact component penalty

Correctness does not require a pivot group to lie in one connected PT piece.
FPContract only needs nonempty, pairwise-disjoint groups whose union (with Q)
covers S and whose union is the frontier.

This suggests a two-parameter idea:

- keep FindPivots search scale k_s small;
- aggregate several PT pieces into a larger supergroup of target size K;
- use one pivot per supergroup, reducing the BM.6 pivot count.

The N4 charging argument shows the precise obstruction.

## One connected PT piece

For one tree piece with c bichromatic edges:

  deleting the c edges leaves c+1 monochromatic components.

BM.23's nonempty-residual condition supplies one terminal component, so

  g + 1 <= c + 1
  g <= c.

This is the verified N4 tightening.

## A supergroup spanning r disconnected pieces

Before deleting any bichromatic edges, the containing forest already has r
connected components.

Deleting c bichromatic edges leaves

  c + r

monochromatic components.

The same terminal-home argument now gives only

  g + 1 <= c + r

hence

  g <= c + r - 1.

So aggregating disconnected pieces introduces an unavoidable component-gap
term r-1 in this proof.

## Summed over all supergroups

Let R be the total number of original PT pieces and P be the number of
supergroups.  If every original piece belongs to exactly one supergroup,

  sum_groups (r_g - 1) = R - P.

Thus

  total reselections
    <= total bichromatic graph-edge charge + (R - P).

Increasing K reduces P, but R is still controlled by the small search/tree
scale k_s:

  R = O(N / k_s)

in the full-call layer accounting.

Therefore the expensive insertion term retains roughly

  I * N / k_s

unless the component gaps can be charged to something better.

This is essentially the original coupling reappearing in another form.

## What would be needed to make supergroups useful

One of the following would have to hold:

1. connect the pieces by actual graph edges that can be globally charged;
2. prove the connector endpoints always have the same home;
3. charge component gaps to a separate globally-small event;
4. change re-selection so a supergroup does not require a new pivot when its
   active component changes;
5. use a different frontier representation than one pivot per residual group.

Arbitrary virtual connectors do not help: every connector whose endpoints
have different homes simply recreates the same R-P term, and unlike PT edges
it has no graph-edge uniqueness charge.

So cross-tree aggregation is correctness-compatible but does not, under the
current N4-style analysis, decouple the pivot-count scale from the local
FindPivots scale in the worst case.
