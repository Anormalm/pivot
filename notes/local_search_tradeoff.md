# Master tradeoff if local FindPivots becomes subquadratic

Suppose the per-search work could be reduced from O(k^2) to O(k^q),
with the corresponding successful/contact total changing from O(N k) per
layer to O(N k^(q-1)).

Keep the current exact ordered-pivot term.  For

  m = n log^alpha n,
  k = log^gamma n,
  t = log^beta n,

the four dominant exponent contributions are

  successful/contact: 1 - beta + (q-1) gamma
  ordered pivots:     1 - gamma
  failed searches:    alpha + q gamma
  edge/data work:     alpha + beta

Balancing them gives

  gamma = (1-alpha)/(q+1)
  beta  = q(1-alpha)/(q+1)
  exponent = (q+alpha)/(q+1).

At alpha = 3/4:

  q = 2.00  -> 11/12 = 0.9167
  q = 1.75  -> 0.9091
  q = 1.50  -> 0.9000
  q = 1.25  -> 0.8889
  q = 1.00  -> 7/8   = 0.8750

So the originally hoped-for 7/8 exponent corresponds to making the local
FindPivots search essentially linear in k.  The N4 sharpening alone does not
do this.

## Why q < 2 is difficult

The current HD1 proof pays O(k) relevant edge interactions per extracted
vertex, for up to k extracted vertices.  In a dense induced k-vertex region,
there can genuinely be Theta(k^2) candidate edges whose weights may affect
the local Dijkstra labels.

Changing the unsorted-array heap alone is not enough:

- ExtractMin can be improved;
- but decrease-key / relaxation work on the dense relevant edges remains;
- a Fibonacci heap only changes the priority-queue component, not the need
  to inspect arbitrary weighted internal edges.

Thus a q<2 result likely requires exploiting additional C-HD-specific
structure, reuse across overlapping searches, or a weaker local task than
the current exact bounded Dijkstra search.

This note is a parameter target, not a claim that such a local algorithm
exists.
