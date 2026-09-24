# Why the weaker CertPull contract is not yet a faster implementation

The candidate CertPull contract removes an unnecessary logical requirement:

  arbitrary non-certifying low D keys do not need to be selected merely
  because they are below Bi.

That is a real correctness-interface observation.

However, the certificate predicates are semantic:

  Complete d y
  D[y] = dis(y)
  a residual group contains a complete y.

The RAM program does not know dis(y) or Complete(y) directly.

## Frontier minima explain the priority structure

At call entry, FP1 says the union of the pivot groups is a frontier (besides
the completed W region).  Observation 2.1(2), used by C-HD itself, says the
minimum label of a frontier is complete.

BM.7 chooses the minimum-label member of every pivot group.

Therefore the minimum among the group pivots is exactly the kind of
observable object from which the proof obtains a complete certificate.

After a child returns and removes parts of the frontier, the same logic
repeats on the residual groups: the next relevant complete certificate is
revealed by the new minimum frontier/pivot label.

This explains why the implementation stores all current pivots in D and why
Pull behaves like a batched priority operation.  The semantic CertPull
contract can say "only pull certifying pivots", but deciding which pivots
certify progress is itself essentially the frontier-minimum problem.

## Consequence

A weaker correctness contract does not automatically evade the
p log(p/M) ordered-pivot cost.

To turn CertPull into an algorithmic improvement, one needs *additional
observable information* beyond the current label/key state, for example:

1. FindPivots returns a computable witness that a particular group contains a
   complete vertex;
2. recursive calls return certificate provenance that survives merges;
3. a randomized/verified candidate mechanism identifies enough certificate
   groups without globally ordering all pivots;
4. a new frontier representation makes the next certificate available
   structurally rather than through label order.

Without such metadata, a safe deterministic implementation may still have to
treat every sufficiently low pivot as a possible certificate.

## Research status

- Logical weakening: concrete and being kernel-checked in
  CertPullSpecCandidate / CertPullCorrectnessCandidate.
- Efficient implementation of the weaker interface: open.
- Claim that CertPull alone improves the asymptotic bound: not justified.
