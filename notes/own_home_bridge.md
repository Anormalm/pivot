# Own/final home bridge

## Source facts

The upstream `Ranges.home` definition has three cases:

1. if `v` is in a direct child return `U_Y`, then `home_X(v)=some Y`;
2. otherwise, if `v` is outside the parent return `U_X` and its fixed value lies in a child range, then `home_X(v)=some Y`;
3. otherwise, `home_X(v)=none`.

Therefore any vertex that is in the parent return but in no child return has
home exactly `none`.

## Why a final residual group gives such a vertex

At the final child-loop state, upstream `LInv.Pmem` says:

```text
y in sigma.P_j  =>  y notin sigma.U
```

where `sigma.U` is the accumulated set returned by children.

Also:

- residual `sigma.P_j` is a subset of the original group `P0_j`;
- every original group is a subset of the call frontier `S`;
- in a full call, `S subset U_parent`;
- the final call result has
  `U_parent = sigma.U union W'`.

Hence any residual-group member must lie in `W'`.

Every direct child return is accumulated into `sigma.U`, so such a `W'`
member is in no child return. Thus it contributes the distinct home colour
`none`.

## Refined colour inequality

For each original pivot group `g`:

- every child meeting `g` contributes a distinct colour `some Y`;
- if `g` has a final residual/own member, that contributes `none`.

Thus

```text
childMeetCount(g) + ownIndicator(g)
    <= # distinct home colours(g).
```

Summing over groups and reusing the existing PT-piece theorem gives the
candidate

```text
mkOf + ownGroupsOf
    <= p + total bichromatic piece edges
    <= p + |Cr| + |Be|.
```

Combined with the strengthened I-credit loop telescope:

```text
loopCost + I p <= cheap + I(mkOf + ownGroupsOf)
```

we obtain

```text
loopCost + I p
  <= cheap + I p + I(|Cr|+|Be|)
```

and can cancel the `I p` term.

## Remaining formal transport

The only nontrivial plumbing step is exposing, at the record/log level, that
parent `W'` is disjoint from every direct child `U_Y`.

That fact is already implicit in the concrete loop/finalization semantics:
all child returns are accumulated into `sigma.U`, while `W'` is defined
outside `sigma.U`.

The existing branch draft `drafts/OwnHomeCandidates.lean` isolates this as
`child_U_disjoint_parent_W'_candidate`.
