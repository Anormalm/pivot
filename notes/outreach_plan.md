# Outreach plan for C-HD authors

Target date: 2026-09-23 evening (Singapore time)

## Primary recipient

Geby Jaff, author of the Vals post "A Faster Shortest Path Algorithm"
(20 Sep 2026).

Public post:
https://www.vals.ai/blogs/faster-shortest-path-algorithm

A public direct email address was not found in the post. If no address is
available from an existing contact route, LinkedIn is the clean fallback:
https://www.linkedin.com/in/geby-jaff

## Goal of the first message

Do not pitch "we proved a faster algorithm."

The useful first-contact goal is to get an expert sanity check on one narrow
accounting question:

> Is there a hidden reason the full-call BM.23 analysis needs one exceptional
> expensive re-selection per pivot group, or can the final residual/own
> `none` home remove that exception?

This makes the message easy to evaluate and lowers the cost of replying.

## Claims safe to make

1. The upstream executable semantics re-select a group only when the current
   pivot is returned **and** the residual group is nonempty.
2. For a full call, the upstream invariant has `S subset U`, so every
   original pivot-group vertex is eventually accounted for.
3. This gives the elementary candidate bound
   `g_j <= #represented homes(P_j) - 1`.
4. Existing C-HD tree-colour machinery already gives
   `#homes(piece) - 1 <= #bichromatic parent edges(piece)`.
5. The upstream cost proof currently uses a coarser child-meeting counter that
   preserves a once-per-group term.
6. BM.6 initial pivot insertion is separately charged with the generic evolved
   insert cost even though the structure starts with one block and Insert does
   not split.
7. If both tightenings formalize cleanly, retuning with constant `k` gives
   the **conditional** candidate core bound `O(sqrt(m n log n))`, hence
   `n log^(7/8)n` at `m=n log^(3/4)n`.

## Claims NOT safe to make yet

- "The C-HD theorem is wrong."
- "We proved O(sqrt(m n log n))."
- "The Lean proof already compiles."
- "This is a new SOTA theorem."
- "The 7/8 exponent is verified."

## Evidence to link

Canonical working repo:
https://github.com/Anormalm/pivot

Current PR:
https://github.com/Anormalm/pivot/pull/2

Useful files:
- `notes/exact_reselection_lemma.md`
- `notes/fresh_insert_audit.md`
- `notes/lean_patch_plan.md`
- `drafts/LoopCostFiniteCandidates.lean`
- `results/LOCAL_EXPERIMENTS.md`

## Experimental evidence

- 585,978 exhaustive states for the exact single-group adversarial
  characterization.
- 1,668,504 rooted-tree / 3-colour exhaustive cases.
- 50,000 random tree/group stress trials.
- 200,000 direct loop-telescope trials.
- No violations observed in any of these falsification tests.

These are sanity/falsification checks, not proof evidence for the full
complexity theorem.

## Recommended email structure

Paragraph 1:
- say you read the post and proof package;
- identify the exact files/terms;
- state the narrow suspected overcharge.

Paragraph 2:
- state the candidate one-group inequality;
- explain the existing home/bichromatic-edge bridge.

Paragraph 3:
- mention the separate fresh BM.6 insert overcharge;
- give the conditional parameter consequence in one sentence.

Paragraph 4:
- link the repo;
- explicitly say the improved theorem is not yet proved;
- ask the one narrow question.

## Best subject line

Possible tightening in C-HD pivot re-selection accounting

Alternative, more technical:

C-HD: can the full-call +1 per pivot group be removed?

Avoid leading with "11/12 -> 7/8"; put that consequence in the body after the
mechanism.
