# Candidate bound blocker audit

Date: 2026-09-23

Status labels: RESOLVED-SOURCE means the relevant fact already exists upstream; PAPER-CLOSED means the informal argument is now complete; FORMAL-OPEN means Lean integration remains.

## 1. Full-call +1 in N4

Status: PAPER-CLOSED / FORMAL-OPEN.

Upstream concludes `g_j <= c_j+1` because c_j bichromatic edges leave c_j+1 monochromatic components. BM.23 re-selects only when the residual group is nonempty, so there is always one additional terminal home/component beyond the g_j re-selection homes. Therefore `g_j <= c_j` at paper level.

## 2. Initial pivot insertion charged as O(t)

Status: RESOLVED-SOURCE / FORMAL-INTERFACE-OPEN.

`newC` starts with one block; upstream `insertL_blocks` / `insManyC_blocks` preserve block count; `insManyC_cost_le` with NB=1 gives constant cost per initial pivot. The remaining work is to stop `BMCost.initCost` from using the generic evolved-structure insertion charge.

## 3. Final residual group has an own/none home

Status: RESOLVED-SOURCE / FORMAL-TRANSPORT-OPEN.

`LInv.Pmem` puts residual group members outside accumulated child U. A full call returns S, and the final result is `sigma.U union W'`, so residual members lie in W'. Upstream `BMTrace.callC_log` already uses the same argument to prove `wr_own` for sources of W' relaxation edges. `Ranges.home` returns none for parent-returned vertices in no child.

## 4. I-weighted emptying telescope

Status: PAPER-CLOSED / FORMAL-OPEN.

Per iteration, marked and emptied groups are disjoint and both meet the child. Exact identity: `nonempty_next + emptied = nonempty_now`. This yields an I-weighted telescope and isolates the expensive insertion coefficient on actual marked events.

## 5. Credit survives CostLog abstraction

Status: FORMAL-OPEN; currently the largest proof-engineering issue.

The useful inequality has `cost + I*p` on the left. Existing `RecCost/budOf` retains only an ordinary nonnegative upper bound on cost, so a refined interface must carry the credit until `CostLe` can cancel it using the global Cr/Be bound.

## 6. Partial calls

Status: RESOLVED-ARITHMETIC.

For partial calls, p <= |S| and the existing `t|S|` term already pays expensive re-selection work. The new theorem does not need to remove a partial-call p term separately.

## 7. Cheap O(k p) work after removing t p

Status: RESOLVED-ARITHMETIC.

Full calls use p(k-1) <= |U|+|Fo|; partial calls use p<=|S| and 3k<=t. Thus cheap pivot/group work can be absorbed without an unconditional t*p term.

## 8. Failed-search correction with k=4

Status: RESOLVED-ARITHMETIC.

`k^2(m + NL/t)` becomes O(m + N log N/t^2). Under `log N <= t^2 d`, the second term is O(m).

## 9. Recursive DLazy insertion under smaller t

Status: ASYMPTOTICALLY-CLOSED / FORMAL-OPEN.

On the certified density branch, the new parameter specification yields `log N = O(t^8)` and delta/L polynomial in t, so separator-stack logarithms remain O(t). A replacement for `mc_lgN_le` and `mc_ins_le` is still needed in Lean.

## 10. A_M extra

Status: RESOLVED-ARITHMETIC.

The paper-level extra O(N t + m log(t delta)) remains below the candidate square-root term over the audited density window. At alpha=0, N t has the same log-power as the candidate and is absorbed in the same order.

## 11. Preprocessing and m log(t delta)

Status: RESOLVED-ARITHMETIC on alpha<=3/4.

For d=log^alpha n, both are n log^alpha n * O(log log n), while the candidate is n log^((1+alpha)/2)n; the exponent gap is positive for alpha<1.

## 12. Prior work

Status: SEARCHED, not a proof of novelty.

The closest published directed deterministic comparison-addition bound remains DMSY26: O(m sqrt(log n) + sqrt(m n log n log log n)). No published O(sqrt(m n log n)) directed bound was found in the targeted 2026 search.

## 13. Kernel compilation

Status: OPEN.

The current working environment has no Lean/Lake toolchain and no shell network access. All candidate Lean files in this repository are explicitly marked uncompiled. Final theorem claims wait on an actual Lean 4.34 build and kernel audit.