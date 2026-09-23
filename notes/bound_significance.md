# Comparison with current directed bounds

Assume m = n log^alpha n and ignore lower-order poly(log log n) factors when comparing log powers.

Candidate core term:

    sqrt(m n log n) = n log^((1+alpha)/2) n.

DMSY26:

    m sqrt(log n) + sqrt(m n log n log log n).

For alpha>0, the first DMSY26 term has exponent alpha+1/2 and dominates its second term in log-power. The candidate exponent is (1+alpha)/2, smaller by alpha/2.

At alpha=0 both have log-power 1/2, but DMSY26 carries sqrt(log log n) in the second term while the candidate core does not.

DMM25 has exponent alpha+2/3, which exceeds the candidate by alpha/2 + 1/6.

Current C-HD has exponent (2+alpha)/3. The candidate improves it by (1-alpha)/6.

Therefore, if the proof closes, the consequence is broader than the profile alpha=3/4. Across 0<alpha<=3/4 the candidate has strictly smaller log-power than the current best expressions included in this audit; at alpha=0 it ties the DMSY26 log-power but removes its sqrt(log log n) factor.

This breadth is a reason to be conservative in external claims until the CostLog credit and parameter retuning are kernel-checked.