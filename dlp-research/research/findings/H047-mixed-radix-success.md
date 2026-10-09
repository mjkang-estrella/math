# H047 two randomized long progressions preserve success

2026-10-09 UTC. Independently checked paper construction following H046's
independent-direction construction. Not an accepted solver, experiment or
complete-work improvement. Native Astra mathematical review completed after
its coordinate fallback finished; the earlier proposed Sol review was removed
before it started, avoiding duplication. Baseline exponent1/2; verified gain NONE.

## Construction and reviewed success law

Fix q prime, Q=[k]G and fixed public filter S of size L independently of fresh
randomness. Let M=n²<q. Choose independent uniform a,b,c,d,h,g in Fq and set

    A_i=Q+[a+i h]G,     B_j=[b+n j h]G,
    C_i=[c+i g]G,       D_j=[d+n j g]G,   0<=i,j<n.

Each left pair sum is U_t=Q+[a+b+t h]G, with t=i+n j in [0,M).
Each right pair sum is V_u=[c+d+u g]G, with u=i'+n j' in [0,M).
The individual four short lists are NOT independent. Instead, (a+b,h) and
(c+d,g) are independent uniform pairs; the two long pair lists are independent
of one another, and each has pairwise-independent entries because M<q.

Count Z with U_t=-V_u in S:

    mu=E[Z]=M²L/q²,
    Var Z = mu(1-L/q²) + 2 M²(M-1)L(q-L)/q^4
          <= mu + 2M³L/q³.
    Pr(Z>0) >= 1/(1+1/mu+2q/(ML)).

There are M² diagonal indicator terms and M²(M-1) ordered distinct pairs
sharing each one of t,u. Terms with both indices different have zero covariance
by pairwise independence of the two long lists. This reproduces the H021
moment bound after M=n², but through a different construction rather than an
invalid four-independent-short-list assertion.

At actual density delta=L/q of order q^(-gamma), 0<gamma<1, and
M of order q^((1+gamma)/2), the moments give constant success.
Each intermediate output count has mean M delta and variance M delta(1-delta).
A cap ceil(C M delta), C>1, loses at most 1/((C-1)² M delta)=o(1) probability
per side by Chebyshev. Rejecting h=0 or g=0 has probability 2/q-1/q²,
at most 2/q unconditionally; exact moments must
not be asserted after conditioning without a correction. All rejection,
reporter abort and failed-attempt work remains paid.

## Extraction and costs

A returned oriented equality gives k=-(a+b+t h+c+d+u g) modulo q, followed
by kG=Q verification. Mixed-radix t gives its short-list indices if needed.
No hidden inverse map or secret-range restriction is used. Constructing four
short lists costs O(n) point additions and O(log q) initial scalar-multiplication
work for a constant number of bases/steps, plus labels and the Q translation.
Alternatively a reporter can consume the long progression's explicit start,
step and M directly; enumerating all M points is NOT a free setup operation.

Unlike H046's general two-direction grids, each side is genuinely one
length-M progression, with independent directions across the sides. This
may fit an elliptic index system, but its filter, block formation, signs,
output extraction, memory, sorting, verification and bit costs still need an
actual circuit. Degree/resultant bounds and BDLS evaluation upper bounds do
not themselves supply a faster reporter. No gain is claimed from fewer random
parameters or a correctness lemma alone.

The role of independent directions is important. If both mixed-radix sides
use the SAME step h with independent uniform offsets, then all total sums
have the form T+v h for 0<=v<=2M-2. Averaging over uniform T, an unfiltered
relation has probability at most min(1,(2M-1)/q), tending to zero in this
parameter regime. The construction uses independent h,g instead.

## Decision gate

Native Astra /root/h007_additive_relations independently checked covariance,
counts, oriented extraction, conditioning, construction and the shared-step
counterexample; no mathematical blocker found. Root derived and independently
rechecked the formulas. The accepted success construction repairs a named
algorithm gate; exact index-system compatibility still needs the actual reporter.
The next substantial question remains a compact filter reporter meeting the
H046 complete-cost threshold, not a generic theorem library or a new trial.
No scripts/imports/experiments, seeds, curve instances or Lean/Audit change.
H034's consumed cap is unchanged. This is a paper result, not a Lean theorem;
no novelty claim, fabricated runtime or universal lower bound. Project validation
is recorded in STATE and does not certify these paper calculations.
