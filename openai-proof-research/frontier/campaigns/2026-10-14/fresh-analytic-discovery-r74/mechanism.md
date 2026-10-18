# A moment-free route: preserved bigeodesics, but a dependent metric

Research only. The full prospective target is: for every Borel nonatomic
probability law G on [0,infinity), with all weights finite, iid planar
nearest-neighbor first-passage percolation has almost surely no bigeodesic.
There is no moment hypothesis. Bounded laws are already covered by source212.
This target is not proved or frozen as a completed candidate. Full083 remains
unchanged and unfinished; this is a distinct family switch.

## 1. Why uniform clipping cannot be a path-preserving reduction

Assume G is unbounded. Fix M>0. Choose a finite interval (a,b) of positive
G-mass with a>M and a>0, then choose H>3b with G((H,infinity))>0. On a unit
square require three consecutive edges to have weights in (a,b), and the
remaining edge, joining the endpoints of that three-edge path, to exceed H.
This is a positive-probability valid pattern in Jacquet2310.04091v1,
Definition1.2: the support is unbounded, so the extra face condition is absent.
Within the square the unique optimal path between its designated adjacent
corners is the three-edge detour. Under t'_e=min(t_e,M), that detour costs 3M,
whereas the direct edge costs M. Thus any original geodesic taking this pattern
is not a geodesic in the clipped environment.

Jacquet Theorem1.4 applies because a nonatomic finite law is useful (its atom
at its support minimum is zero) and has unbounded support. For each endpoint
x it bounds the probability that any geodesic from 0 to x has fewer than
alpha|x|_1 pattern occurrences by C exp(-c|x|_1). Summing over x and applying
Borel–Cantelli shows that every sufficiently distant endpoint has no such
geodesic. Every infinite ray from 0 has endpoints arbitrarily far away, so
its segments take the pattern. Countability of starting vertices proves that
almost surely no original infinite ray is a ray for this fixed clipped metric.
A countable intersection handles all positive integer clipping thresholds.
No simultaneous assertion for uncountably many M is needed.

This is a direct technical corollary of a credited primary theorem, not a
new substantial nomination. It rules out a specific preservation argument,
not passage of some other geometric property between metrics.

## 2. A circuit-dependent cap that does preserve every bigeodesic

Here is a deterministic statement. Let t_e>0 be arbitrary finite weights.
Fix M>0 and for every edge e suppose there is a finite simple lattice circuit
C_e, all of whose weights are <=M, with both endpoints of e strictly inside.
Write L_e=number of edges of C_e and choose finite K_e>=2ML_e. Suppose also
K_e>=M, as is automatic here. Set s_e=min(t_e,K_e).
Then every t-bigeodesic is an s-bigeodesic, with every edge on it unchanged.

Proof. Fix a t-bigeodesic gamma. Its two tails leave every finite set.
For any circuit C, its first and last contacts along gamma enclose every
vertex of gamma strictly inside C. The gamma segment between these contacts
has cost at most the cheaper of the two C-arcs, hence at most ML/2, where
L is the circuit length. If gamma used an edge e changed by the cap, its
segment crossing C_e would cost at least t_e>K_e>=2ML_e, a contradiction.
Thus gamma uses only unchanged edges. Circuit edges are also unchanged:
t_f<=M<=K_f for each such edge f.

Let a,b be vertices on gamma and let pi be any finite s-walk from a to b.
If pi contains a changed edge e, consider C_e and delete a portion of pi
containing that occurrence as follows. If a,b are outside or on C_e, replace
from a preceding boundary contact to a succeeding boundary contact by a
C_e arc. If a is strictly inside and b outside, replace the prefix through
the last boundary contact after e by a gamma segment from a to a boundary
contact followed by a C_e arc; use the reversed construction when b is inside.
If both endpoints are inside, replace the entire walk by gamma[a,b].
The gamma pieces used are between the outermost contacts of gamma with C_e,
so have cost <=ML_e/2; a shortest circuit arc also costs <=ML_e/2.
Each replacement therefore costs at most ML_e, whereas the removed portion
costs at least s_e=K_e>=2ML_e. Boundary endpoints are treated as outside.
All added edges belong to gamma or the circuit and are unchanged. Hence the
number of changed-edge occurrences strictly decreases. Repeating finitely
many times produces a walk using only unchanged edges whose original cost
is <= the s-cost of pi. Original minimality of gamma gives
cost_t(gamma[a,b])<=cost_s(pi). Since gamma itself is unchanged, this proves
s-minimality of every finite gamma segment. The statement holds simultaneously
for all bigeodesics, without choosing one measurably.

## 3. Application of the cap and its precise defect

For iid finite G choose M so q=P(t_e>M)<1/3. M-open edges are those with
t_e<=M. For an edge e let L_e be the minimum length of an M-open simple
circuit strictly surrounding both its endpoints. Such a circuit exists a.s.
One elementary Peierls justification: in the square annulus between a fixed
box around e and a box of radius R, absence of a surrounding open circuit
forces a closed dual crossing. After erasing loops this has at least R-O(1)
edges. There are finitely many possible starting dual edges at the inner
boundary, and at most 4*3^(n-1) length-n choices. Its probability is at most
C sum_{n>=R-O(1)}(3q)^n. Planar finite-annulus duality supplies the crossing
alternative. An open circuit within the radius-R box has at most CR^2 edges.
Consequently P(L_e>CR^2)<=C exp(-cR), and L_e has every finite moment.
Countability supplies the circuits for all edges. This is an elementary
percolation argument; no independence between L_e at different edges is claimed.

Introduce independent U_e uniform in (0,1) and use
 K_e=M(2L_e+U_e),  s_e=min(t_e,K_e).
The preceding deterministic proof applies. Also s_e<=M(2L_e+1), so every
s-edge has every finite moment. The construction is translation-covariant
and invariant under lattice symmetries since the minimum length is used.
It is a factor of the iid original weights and auxiliaries, hence stationary
and ergodic. The jitter avoids the obvious atoms of an integer-length cap:
conditional on the entire open/closed edge configuration, the truncated
original weights and auxiliary U_e are independent and nonatomic across
edges, and L_e is fixed. Thus finite distinct simple-path costs have no ties.

Nevertheless this transformed law fails Ahlberg–Hoffman A2(v), not just
an unverified abstract independence test. Consider e={(0,0),(1,0)} and the
length-10 rectangular circuit with corners (-1,-1),(2,-1),(2,1),(-1,1).
The event that its ten observed s-weights are <=M has positive probability
and is measurable without s_e. Observed s_f<=M is equivalent to t_f<=M,
because every cap exceeds M. On this event L_e<=10, and hence s_e<21M.
On the other hand P(s_e>21M)>0: force all original weights in a sufficiently
large finite box containing every circuit of length <=10 surrounding e
(including t_e) to exceed 21M. This has positive probability for unbounded G.
Then L_e>10, so its even integer length is >=12 and K_e>24M, while t_e>21M.
Thus the conditional probability of s_e>21M vanishes on a positive-probability
outside event although its marginal is positive. This violates exactly A2(v).
It also proves that the transformed weights are not iid.

## 4. Remaining full-target obligation

Source212 requires iid G and its structural input uses global original-metric
shape approximation, simultaneous linear Busemann asymptotes for every ray,
and fixed-functional uniqueness/coalescence/backward finiteness. Cerf–Théret's
regularized shape theorem does not establish those assertions for either the
original heavy-tailed metric or the circuit-capped dependent metric.
Ahlberg–Hoffman's dependent-law alternative is unavailable by the explicit
failure above. Nor does the iid source's spatial perturbation budget apply
automatically to the cap field. A proof must retain the original iid environment
and establish the needed ray structure on a regularized backbone, or prove a
new structural/perturbation theorem for this specific dependent cap law.
No such theorem is proved here. The preserved-path cap is supporting mechanism
work only, and neither it nor the clipping obstruction is nominated.
