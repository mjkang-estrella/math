# H015 component-aware admission: conditional constant-factor hypothesis

2026-10-08. Native Sol /root/h010_early_dependencies proposer; separate native
Astra /root/h007_additive_relations mathematical/cost reviewer. Root integrates
and checks their algebra. No run, implementation, Lean theorem or validated gain.
Targeted prior-art followup completed; global novelty remains unresolved.
Single-target exponent unchanged.

## Frozen proposed attempt

Input K distinct full-range targets Q_i=d_i*G in a known odd prime-order group.
Objective: recover ALL K logs, not any one. Use one target-independent point-only
32-jump adding walk with paid J_j=kappa_j*G, separate domain-separated jump/DP
hashes and negation canonicalization. Every canonical negation changes BOTH
coefficients in P=a*G+sigma*Q_i, sigma in{+1,-1}. Hashes/cycle behavior are not
yet implemented or performance-validated; this is an operation specification.

Maintain a signed weighted forest d_i=alpha_i*d_r+c_i with alpha_i in{+1,-1},
known flags, original-target root representatives and retained endpoint counts.
Keep the first full-point record at each endpoint with original label and seed;
normalize lazily through the forest on lookup. Sum counts on union. A solved
component's retained records remain available as known-log anchors.

Choose W a power of two with K*W^2<=q<4*K*W^2 when K<=q; for K>q/4 use W=1.
Use a frozen predicate of mean spacing W. First obtain a paid known-log endpoint
from a fresh uniform a*G. Subsequently select an unresolved component with the
fewest retained records, ties by original representative index. Start uniformly
with a*G+sigma*Q_r using independently sampled a and fair sigma. Stop each chain
at its first distinguished point or8W steps; no history-dependent successor is
introduced. At most16K chain starts including initial-anchor retries and4K
distinct stored endpoints; otherwise FAIL. Success requires all logs recovered
and K scalar-multiplication verifications. Repeated attempts repay setup/failures.
The128KW step cap is not an expected runtime or success theorem.

## Exact correctness and geometric limitation

Normalize the record to P=(a+sigma*c_i)*G+(sigma*alpha_i)*Q_r, written A*G+S*Q_r.
Different unresolved roots yield a signed affine relation. Same-root collision
gives (S1-S2)*d_r=A2-A1; coefficient +/-2 solves the root, coefficient0 is
redundant. A hit on a known component solves the queried unknown root. Each useful
event reduces the number of unknown root variables by ONE, even if it solves
many targets in that component. K independent reductions are needed overall.

The independent reviewer supplied a stronger exact observation. Conditional on
the entire existing table/forest, fresh uniform a makes a*G+sigma*Q_r uniform on
the group and independent of sigma, for ANY selected root. A fixed point-only
map and cutoff therefore give the SAME geometric path/endpoint/failure law for
every root. Final sigma is still fair conditional on the path: canonicalization
multiplies it by a sign determined only by that path.

Let nu be this actual subprobability endpoint law (missing mass is cutoff failure),
T the stored endpoint set, and T_r the subset owned by the queried unknown root.
An endpoint collision outside T_r always gives a reduction; inside T_r it does
so with probability1/2. Thus the EXACT per-start useful-collision probability is

    nu(T) - nu(T_r)/2.

Minimum true basin mass is the locally optimal objective; minimum RECORD COUNT
is only a proxy. One endpoint of mass0.4 can be worse than two each of mass0.001.
This is a counterexample to the proxy's universal optimality, not an established
ordinary-curve walk family. Scheduling changes dependency usefulness, not raw
endpoint collision geometry. Local rank efficiency lies between1/2 and1 for
any policy querying unresolved roots; this is not a total-runtime factor theorem.

With fresh independent signs, a stopped-trial Chernoff argument bounds the JOINT
event {4K endpoint collisions occur before other caps AND fewer than K reductions}
by exp(-K/4). Pad after stopping with fair trials. Do not assert that bound
conditionally on reaching4K: the cap-reaching event can depend on prior signs.
This does not prove the proposed attempt reaches4K collisions or succeeds with
constant probability. Root added the joint-event qualification to the review.

## Baselines, paid costs and gate

Compare uniform unresolved ROOT selection, uniform unresolved ORIGINAL TARGET
selection (different component-size weighting), sequential solving with retained
endpoint reuse, and optimized known preprocessing/graph methods at equal memory.
Never keep querying solved targets in a supposedly competent comparator. All
comparators receive the same reusable map, setup and available automorphisms.
See H015-preprocessing-baseline.md: heuristic setup sqrt(qM) plus K*sqrt(q/M),
balanced at M~K, already has sqrt(qK) principal group-work scale.

Charge starts/scalar multiplications, jump setup, every failed chain, records,
hashing/lookups, signed-forest normalization/updates, scheduling, propagation,
and all verification. Memory includes4K full records, O(K) forest/scheduler,
jump tables and multiplication workspace. Sign-cycle loss with a cutoff-only
walk may dominate; batching is not automatically preserved by adaptive admission.
Use actual basin geometry: uniform endpoint birthday probability W/q is wrong
for the usual chain-coalescence heuristic W^2/q. Neither heuristic proves this
fixed walk's success law.

The remaining proposed benefit is a material finite complete-work constant,
not an exponent change. No evidence yet meets a10% saving gate. Actual FJM2014
and published May--Ostuzzi2025 algorithms have now been inspected; the precise
minimum-count rule differs from those schedules, without proving global novelty.
See H015-preprocessing-baseline.md for access commands and step-cost limits.
Require a favorable full-work case before a small paid synthetic functional-graph
diagnostic. Any diagnostic
must compare the strengthened schedules, include caps/failure probability and
seeds, and cannot establish ordinary-EC scaling by itself. No engine authorized
on the strength of this paper card alone.
