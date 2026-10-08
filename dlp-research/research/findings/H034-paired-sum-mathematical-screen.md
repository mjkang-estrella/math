# H034 paired-sum mathematics: dense negative, sparse positive premise

Status: Sol proposal, independent Astra review completed, root checked the
combinatorics and consulted the primary Poisson theorem. These are mathematical
screens, NOT a verified complete-work improvement, a Lean proof or a novelty
claim. No numerical experiment. Full sparse solver contract/cost/prior-art review
remains open in H034-sparse-paired-sum-hypothesis.md.

## Literal all-pair prefix loses its apparent collision advantage

Seeds P_i=a_iG+b_iQ have fixed labels/order independent of the unknown scalar.
After seed r, emit x(P_r±P_i) for i<r. Leaves have formal vectors e_i±e_j.
A signed leaf/seed equality gives a vector supported on at most four seeds.
Modulo global sign, four distinct indices have8 sign patterns, regardless of
which edge pairing produced the equation. Conservative counts for smaller
supports give the coverage bound

    8*C(r,4)+32*C(r,3)+8*C(r,2)+2r.

Each equation with nonzero resulting target coefficient determines at most one
scalar; zero identities give none. Complete rows emit t=r(r−1) keys. Bounding
partial rows by the next full row yields coverage<=t²/3+O(t^(3/2)). Thus for
uniform k and L=ceil(sqrt(3q)), the tail-sum identity implies

    E[min(T,L)] >= (2/sqrt(3))sqrt(q)−O(q^(1/4)).

This counts final seeds/leaves/infinity only. Testing K=O(r log(q)) construction
helper keys contributes O(Kt+K²) possible signed relations; the lower-order
remainder becomes O(q^(1/4)log(q)+log²(q)). G,Q or helpers must not be free
extra detectors omitted from this accounting.

A regular row of n seed pairs costs5nM+2nS+I−3M for2n keys. With fixed arithmetic
prices, total finite inversion/seed setup corrections are lower order at
r=O(q^(1/4)). Exceptional pairs require their actual dispatch costs: distinct
fixed seed labels up to sign bound each exceptional equality to at most one
target per sign, and a permanent zero seed needs separate handling. Subject to
this literal arithmetic implementation and sufficient square-root storage, the
leading2/sqrt(3) key count loses to H019's2sqrt(2)/3 at the same limiting key
price. No arbitrary DAG, adaptive schedule or different kernel is excluded.

## C4-free sparse graph removes the repeated matching equations

Now assign IID uniform(a_i,b_i) to vertices of a simple C4-free graph. For any
FIXED input k, z_i=a_i+b_i k are IID uniform Fq; b is independent of z. Assume
q is odd. Emit two signed-sum keys per edge, in fixed order. For a prefix of m
edges with maximum degree Delta, the number of distinct four-support equations
modulo global sign is exactly

    N=8*[C(m,2)−sum_v C(deg(v),2)].

Each disjoint edge pair supplies8 patterns. Another pairing on the same four
vertices would create a C4. Distinct ±1 coefficient vectors are nonproportional
over odd Fq, so their zero events have probability1/q and distinct pairs have
joint probability1/q². This pairwise statement is NOT mutual independence.

Take an event's dependency neighborhood to include every event sharing one of
its four vertex variables. A conservative size bound is32 Delta m (increase by
one harmlessly if needed for self-inclusion). Events outside depend jointly on
disjoint independent variables; the residual dependence term is zero. The
zero-event bound from [Arratia–Goldstein–Gordon, Theorem1](https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/AGG-1.pdf)
then bounds the Poisson error by

    O(min(1,1/lambda)*N Delta m/q²), lambda=N/q.

At m=Theta(sqrt(q)), Delta=O(q^(1/6)), this is O(q^(−1/3)); meanwhile
N=4m²−O(m Delta+m). For t=2m=x sqrt(q), four-support survival therefore tends
to exp(−x²). Root and reviewer read the theorem's dependency definitions and
zero-event bound, rather than transferring an empirical random-walk law.

Additional shared-vertex patterns number O(m Delta), giving probability
O(m Delta/q)=o(1) in this regime. Seed zero, leaf infinity and exceptional
denominators still need explicit recovery/dispatch. For a nonzero formal relation
selected using only point geometry and fixed ordering, its target coefficient
is uniform conditional on that geometry. Null probability is1/q; selection
must not inspect the coefficients first. Resolve x-equality signs by trying
and verifying the corresponding candidates or paying for point reconstruction.

## Stopping, caps and full cost remain separate

A constant cap A sqrt(q) leaves constant failure probability. Its truncated
mean is not automatically the uncapped sqrt(pi)/2 coefficient. An independently
blinded fallback can restore a uniform-input baseline expectation after the
candidate's nonuniform failure posterior; its full work is paid.

Alternatively a slowly growing cap, suitable prefix-degree bounds and lazy
graph enumeration permit a tail argument: pairwise independence gives
Pr(no four-support event)<=1/lambda. Together with the fixed-x limit, the
integrable O(q/t²) tail supports the suggested sqrt(pi)/2 mean with a properly
charged O(sqrt(q)) fallback. Eagerly generating every cap-sized edge would
invalidate a free-generation interpretation. This is a proposed asymptotic
contract, not yet an executable or formalized full-cost theorem.

Uniform graph construction, random bits, seed multiplications, graph indexing,
peak scratch, descriptors, exact lookups, exception branches, verification,
clearing and fallback remain in the ledger. Compare against H019 AND applicable
grumpy constants, with their distinct proof/evidence status. No clock/bit-work
gain follows from the geometric premise alone. Verified improvement NONE.

Process: proposer `/root/h010_early_dependencies`; independent mathematical
critic `/root/h007_additive_relations`; root source/algebra checks. No edits,
imports, experiments or children by reviewers. Root integrates. Focused Lean
work is deferred until the complete candidate survives the remaining reviews.
