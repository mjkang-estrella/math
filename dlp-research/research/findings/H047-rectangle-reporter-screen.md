# H047 literal perimeter-priced rectangle reporting stays square-root

2026-10-09 UTC. Candidate-specific paper screen, not an arbitrary-reporter
lower bound. No new experiment. Best supported exponent1/2; verified gain NONE.

## Candidate and exact implementation assumption

Use the H046 randomized two-direction n-by-n grid and fixed public filter of
actual density delta. A recursive reporter partitions into dyadic squares,
tests squares for emptiness and descends through every occupied square until
it reports all matching indexed pairs. Suppose it incurs at least c*s fresh
operations on every visited side-s square, for a constant c>0 independent of
parameters. Explicitly rebuilding/reading local lists or products can have this
property. The lower charge is an assumption about that implementation, NOT an
inference from the degree of a polynomial or an upper bound on a known method.
Grant even an exact emptiness oracle; its implementation price remains charged.

## Expected work at one level

For a fixed side-s square, its hit count X satisfies

    E[X]=s² delta,    Var X<=E[X],
    Pr(X>0)>=s² delta/(1+s² delta).

These follow from the pairwise independence of distinct indexed pair sums in
H046-random-progression-success.md and the second-moment inequality. No Poisson
or independent-occupancy assumption is made. Choose a dyadic level with
s asymptotic to delta^(-1/2). At the H046 parameters
n asymptotic to q^((1+gamma)/4), delta asymptotic to q^(-gamma), 0<gamma<1,
this level exists with s<n for sufficiently large q. Ignoring boundary strips
retains a constant fraction of the grid if n is not a power of two.

Each of the order n²/s² squares has occupancy probability bounded below by a
positive constant. Every occupied square must be visited by complete reporting.
Linearity of expectation, without independence between squares, therefore gives

    expected charged work >= constant * (n²/s²) * s
                          = Omega(n² sqrt(delta))
                          = Omega(sqrt(q)).

An output cap failing with probability o(1), as in H046, cannot remove this
particular obstruction. Use as a proxy c*s times the number of occupied squares
at this level. It is bounded above by c*s times the total number of squares,
which is O(n²/s). Deleting an o(1)-probability event subtracts only o(n²/s)
from its expectation. On the remaining completed-report runs the actual work
dominates the proxy. This reasoning does not bound actual work from above.

## Disposition and remaining possibilities

Park this literal complete-reporting recursion as an exponent-improvement
candidate under its fresh-charge assumption. No constant-factor comparison is
established. A successful variant must avoid that price through amortized
sharing/caching, a different extraction organization, or an early matching
schedule that does not complete the pair reports. This proof does not apply
automatically to any of those alternatives. Sparse outputs and a block-norm
name alone do not supply the required sharing operation.

Native Astra /root/h007_additive_relations proposed the reporter screen during
its H047 construction role. It found no explicit competitive shared operator.
Root independently checked the pairwise moments, existence of the dyadic level,
complete-report visitation implication and bounded-proxy cap argument. This
elementary paper finding is not asserted to be a novel theorem in the literature.
No broad circuit lower bound or generic-coordinate impossibility is claimed.

No scripts/imports/experiments, seeds, new instances, Lean claims or Audit changes.
H034 cap remains consumed. Formal code unchanged since the passing H046 check;
that check does not certify this paper proof. Next potentially decisive evidence
is a concrete shared reporter or compatible early extraction schedule whose
complete costs escape the explicit assumption above. No infrastructure follows
merely from the missing operation.
