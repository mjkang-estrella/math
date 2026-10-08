# H025 low-memory screens: orientation and bounded strides

2026-10-08. Native Astra independent ideation completed; root independently
checked the algebra and counting below. No surviving positive complete-work
rationale and no new experiment admitted. Verified improvement NONE.

## Oriented translation bursts: conditional cost screen

Retain oriented(μ,u), without sorting, representing P rather than its reflection
class. Use L−1 translations and one deterministic public jump, retaining phase.
Labels remain affine; equality of COMPLETE states coalesces. Arbitrary jump
needs4M+S+2I (the second root is unnecessary), leading10M+S with large batches.
Together with regular4M+S, the mean leading arithmetic is(4+s)+6/L in M units,
s=S/M. Finite inversions, initialization, phase, exceptions, table/replay and
record work are additional.

Even granting an optimistic random-map law on only q point states, disregarding
any phase penalty, the limiting ratio versus matched negation rho is
sqrt(2)*(4+s)/(5+s)>1 for0<=s<=1: squaring reduces to7+6s+s²>0.
This is a CONDITIONAL arithmetic rejection under that collision law. A different
structured discovery law is not excluded, but no positive reason for it was
supplied. Equal μ across orientations is not equality of complete coalescing
states; noncoalescent collision detection would require its own storage/discovery
accounting. Do not convert this into a universal orientation lower bound.

## Bounded-stride cross-seed coverage: exact screen

Let H=G/2 and T=P−H in an odd prime-order group of order q. At each step,
translate by dG with integer |d|<=s, optionally reflecting P→G−P. Stride and
reflection choices may depend arbitrarily on coordinates. Inductively after
at most L steps,

    T_j=epsilon_j*T_0+c_j*G, epsilon_j in{−1,1}, |c_j|<=sL.

Translation adds d to c; reflection negates the entire centered expression.
Thus any signed collision between two such trajectories implies

    T_0=±T'_0+rG, |r|<=2sL.

For independent uniform starts, each fixed sign/r relation has probability1/q.
There are at most2(4sL+1) choices, so a union bound gives

    P(any cross-trajectory signed collision)<=min(1,2(4sL+1)/q).

Modular overlap only decreases the bound. Coordinate adaptivity does not defeat
it: every resulting relation lies in that same fixed set. This does not supply
L²/q independent chances when s is fixed and L grows. Within a trajectory,
the initial coefficient either cancels or constrains the seed to a comparably
small set; do not assume useful-label probability from this observation.

Scope excludes doubling, unbounded/large jumps, correlated starts and general
affine maps. Large jumps can remove this relation-count restriction, but their
construction/normalization must be paid. No generic-group impossibility or
coordinate-aware lower bound is asserted.

## Decision

No second escape-rate run or tuning of H024 fixtures. A new low-memory survivor
must combine enough distinct useful relations with an inexpensive coalescing
quotient-state update. The bounded-stride count and oriented arithmetic do not
provide that combination. These are scoped derivations of familiar walk
components, not a newly discovered attack or a novelty claim.
