# Tail preservation, metric correction, and modification interfaces

Author collaboration in progress. These are supporting facts, not the full
moment-free no-bigeodesics theorem. The cap and circuit notation are those of
mechanism.md. A choice of a minimum-length circuit C_e can be made measurably;
the capped weights themselves depend only on its length.

## Finite endpoint correction (parent-suggested)

For a vertex x let E_x={e: x is strictly inside C_e}. If x is inside C_e,
the distance from x to e is at most L_e. The stretched-exponential bound for
L_e therefore implies sum_e P(x inside C_e)<infinity. Borel–Cantelli shows
E_x is finite a.s., simultaneously for all x. Put B(x)=sum_{e in E_x}t_e.
This is finite and can be chosen stationary, but need not be integrable.

For every x,y,
 0 <= T_t(x,y)-T_s(x,y) <= B(x)+B(y).
Indeed, start with any finite simple s-path. If a changed edge e on it has
neither endpoint x,y strictly inside C_e, replace the subpath between boundary
contacts surrounding that occurrence by a cheaper C_e arc. Added edges are
unchanged. Loop erase after each replacement, so the changed-edge count
strictly decreases. The remaining simple path only has changed edges in
E_x union E_y, each used once. Restoring original costs adds at most B(x)+B(y).
Take the infimum over competitors. No minimum-existence hypothesis is needed.
This is not a uniform almost-sure shape comparison: stationary finite B(x)
need not be o(|x|) uniformly over x.

## All ray tails are preserved in both directions

Let U_x be the finite union of the interiors and boundaries of C_e for e in E_x.
Every original ray from x eventually leaves U_x for the last time. Its tail
after that time is an s-ray. To see this, apply the competitor replacements in
mechanism.md to two vertices a,b of this tail. For a circuit containing x,
both a,b are outside or on it, so circuit replacement works without a backward
arm. For a circuit not containing x, if a or b is inside, the original ray
starts outside, enters, and eventually exits the finite circuit. Its segment
between outermost contacts has cost <=ML_e/2. The same mixed/both-inside
replacement works. Changed edges cannot occur on this tail: an original ray
can use a changed e only if x is strictly inside C_e, since otherwise its
crossing segment has a cheaper boundary competitor. Added edges are unchanged.
Thus every competitor is reduced as before and the entire tail is s-geodesic.

Conversely an s-ray from x can use a changed edge e only if x is strictly
inside C_e; otherwise its cost K_e>=2ML_e contradicts the circuit shortcut.
Only finitely many such edges exist. Beyond them its edges are unchanged,
and s<=t then implies that every finite segment of the unchanged s-ray tail
is t-minimizing. Hence the two metrics have exactly the same geometric ray
tails, although their rays rooted at a specified vertex can have different
initial segments. This does not establish a canonical measurable bijection
of rooted rays or coalescing families.

For an original ray p starting at x and any vertex y on p, a stronger one-sided
comparison is available:
 0 <= T_t(x,y)-T_s(x,y) <= B(x).
Use p's continuation past y to replace every changed edge whose protecting
circuit does not contain x, even when y is inside that circuit. Remaining
changed edges lie E_x; loop erase and restore their weights. This gives a
uniform-in-y correction along every original ray from x, on the same event.

## Finite original modifications have finite cap influence

If original configurations differ on finitely many edges F and the auxiliary
U_e are kept fixed, their caps differ only on a finite random set, almost surely
for any coupling in which each original marginal is absolutely continuous to
the iid law. For e far from F, a minimum-length protecting circuit in either
configuration cannot meet F: a circuit meeting F has length at least a constant
times dist(e,F), whereas L_e/dist(e,F) tends to zero uniformly over distant e
by the stretched-exponential tail and Borel–Cantelli, in both marginals.
Thus the minimum lengths in both configurations coincide (each minimizing
circuit is admissible in the other). Original weights and auxiliaries also
coincide there. If original weights only increase, every M-open circuit in the
new configuration was open before, so L'_e>=L_e and s'_e>=s_e everywhere.

This supplies finite-change metric bounds and monotonicity. It does not say
that a chosen rooted s-ray avoids the finite changed-cap region. A tail of a
rooted s-ray is an original ray, however, so if an upward original modification
avoids all its original edges, then its unchanged tail remains s-geodesic once
one knows it is unchanged under the cap modification. On an already unchanged
tail, min(t_e,K'_e)=t_e because K'_e>=K_e>=t_e. This is the precise safe case.

## Independent retention does not repair A2(v)

Parent proposed retaining t_e independently with probability exp(-t_e), using
s_e otherwise. This intermediate metric lies between s and t and still
preserves every original bigeodesic; its moments are finite because
E[t_e^k exp(-t_e)] is bounded for each k. Nevertheless it can fail A2(v).
Take M=1 and an absolutely continuous unbounded law with mass0.995 uniform on
(0.1,0.2), and remaining mass0.005 distributed with positive masses over
(100+n,100+n+0.1), n=0,1,... . In particular (20,21) is disjoint from its support.
Let f={(0,0),(1,0)}. The unique length10 simple circuit strictly enclosing both
endpoints is the 3-by-2 rectangle with corners(-1,-1),(2,-1),(2,1),(-1,1).
For justification, any such circuit has horizontal span>=3 and vertical span>=2,
so length>=10. Equality forces its upper and lower connections between the
left and right sides to be shortest paths. Any indentation would pass through
one of the two enclosed vertices; thus the enclosing circuit is that rectangle.
Choose an edge e on its upper side. The event that the retained/capped output
at f lies in(20,21) has positive probability. It cannot be a retained original
or uncapped original, since G has no mass there. The disjoint bands
(2L,2L+1) force L_f=10, hence every rectangle edge, including e, was M-open.
Therefore the output at e is <=1 on this outside-observable event. Its marginal
probability of exceeding1 is positive, by retaining a high original at e.
Conditional upward positivity fails exactly. This is not restricted to singular
continuous input laws. No conditional finite-energy restoration is claimed.

## Actual modification use-sites and next obligation

AH1609.02447v2 Section9 introduction and Proposition9.5 were read; the latter
requires tail/label stability under a finite-change coupling, not merely a
metric distance bound. In Section9.4's unbounded-support case (extracted
lines2430–2510), three noncoalescing rays lie in the right half-plane. Boundary
edges of a thin rectangle have weights <=t; its interior rungs are raised above
2mt while those rays and the cheap boundary remain unchanged. This produces
a forbidden least coalescence-class element. The whole use is stronger than
having an arbitrarily large central cap somewhere in a resampled box.

Source212 sections07-tilts.tex1–135 were read: selected paths come from individual
output iid environments, and a shared product coupling preserves exact conditional
hidden-raise identities and finite-region unions. The original iid construction
retains those law identities. Transferring the selected paths' labels and the
comparison rays to the capped metric remains an obligation.

The full next task is a block-modification substitute at these actual use-sites,
with unchanged selected ray tails, controlled label order, and protected cheap
boundary connections. Raising a larger undifferentiated box is not a proof:
it may alter the initial cap-ray portions or erase the low boundary connections.
No blanket application of AH's A2 theorem is justified.

## Uniform uncapping for point-to-half-plane approximants

Let H={z in Z²: ell(z)>=a} be any lattice half-plane, with ell a nonzero
linear functional, and let p be a minimizing s-path from v to H. Every
changed edge of p lies in E_v, uniformly in ell and a. Indeed suppose p
uses a changed e and v is outside or on C_e. It has a first C_e contact
before e. If it subsequently exits C_e before reaching H, replace the
segment around e by a cheaper circuit arc. Otherwise its target in H is
strictly inside C_e (the boundary case permits the same replacement). A
linear functional attains its maximum over the enclosed polygon at a
boundary vertex, so C_e has a vertex in H. Replace the path after the first
C_e contact by a circuit arc to such a vertex. This is an admissible path
to H of added cost <=ML_e, while the removed suffix contains cost K_e>=2ML_e.
Either case contradicts minimality. Therefore only E_v can contain changed
edges. The same proof for an original t-minimizer excludes original edges
with t_e>K_e outside E_v, using t_e>K_e in the comparison.

This statement applies to every finite DH point-to-half-plane approximant,
not merely a limiting ray. It does not assert all these paths are unchanged
under an arbitrary finite modification: one must choose cut roots beyond
their potentially capped initial portions, and protect the remaining paths.
It may supply the uniform uncapping needed in a finite-approximation wall
argument, but the weak-limit pushforward and its uniform positive-probability
estimates remain to be proved.

## Bigeodesics coincide exactly, with uncapped edge costs

The original-to-cap preservation proof in mechanism.md has a converse.
Every s-bigeodesic uses only edges with s_e=t_e. If it used a changed edge e,
both infinite arms leave the finite protecting circuit C_e. Its segment
between boundary contacts bracketing e would cost at least K_e>=2ML_e,
whereas a boundary arc costs <=ML_e, contradicting its s-minimality.
Thus the entire bigeodesic is unchanged edgewise. Since s<=t, every one of
its segments then also minimizes for t. Combined with the earlier replacement
proof, the sets of geometric original and cap bigeodesics are exactly equal,
simultaneously, with identical costs on every such path. This does not extend
to arbitrary rooted rays or finite minimizers, and does not identify their
Busemann functions in the two metrics.
