# Cubic caps and the outer-circuit wall

Live author work; conditional supporting lemma, not a nomination or a completed
moment-free theorem. Original full target in mechanism.md is unchanged.

## Cap variant and deterministic barrier

Fix M with q=P(t_e>M)<1/3. Replace the earlier linear cap by
K_e=M(L_e^3+U_e), 0<U_e<1, and s_e=min(t_e,K_e).
Here L_e is the minimum length of an M-open simple circuit strictly enclosing
both endpoints of e. Since L_e>=10, K_e>=2ML_e. All deterministic bigeodesic,
ray-tail, and endpoint-correction proofs previously given therefore apply
verbatim. The stretched-exponential tail of L_e gives every moment of K_e
and s_e. The retention counterexample in tail-and-modification.md describes
the earlier linear variant; no retention repair is used here.

For integer m>=2 let F_m consist of horizontal edges from (-1,j) to (0,j),
1<=j<=m-1. Raise only the original weights in F_m above H_m=4Mm^3,
keeping all auxiliaries fixed. All these rungs become M-closed. Every open
circuit strictly enclosing a rung must cross the vertical line x=-1/2 below
and above that rung. All crossings at heights 1,...,m-1 are now closed;
therefore its vertical span is at least m, and its length is at least 2m.
Consequently K'_e>=8Mm^3 and s'_e>H_m for every rung e in F_m.

Raising originals can only remove open circuits. Thus L'_f>=L_f and
s'_f>=s_f for every edge f. An originally uncapped s-ray avoiding F_m remains
pointwise unchanged: s_f=t_f and min(t_f,K'_f)=t_f on that ray. It is an
s'-geodesic by monotonicity. This statement concerns the geometric ray, and
does NOT yet say that a given selector chooses it in the modified field.

Suppose C is an M-open simple circuit, disjoint from F_m and strictly
surrounding all its endpoints, with |C|<=C0 m^2. Every edge of C remains
unchanged and has cost <=M. For m>C0/4, its total cost is less than H_m.
A finite s'-geodesic between vertices outside or on C cannot use any rung:
the segment between its first and last C contacts surrounding that rung
costs >H_m, whereas an arc of C costs <H_m. This is a strict contradiction.
This replacement uses unchanged edges and entails no recursive cap argument.

The event that such a circuit exists, for an absolute sufficiently large C0,
has probability tending to one as m tends to infinity. Indeed use the annulus
between two square boxes of radii proportional to m about the wall midpoint.
Failure of an open surrounding circuit implies a closed dual annulus crossing
of length >=c m. Its possible starting sites number O(m), and the union bound
for self-avoiding dual paths gives O(m) sum_{n>=cm}(3q)^n. A simple circuit
inside the outer box uses at most its O(m^2) vertices. This is the same cheap
open-circuit ingredient used in ADH Appendix C; only its use with the cubic
cap wall here is new author work, with no literature verdict.

## Conditional least-element lemma

Assume a translation-covariant measurable selector G assigns to every vertex
an s-ray, is suffix-consistent (v on G(u) implies G(v) is its suffix), and
rays from different coalescence classes are disjoint. Assume all selected rays
eventually lie in every right translated half-plane. Suppose with positive
probability there are three different classes with selected rays rooted at
(0,j1),(0,j2),(0,j3), 0<j1<j2<j3, all uncapped and strictly in x>0 after
their roots. Finally assume the following modification property, NOT proved:
under the finite original upward resampling above, these three rays remain
the selected rays in the modified configuration.

For all sufficiently large m>j3, intersect this fixed positive-probability
triple event with the cheap-circuit event. The intersection still has positive
probability since the circuit failure probability tends to zero. Choose a
finite deterministic a>=H_m so the intersection with max_{F_m}t_e<=a
still has positive probability. For unbounded G, replace the rung weights
by independent samples from G conditioned on t>a. This is an upward original
iid finite modification, absolutely continuous with respect to the original
product law; the auxiliaries remain fixed. The three geometric rays remain
unchanged by the preceding monotonicity argument. By the assumed selector
property they remain three distinct selected classes.

The outer two rays joined by the vertical segment from (0,j1) to (0,j3)
form a proper simple planar curve. Its right-hand corridor contains the
middle ray. A vertex outside C and outside this corridor cannot belong to
the middle class. Its selected ray, if it coalesces with the middle ray,
reaches a sufficiently late middle vertex outside C. Before doing so it must
cross an outer ray or enter the corridor through the joining segment. An
outer-ray intersection contradicts distinct classes and suffix consistency.
Entry through the segment from the left uses a rung in F_m (entry at an
endpoint intersects an outer ray). The segment of this selected ray from
its root to the late middle vertex would then violate the circuit barrier.
Thus the middle class is contained in the corridor union the finite interior
and boundary of C.

The corridor is bounded below in the x coordinate. In each fixed vertical
column it contains only finitely many lattice vertices: each outer ray has
only finitely many vertices in the corresponding left half-plane, and its
remaining tail lies strictly to the right; above and below their finitely
many crossings that column is outside the corridor. Adding the finite set
bounded by C retains both properties. The middle class consequently has a
least vertex in lexicographic order (x first, then y).

This contradicts AH Lemma 9.11, whose mass-transport proof uses stationarity
and suffix consistency: every vertex sends at most one unit to its class's
least vertex, which would receive infinitely many units from its own ray.
Absolute continuity of the modified original field transfers this almost-sure
no-least-element property to the modified cap field. Hence the assumptions
above, including the unpaid selector-stability property, imply coalescence.

## Extracting unchanged triples: exact prerequisite

Given three distinct selected classes whose rays move right and are eventually
uncapped, choose a sufficiently far common integer vertical line beyond all
their finitely many capped edges. Cut each ray at its LAST contact with this
line. Suffix consistency makes each cut tail selected; all its later vertices
have strictly larger first coordinate. The three cut heights are distinct.
Order them, translate the common line to zero and the lowest height to a
positive height. Countably many integer choices imply that some deterministic
triple event has positive probability whenever existence of such a triple
has positive probability. Translation covariance supplies the stated form.
No full coalescence is used. Existence of at least three distinct classes
still requires the usual stationary noncrossing-family argument (AH's proof
uses ergodicity to pass from two to infinitely many); it is a separate
structural premise, not supplied by the deterministic cap construction.

## Precise remaining interface after actual AH proof-body reading

AH extracted lines2120–2395 and2380–2510 were read in full for this step.
Proposition9.5 is more than finite metric influence. Lemma9.6 first proves
that an already coalescing reference family is measurable from its eventual
half-plane, using a conditional two-environment coupling. Lemma9.7 uses
uniform shape and Busemann estimates to obtain whole unaffected cones.
Lemma9.8 then preserves labels by local prediction stubs and planar order;
Lemma9.9 supplies limits to the extremal selected ray. Only after those steps
does monotonicity prove that the chosen ray itself is unchanged (9.5(b)).

Our induced cap coupling has finitely many changed edges and both marginals
absolutely continuous to the cap law, but it is not AH's conditional iid
resampling coupling on a deterministic cap-edge set. The half-plane
measurability/reference-family argument, cap-label construction, uniform
cap shape inputs, and all other uses of AH assumptions remain to be justified.
In particular geometric ray preservation cannot replace Proposition9.5(b)
without these steps. The wall lemma removes the specific cheap-boundary and
large-rung obstruction; it does not prove the full moment-free target.

## Diagonal wall geometry (same conditional structural scope)

The barrier geometry extends to the diagonal right half-plane h=x+y>=0.
Let u=x-y and v_k=(k,-k). For |k|<=m raise both incoming edges from v_k
to h=-1 above H=Mm³. These edges cross the Euclidean line h=-1/2 at
u=2k-1/2 and u=2k+1/2. They exhaust its lattice-edge crossings between
u=-2m-1/2 and u=2m+1/2. Any open simple circuit strictly surrounding one
raised edge must intersect this line on both sides of its midpoint. None
of the intervening crossings is open, so its two extreme crossings lie
beyond the two ends of that entire blocked interval. Its u-span exceeds4m;
since each lattice step changes u by one, its length is at least4m (in fact
a perimeter bound gives more). The cubic cap therefore exceeds64Mm³,
and the raised s-weight exceeds H. An M-open circuit around the O(m)-sized
wall has O(m²) edges with probability tending to one and total cost <H
for all sufficiently large m. The identical circuit shortcut applies.

Rays cut at their last contacts with h=0 thereafter lie in h>=1 and avoid
all incoming wall edges. Join the two outer roots by the straight Euclidean
segment on h=0, which need not consist of lattice edges. A lattice path
entering the right corridor through the interior of this joining segment
from h<0 passes through some v_k and uses an edge from h=-1 to h=0.
All such edges in the root interval are among the raised edges. Entry at
an outer root intersects its ray. Parity causes no gap: h=0 lattice vertices
have u=2k, and the two incoming midpoint values are exactly 2k-1/2 and
2k+1/2; the blocked crossing values are consecutive half-integers from
-2m-1/2 to2m+1/2. The order h first, then u is a translation-invariant
discrete lexicographic order on Z². Eventual movement into every h-half-plane
gives finite intersections with each h-level, and the same least-element
argument follows. Reflections and right-angle rotations cover the eight
normal directions used by AH/DH. This geometric extension does not solve
the limiting-graph measure/selector-stability interface.
