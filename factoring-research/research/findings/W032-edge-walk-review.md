# W032 weighted edge walk: symbolic correctness and cost review

**Disposition: ACCEPT the geometric compiler and the claimed conservative
primitive bounds, with the explicit implementation conventions below.
For the accepted large-base cover the complete bound is soft
O(R^4(n+R)); for the new affine floor formula it is soft O(R^6(n+R)),
where n=bitlength(N). The new affine identity remains CONDITIONAL and
outside this review. Verified complete factoring improvement: NONE.**

The proposed walk really can replace repeated slab sampling: it processes
O(J^2) edge incidences and gcd arguments, initializing the original floor
formula only once per walked line. No face-location, arrangement, lattice,
root-ordering, or useful-factor oracle is needed. The offset constant
1/(64 B^6) is sufficient. No symbolic counterexample to the completed
algorithm was found. This is a prose proof, not an implementation test,
Lean proof, numerical experiment, or claim of optimality.

The implementation must retain each crossing's line identity when equal
vertices are grouped; apply the signed sum of all its incidences before
sampling; and preserve boundary-coincident thresholds through the direct
initialization while walking the square edge only on its inside. These
complete the target's stated conventions without changing its formulas
or asymptotic bound. In particular, deduplicating points must not discard
the tied incidence lists, and a boundary record's zero geometric weight
must not erase a threshold's contribution to the original floor formula.

## 1. Frozen scope and dependency separation

The [full assignment](W032-edge-walk-review-evidence/full-brief.txt) and
18 complete inputs were frozen before substantive analysis. The
[input manifest](W032-edge-walk-review-evidence/input-manifest.sha256)
was hashed with terminal `sha256sum`; its external anchor is
`d68a193ab51128b7230e68f2460162b43e6e12711d10cab2d4df6748dc95b329`.
The full target is the
[frozen weighted-edge-walk note](W032-edge-walk-review-evidence/inputs/research/findings/W032-weighted-edge-walk.md).
[Read scope](W032-edge-walk-review-evidence/read-scope.md) records complete
reads, excerpts, metadata inspection, and frozen-but-unreviewed material.
The final byte comparison found concurrent changes only in README.md
and STATE.md. Their later bytes are preserved separately and were not
semantically read or adopted; all mathematical source snapshots matched.

The accepted arrangement review supplies the old cover with normals
(i,1). Its formerly live common-lift interface is accepted by the separate
lift-sweep review, whose former base-acquisition dependency is resolved by
the accepted carry-quotient review, as specified by this assignment.
These three review reports were read; their nested evidence packages and
external arithmetic references were not independently reaudited here.

For the new normals (i+1,i(i+1)), this report proves a compiler theorem
for the **given floor formula**. It does not certify the new Taylor law,
annihilation, top-digit comparison, or an actual affine-lift witness.
The separate live affine identity audit was not read or duplicated.
The original W032 hypothesis is context only.

The sole sweep assay is terminal: two finite families exhausted without
a proper gcd, and the third group stopped in setup with its candidate
unstarted. The frozen assay-audit report was read for that boundary; no
assay source, event ledger, or candidate was executed or recomputed.
This review neither changes those observations nor selects another run.
Independent yield and order mechanisms are outside this review.

## 2. Compiler contract and exact threshold representation

For the geometric theorem, assume only integers N>1, c0, lambda_i,
b_i, A_i, B_i, with 0<=b_i<N, A_i,B_i>=0 and s_i=A_i+B_i>0.
There are m+1 terms, indexed 0 through m. Put

```text
C(x,y) = c0 - sum_i lambda_i floor((b_i+A_i x+B_i y)/N),
J = sum_i s_i,
B = max(1, max_i A_i, max_i B_i),
S = [0,N]^2,              S_open = (0,N)^2.
```

The letter B here is a bound on normals, not the bit length of the
carry-acquisition modulus. For every point of S, each floor is between
0 and s_i, and exactly

```text
floor((b_i+A_i x+B_i y)/N)
  = sum_(k=1..s_i) 1_{A_i x+B_i y >= kN-b_i}.          (1)
```

Indeed the numerator is nonnegative and strictly below (s_i+1)N,
even on the closed square. Thus the advertised threshold range is
complete. A possible k=0 equality creates no jump from a negative
floor inside the domain. A zero normal is excluded by the contract.

All weights are signed integers; a positive threshold means k>0,
not lambda_i>0. Generate every record (A_i,B_i,kN-b_i,lambda_i).
No threshold's equality convention is inferred from a floating point
test. Equation (1) includes its positive side and equality; all final
geometric samples are strictly off the threshold lines.

## 3. Exact preprocessing, clipping, and orientation

The following implements all geometric preparation with finite lists.

1. Normalize a threshold triple (a,b,d) by dividing all three entries
   by gcd(a,b,d), taking the positive gcd. The normal is nonzero and
   nonnegative, and d=kN-b_i>0. This gives a unique primitive integer
   triple for each geometric line, with its original positive side.
   Sort triples lexicographically, merge equal triples, and sum their
   signed weights W. Positive rescaling never changes an indicator.
   Keep a line even if W=0, to retain the full floor arrangement's
   chamber coverage. This optional redundancy is already paid.
2. Treat x=0, x=N, y=0, y=N as four separate geometric boundary
   records with an inside direction. A coincident threshold is not
   a second traversal and is not a two-sided interior edge. Preserve
   the original floor terms for initialization; do not turn that
   threshold into an extra zero-weight term in formula (1).
3. Clip each remaining threshold by solving against the four boundary
   lines. For two normals (a,b),(a',b'), set D=ab'-ba'. If D!=0,
   construct the intersection by Cramer's rule, make its common
   denominator positive, and retain it only if both coordinates are
   in [0,N]. If D=0, do no division. Coincidence with a square edge
   was handled in step 2; distinct parallel lines have no crossing.
4. Deduplicate the retained boundary points exactly. A noncoincident
   line intersects the closed convex square in either nothing, one
   point, or a segment with two distinct endpoints. Discard empty
   and one-point clips. A corner tangent therefore has no edge.
   The midpoint of any remaining non-boundary segment is strictly
   inside S. Keep these as the active threshold lines. A boundary
   line itself has its two square corners as endpoints.

A threshold discarded in this process has a constant indicator on
S_open. Formula (1), evaluated directly at initialization, automatically
includes that constant. It then needs no event. In the present positive
threshold/nonnegative-normal domain, the excluded boundary-only
thresholds are on upper boundaries and are inactive on S_open; the
initialization argument also avoids depending on this specialization.

Let K be the number of active threshold lines, and T=K+4 the number of
walks. Thus K<=J and T<=J+4. For an active line g with normalized normal
n_g=(a_g,b_g), choose the **integer walk direction**

```text
d_g = (-b_g,a_g),       t_g(P) = d_g dot P.
```

Sort its endpoints and later vertices by increasing t_g. Along the
line, increasing t_g means moving in direction d_g, because
d_g dot d_g>0. This works for horizontal and vertical lines without
a special division. For square boundaries use their positive unit
normal to define a tangent the same way; store the inward unit normal
separately. On x=N or y=N the inward normal is the negative unit vector.

For each walk g, intersect it with every other active threshold and
the four boundary lines using the same nonzero-determinant rule. Keep
intersections on its closed clipped segment. Attach the other line's
identity to each intersection. Add both segment endpoints, sort by
t_g, and group exactly equal points **with the union of their incident
line records**. Every pair is considered at most once during this walk.
No zero-length edge is produced. Distinct parallel thresholds never
generate an event, but remain in the original initialization.

Boundary incidences have zero update weight. On an interior threshold
segment they are only at its endpoints. On a boundary walk the other
boundaries meet only at the corners. Thresholds through those endpoints
are represented by initialization after the first endpoint, not by
applying a fictitious before-the-square update.

Clipping costs O(J) constant-size intersection calculations, after
O(J log(J+1)) merging comparisons and O(J) normalization gcds. It does
not enumerate lattice points, line intercepts one unit at a time, or
an unbounded set of points on a coincident boundary.

## 4. Exact midpoint margin and the proposed offset constant

All primitive threshold and boundary normals have coordinates of
absolute value at most B. Each intercept has O(n+log(B+1)) bits:
before normalization 0<kN-b_i<=2BN. Every nonzero determinant satisfies

```text
1 <= |D| <= 2 B^2.
```

Represent a vertex as (X/q,Y/q) with **one common positive denominator**
q<=2B^2, obtained from that pair's determinant; square corners use q=1.
Coordinatewise reductions are unnecessary. After membership filtering,
0<=X,Y<=Nq. Deduplicating a vertex may retain any one such bounded
representation. It must not repeatedly add or average duplicates.

For consecutive distinct vertices with denominators q,r, construct
their midpoint directly from those two original records, using common
denominator

```text
D_mid = 2 q r <= 8 B^4 = Q_max.                      (2)
```

Do not form midpoints by accumulating prior offsets or unrelated
denominators. At an open edge midpoint P, every noncoincident relevant
integer line form ell(X,Y)=aX+bY-d is nonzero, hence

```text
|ell(P)| >= 1/D_mid >= 1/(8 B^4).                    (3)
```

Any other active line passing through that midpoint would have been a
vertex splitting the edge. Empty or tangent clips cannot meet it in
S_open; on a boundary, corner tangencies are endpoints. A coincident
boundary threshold is a self-line case, not a purported nonzero form.

Use the target's exact value

```text
delta = 1/(64 B^6).
```

For an interior walk take P_minus=P-delta*n_g and
P_plus=P+delta*n_g. For any noncoincident threshold or square boundary,

```text
|ell(P_plus/minus)-ell(P)|
   <= 2 B^2 delta = 1/(32 B^4) < 1/(16 B^4).        (4)
```

The perturbation is at most one quarter of the conservative lower
margin (3), in particular strictly less than half. All other signs
are preserved. For an interior edge all four boundary forms are
nonzero too, so both offsets stay strictly in S_open. The self-line
form becomes respectively -delta*||n_g||^2 and +delta*||n_g||^2,
with the desired strict signs.

For a boundary edge use only P_inside=P+delta*u, where u is its
inward unit normal. Its own boundary is crossed into the square.
The other three boundary forms and all noncoincident thresholds obey
the same estimate; any threshold coincident with the walk's boundary
has a fixed sign on the inside. Thus the sample is strictly inside
S and on no threshold. No external chamber is sampled.

An offset can use denominator
64 B^6 D_mid <= 512 B^10. Its coordinates, numerators, denominators,
floor numerators, floor denominators, determinant comparisons, and
cross-products all have O(n+log(B+1)) bits. Fixed-power growth changes
only constants in this bound. Exact rational reduction is optional;
if used, its gcd cost is paid. There is no real-arithmetic oracle or
numerical epsilon.

## 5. Initialization and the signed atomic update invariant

For the first open edge of an interior walk g, evaluate the **original
m+1 floors** exactly at P_minus and form C_minus. Then set

```text
C_plus = C_minus - W_g.                              (5)
```

All other threshold signs agree at the two offsets by section 4.
The merged self-line's indicator alone changes from 0 to 1, proving
(5), including negative or zero W_g. For a boundary walk, initialize
only C_inside by the original floors at P_inside. This accounts for
all constant, discarded, parallel, and self-boundary contributions.
An O(J) indicator rescan is unnecessary; one O(m+1) initialization
per walk suffices. No division by N modulo N occurs.

Suppose consecutive open edges meet at vertex V. Let I(V) be the
set of other active threshold lines crossing g there, with their
identities retained. For h in I(V), nonparallelism gives
n_h dot d_g != 0. Along the unperturbed walk, ell_h changes sign
at V from negative to positive if this dot product is positive,
and in the opposite direction if it is negative. Therefore

```text
Delta_V = sum_(h in I(V)) sign(n_h dot d_g) W_h,
C_minus <- C_minus - Delta_V,
C_plus  <- C_plus  - Delta_V                         (6)
```

or the identical update to C_inside on a boundary walk. It suffices
to maintain C_minus alone and recompute C_plus by (5) at each edge.

To prove (6) gives **the actual next offset's C**, compare the two
edge midpoints. A nonself line not incident to V has no zero between
them, since their edges are consecutive in the complete vertex list.
Its indicator is unchanged. A line in I(V) changes by exactly the
displayed sign. By (4), each midpoint's offset has the same indicators
as that midpoint for every nonself line. The self-line has its fixed
chosen sign on each side. Subtracting the corresponding weighted
indicator differences in (1) proves (6) for each side. Induction from
the direct initialization proves the invariant throughout the walk.

The geometric paths joining displaced midpoints need not cross the
tied lines at the same time. Only the endpoints' floor vectors are
used in this proof. Sum all tied contributions before any gcd test
or claimed sample output; a partial sum need not be an adjacent
chamber value. A zero-net tie is still a valid crossing group and
may leave C unchanged. Do not infer that its floor vectors agree.

The sign in (6) is essential. For a horizontal walk directed left,
a crossing vertical line's positive half-plane is exited, so its
weight must be added back. In general the dot
product handles that orientation automatically. Neither “always
subtract” nor a sign determined by the walk's normal is valid.

Process no event before the first open edge or after the last one.
Endpoint and corner incidences are already reflected in the first
floor initialization. This handles arbitrarily many lines through
a corner, endpoint intersections, interior multiway ties, parallel
families, vertical lines, horizontal lines, and coincident thresholds.

## 6. Coverage, including integer equalities and empty arrangements

Each component of S_open with all active threshold lines removed is
an intersection of finitely many open half-planes with S_open. It
is nonempty, convex, bounded, and two-dimensional. Its closure is
a convex polygon with nonempty interior. Such a polygon has a
positive-length edge on a threshold or square boundary. Finitely
many other line intersections split that edge into positive-length
subedges. At least one is among the traversed open edges. Its
midpoint offset into the polygon has all the chamber's strict signs
by section 4 and therefore belongs to that chamber.

Thus the walk visits every chamber, and (6) assigns its true value.
This does not assume a supplied face list or require identifying a
chamber reached from two different edges. Repeated visits are legal
and paid. If there are no active threshold lines, the four boundary
walks each have one edge and sample the sole interior chamber.
J counts generated threshold records, not surviving interior lines;
one must not silently drop these four walks when K=0. For a wholly
empty term list, the optional extension J=0 tests the constant c0
directly or retains the boundary walks.

For integer (x,y) in [0,N)^2, put s_max=max_i(A_i+B_i) and

```text
epsilon = 1/(2 s_max),       (x',y')=(x+epsilon,y+epsilon).
```

Both coordinates are strictly between 0 and N. Every old numerator
is an integer and increases by s_i*epsilon in (0,1/2]. It cannot
reach its next strictly larger multiple of N, which is at integer
distance at least one. At an equality it moves into the positive
side with the same floor. All perturbed numerators are nonintegers,
so the new point lies on no threshold. Every original floor is
unchanged simultaneously. This also covers lower edges, the origin,
integer intersection points, and every actual permitted lift point.

Consequently the sampled C values include all integer-square C
values. The accepted old identity then includes all its actual
one-parameter lift outputs. For the new affine family, that last
connection to an original scalar observation remains conditional
on its separate identity audit. The integer-square inclusion for
the stated formula is already proved here.

Every sampled C is an integer, including extra values from chambers
without a lift point. Test g=gcd(|C|,N) and accept only 1<g<N with
N mod g=0. C=0 gives g=N; nonzero multiples of N also fail. Unit
and full gcds remain ordinary unsuccessful samples. No batching or
unpriced localization is assumed. A complete failed traversal rules
out proper gcds in the covered family, conditional on the relevant
identity. A partial traversal, rejected base, or budget stop does not.
Extra successes are valid factors without an actual lift witness.
Chamber counts and repeated edge samples are not lift probabilities.

## 7. Actual operation count, bit work, and acquisition

Each of T<=J+4 walks forms O(T) pair intersections, retains O(T)
vertex/incidence records, and sorts them with O(T log(T+1)) exact
comparisons. Multiway vertices decrease the number of distinct
vertices, while their total incidences per walk remain O(T).
There are O(T) edges and O(T) signed updates per walk; each edge
tests at most two gcds. No all-lines scan is performed per edge.
Recomputing a pair while walking its other line multiplies work
by at most two. Preprocessing and clipping fit these bounds.

With F=m+1 original floors, the elementary arithmetic/comparison
count, counting each floor division or gcd as a priced primitive, is

```text
O(T^2 log(T+1) + F T + J log(J+1)).                  (7)
```

There are O(T^2) gcd calls for samples, plus normalization and any
optional rational reductions. For the two nonempty W032 families,
J>=F and m>=5; (7) is O(J^2 log(J+1)+mJ), as advertised. Writing
J+1 and m+1 instead gives a version also valid for an empty list.

Let Lambda bound the bit length of every signed lambda_i and define
a conservative weight/index width

```text
H_bits = O(1 + bitlength(|c0|) + Lambda + log(J+1)),
U_bits = O(n + log(B+1)).
```

Indeed, if S_weights=sum_i (A_i+B_i)|lambda_i|, then
S_weights<=J*2^Lambda. Formula (1) bounds |C| by |c0|+S_weights.
Merged weights, partial tied sums, intermediate direct weighted
sums, and intermediate updates are bounded by a constant multiple
of |c0|+S_weights. A walk crosses each other geometric line at
most once, so cancellation does not hide unbounded accumulated
integers. Indices require O(log(J+1)) bits and are included.

For signed binomial weights with m=2R+1 and the accepted base
|c0|<4^R, Lambda=O(R), hence H_bits=O(R+log(J+1)). This conservative
bound is enough; the affine compiler does not need a new proof of
the stronger actual-lift magnitude bound. Each floor's rational
division uses O(U_bits)-bit operands. A sample gcd must process
both its H_bits-bit signed argument and the n-bit modulus, even
when C=0 or tiny. Rational sorting uses cross-products at O(U_bits)
width, rather than constant-time comparison of arbitrary rationals.

Under the accepted soft-linear multiplication, division, and gcd
model, including record traffic and weight operations, (7) gives

```text
soft O((T^2+F T)*(U_bits+H_bits) + C_base).           (8)
```

For both W032 families, F=O(R), log(J+1)=O(log(R+1)),
and C_base=soft O(R^2 n) is the accepted shared acquisition/check
envelope for one legal stencil. Thus (8) specializes to the target's

```text
soft O((J^2+mJ)*(n+R+log(B+1)) + R^2 n).
```

This includes reading canonical N,R and any supplied old start a0;
the full denominator prefilter through 2R+1; every base-point unit
check; paid ordinary-factor exits and product-gcd localization if
that alternative is used; modulus/coefficient construction; shared
monic evaluation; exact signed c0 division and canonical b_i
extraction; binomial-weight generation; and factor validation.
Do not certify eligibility merely from the shortened recurrence's
denominators. Never round a nonintegral purported c0 or splice
nonunit points out of a stencil. Arbitrarily wide supplied inputs
pay their real reading cost, and multiple starts/depths pay each
acquisition and traversal. Acquisition is imported, not re-proved.

For the old normals (i,1), B=O(R) and J=Theta(R^2), yielding
soft O(R^4(n+R)). For the given affine normals
(i+1,i(i+1)), B=O(R^2) and J=Theta(R^3), yielding
soft O(R^6(n+R)). These replace the respective literal slab
upper envelopes R^7(n+R) and R^10(n+R), up to soft factors.
The saved work is removal of repeated slab visits and per-sample
floor recomputation. This compares specified mathematical upper
bounds; it proves neither an optimal lower bound nor a measured
implementation speedup. The accepted small-base a0=1 one-dimensional
sweep still has its cheaper soft O(R^2(n+R)) bound for that narrower
family; an edge cover is not a universal replacement advantage.

## 8. Streaming space and output size

Retain the normalized line table, base floor parameters and weights,
one walk's O(T) intersections with line identities, its sorted/grouped
vertices, and a constant number of samples and carry accumulators.
The total incidence list remains O(T), even at a many-line vertex.
Use shared references to the line weights or explicitly pay for
copied H_bits-bit weights. Sorting scratch of one list suffices;
there is no global O(J^2) intersection table or face adjacency graph.

Including the accepted base-acquisition workspace and suitable fast
arithmetic scratch, a conservative streaming space envelope is

```text
soft O(J*(n+log(B+1)+R) + R^2 n) bits               (9)
```

for the two families. The +4 boundary records and O(R) input terms
are absorbed because J>=m+1. Use J+1 for an empty-list extension.
All samples can be regenerated from the two adjacent vertices;
carrying full floor vectors is unnecessary.

Compact records for every visited side, consisting of rational sample
coordinates, C, gcd, and line/edge references, have total worst-case
size O(J^2*(n+R+log(B+1))) in these families. Writing them is paid
even when streamed; retaining them all adds that storage to (9).
Recording every full m+1 floor vector, every lifted stencil, or all
wide scalar evaluations is a different output task with additional
construction and storage costs. No seen-set of all chamber values
is assumed; any such cache would also have to be paid.

## 9. Disposition and remaining obligation

Accept the completed exact algorithm, rational margin, atomic weighted
updates, full chamber coverage, integer-boundary representative, and
complete supplied-formula time/space envelopes. The geometric and cost
claims do not depend on the new affine identity being accepted. Only
its interpretation as original affine-lift outputs does. No amendment
to that separate identity derivation is supplied or implied here.

The next proof that could change the factoring conclusion is still a
proper-split cover or useful-mass theorem for an explicit, fully paid
N-only schedule, with all failed acquisitions, depths, starts, and
repetitions included. The walk resolves an enumeration cost; it does
not resolve factor supply. No new experiment, rerun, seed, depth, or
case is proposed. Verified complete factoring improvement remains NONE.

Only this report and its assigned evidence directory were written.
There was no delegation, candidate execution, installation, commit,
shared solver/Lean/STATE/registry change, or project-check invocation.
Administrative Python only copied files and recorded file provenance;
terminal SHA-256 checks seal byte identity, not mathematical correctness.
The user's subsequent explicit termination boundary is preserved in
[the evidence](W032-edge-walk-review-evidence/termination-boundary.txt).
This delivery closes only the assigned review; it initiates no further
research, task, restart, experiment, or review round.
The [delivery manifest](W032-edge-walk-review-evidence/delivery-manifest.sha256)
covers this report and all evidence payloads except its own inventory
files, with an external terminal hash supplied at handoff.
