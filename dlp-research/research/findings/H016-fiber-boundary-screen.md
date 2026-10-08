# H016 two fibre partitions: exact recovery bridge, few-anchor coverage limit

2026-10-08. Native Astra /root/h006_structured_relation_ideas proposer; separate
Astra /root/h007_additive_relations geometry/coverage reviewer. Root checks
signs, incidence accounting and secret-independence conditions. Paper result,
no experiment, Lean proof or improved complete solver.

## Explicit finite operation

On E/Fp with p>3 and ordinary prime-order group E(Fp)=<G>, q>3, target Q=kG!=O, choose fixed
public slopes lambda0,lambda1 and rational functions

    f0(P)=y(P)-lambda0*x(P),
    f1(P)=y(P-Q)-lambda1*x(P-Q).

Query the fibre through P by dividing its line-cubic intersection polynomial by
the known abscissa root and solving the residual quadratic. The polynomial is
X^3-lambda^2*X^2+(A-2*lambda*v)*X+B-v^2 for line value v. Admit only three
DISTINCT rational points at a finite function value. Colour0 has pole O;
colour1 has pole Q. Translating a colour1 fibre may produce O, which must be
handled explicitly as a known zero-log anchor, not as an affine coordinate.
Pay translations, interpolation,
division, residue/square-root work, reconstruction, verification and failures.
This is an actual constant-degree factor operation, not a free root oracle or
a claim of constant bit cost. Nonsplit, ramified or pole cases cannot be silently
discarded from an accepted closure; they make that attempted traversal fail.

Each admitted f0 fibre has point sum O by the chord group law. Each f1 fibre
is the translate by Q of an f0-type line fibre and has point sum3Q. Record
distinct fibres as rows of the corresponding colour, deduplicated by colour and
fibre value. A point lies in at most one fibre of each colour.

Choose a set of anchors with known NUMERICAL logs s_j, not just unknown affine
coefficients involving k. Traverse the bipartite incidence component through
unknown points; delete known-anchor columns. For every remaining unknown point,
accept only when BOTH its incident colour rows have been visited and admitted.
Summing colour0 rows minus colour1 rows cancels those unknown logs and gives

    sum_j epsilon_j*s_j = -3*n1*k modq,
    k = -sum_j epsilon_j*s_j / (3*n1) modq,

where n1 is the number of distinct colour1 rows, and only nonzero denominator
is accepted. Verify kG=Q. Repeated anchor encounters require correct multiplicity
in incidence bookkeeping; after row deduplication epsilon_j is in{-1,0,1}.

This retains the known-column possibility excluded by overly broad complete-
column cancellation arguments. No common-composite oracle is assumed. The
missing operation is finding a SMALL useful closed boundary cheaply.

## Exact frontier accounting

For a connected explored row graph, let R be its rows, E its unknown-point
edges with both endpoint rows visited (parallel edges allowed), H its known-anchor
incidences and F its
unknown-point incidences with only one visited endpoint. Every row has degree3:

    F=3R-2E-H=R+2-2c-H,  c=E-R+1.

A first query through one anchor has F=2. An ordinary new row closes one prior
frontier incidence and opens two, increasing F by one. Closure therefore needs
enough further anchor incidences or cycle surplus. An unexplored/nonadmissible
opposite fibre leaves a frontier obligation; it is not a cancelled variable.
These identities do not assume uniform residuals or prove a general lower bound
on adaptive coordinate exploration. Informal random-residual heuristics alone
provide no cheap useful closure. More generally, a new row sharing t frontier
points and h anchor incidences changes F by3-2t-h. An unknown singleton column
forces its row weight to zero in any cancelling linear combination, and internal
edges propagate zero through its connected component. Arbitrary row weights
therefore do not repair an open frontier in this incidence model.

An unanchored closed component is impossible: it would give3n1*Q=O, but its
disjoint colour1 triples imply0<n1<=floor(q/3)<q. For prime q>3 and Q!=O
that contradicts the group order. This does not eliminate anchored components.

## Exact fixed-few-anchor falsifier

Fix L deduplicated numerical anchors independently of secret k. For any success
with1<=n1<=N and invertible3n1, the recovered secret belongs to

    {-sum_j epsilon_j*s_j/(3n): epsilon_j in{-1,0,1}, 1<=n<=N}.

The set has at most3^L*N elements. Target-adaptive slopes or repeated slope-pair
attempts cannot enlarge it if the SAME fixed anchors and total row budget N
are used. No distributional assumption on the fibre graph is needed. With a
uniform nonzero secret, success probability is at most
min(1,3^L*N/(q-1)). For anchors{G} or{O,G}, the only possible nonzero recovered
secrets are +/-(3n)^(-1), at most2N in number. Fixed L and constant success
therefore require Omega(q/3^L) rows in THIS realization.

Do not extend the counting argument to secret-dependent anchor choices, growing
anchor pools, changed relation incidences, or new centres aG+bQ unless
their choices and coefficient sets are separately bounded. In particular a
logarithmically growing anchor set can make this bound uninformative. No
universal coordinate-aware lower bound is asserted.

## Costs and disposition

Anchor generation/log storage, all fibre trials, failed components, deduplication,
frontier/edge tables, translations, extraction and final verification are paid.
The original few-anchor breadth-first realization fails its full-range gain
justification by exact coverage counting. A growing dictionary needs a concrete
cheaper useful-boundary selector and complete cost estimate, not just a larger
rank system. With mean complete attempt cost C and independent-attempt success
probability sigma, setup+C/sigma+verification must beat the matched solver;
memory is O(L+J) records for J retained queries. No favorable pair C,sigma is
supplied. Keep the executable relation bridge and this limited negative
finding; no numerical engine or general formal machinery is justified yet.
