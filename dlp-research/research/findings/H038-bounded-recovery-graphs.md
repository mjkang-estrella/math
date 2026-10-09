# H038 bounded recovery graphs for two-point decompositions

Status: PAPER negative screen, proposed by root and independently reviewed by
native Astra /root/h007_additive_relations. No executable improvement, experiment,
Lean claim or universal ECDLP lower bound. This tests the small-cycle escape from
the full-rank assembly gate in H038-farey-geometry.md.

## Fixed-base, fresh-target model

Work in an odd prime-order group with generator G, order q, public Q=kG. Fix an
explicit set F of B distinct group points. Abstractly identify their logs with
S subset F_q for counting only; the algorithm receives no secret-log table.
Each query ID j has one fixed known label pair (a_j,b_j) and target
R_j=a_j*G+b_j*Q. Conditional on the past and F, each new R_j must be fresh
uniform. There is a deterministic cap n on queries; pad any stopped sequence
with unused fresh draws. The extractor can report any or all edges P+P'=R_j.
Count full matching graphs to upper-bound any such extractor.

Colors mean QUERY IDs, not numerical target values. Distinct queries that happen
to produce the same point retain distinct colors and labels. Repeated reports
of an identical witness are not new witnesses. Fixed F can be conditioned on,
but adaptive changes to F are outside this argument.

## Independently accepted bounded even-cycle calculation

Fix even length ell<=L, with L constant independent of q, and q>L. Use ell
formal vertex positions x_i, even if the actual graph identifies some positions.
The edge-sum matrix M has rows x_i+x_(i+1). It has rank ell-1 and left kernel
spanned by the alternating vector a. Partition edges into d nonempty query-ID
classes. Equalities between sums within each class have rowspace

    W = {w : sum of w_i within each color class is zero}, dim W=ell-d.

If the alternating multiplicities of query colors are nonzero modulo q, then
a is not in W. Thus the composed vertex constraints have rank ell-d. Choose d
free vertex coordinates from S: every other coordinate is uniquely determined,
so at most B^d assignments exist. Imposing actual vertex identifications can
only reduce this count; do not claim the collapsed graph has the same rank.

For each assignment and d distinct query IDs, fresh uniform targets match all
required edge sums with probability q^(-d). There are at most n^d choices of
IDs and only a constant (depending on L) number of lengths, partitions and
orientations. Hence

    E[number of potentially useful bounded even-cycle witnesses]
      <= C_L * sum_(1<=d<=L) (B*n/q)^d.

Nonzero alternating color counts are NECESSARY, not sufficient for recovery.
The resulting coefficient of k must be nonzero and the candidate scalar must
be verified. If every target is Q+a_j*G, all even-cycle coefficients of k cancel.
Loops, parallel edges and repeated numerical targets introduce no extra freedom
in the formal-position count. Length two covers distinct-query duplicate edges.

For success probability bounded below by a positive constant, this bound forces
B*n=Omega(q). Explicit materialization costing Omega(B), and at least one unit
per started query, then force capped-budget work B+n=Omega(sqrt(q)). This is a
budget/success-probability statement, not a claim that every early-stopped run
pays its entire cap or a universal expected-cost theorem.

## Review and scope

Astra accepted the rank/count argument and corrected root's original use of
distinct target colors to distinct QUERY IDs. It also required the explicit
necessary-versus-sufficient recovery qualification and formal-position handling
of loops/repeated vertices. Root incorporated these corrections above.

Long cycles, nonuniform queries, implicit or adaptive bases and separately paid
known-log advice are not excluded. The following independently accepted
extension does cover bounded combined odd-cycle dependencies. No broader formal
infrastructure or experiment is justified by this negative screen.

## Accepted extension to bounded dependency graphs

Root proposed the extension; a separate native Astra follow-up accepted it.
Fix a connected multigraph with v vertices and e<=L edges. M maps vertex logs
to edge sums; a loop has coefficient2 at its vertex. In odd characteristic,
rank M=r=v-1 for bipartite graphs, and r=v otherwise: the kernel equations
x_u=-x_v propagate along paths, and an odd cycle or loop forces x=0.
Let C be the e-by-d matrix that duplicates each query-ID target onto its edges.
Repetition constraints have coefficient rowspace W=ker C^T, dimension e-d.

A potentially useful dependency c must satisfy M^T*c=0 and C^T*c!=0. Otherwise
eliminating all vertex logs also eliminates all fixed query labels, yielding
only a null equation. This necessary condition implies ker M^T is not contained
in W, so

    dim(W intersect ker M^T) <= e-r-1,
    rank of the constraints W*M >= r-d+1.

Selecting free vertex coordinates from S therefore bounds assignments by
B^(v-r+d-1): B^d in the bipartite case and B^(d-1) otherwise. If the rank lower
bound is negative, it is vacuous but the stated assignment upper bound still
holds for B>=1. A purported d=1 useful pattern cannot exist: M*1=2*1 implies
sum c_e=0, hence C^T*c=0 with one query color.

Each assignment fixes the values of d distinct query IDs; the probability is
q^(-d). Sum over at most n^d choices of IDs and the finite set of graph/color
patterns with e<=L. The same C_L*sum_d(B*n/q)^d probability bound follows.
For disconnected graphs a useful dependency has a useful connected component:
restrict c to each component, then at least one component has nonzero color
coefficients. This includes bounded linked odd-cycle configurations. Usefulness
is tested directly modulo q, so this extension only needs odd q, not q>L.

Scope: recovery must eliminate ALL included unknown vertex logs. Independently
known numerical anchor logs add constraints absent from M and are not covered
automatically. Nonzero C^T*c still does not guarantee a nonzero challenge-scalar
coefficient. Long or growing-size dependencies are outside the fixed-L bound;
no constants uniform in L have been established. The explicit-base and fresh-
uniform-target assumptions remain essential. This is not a generic-group bound
or a coordinate-aware ECDLP impossibility result.

Exact process: algebraic paper derivation and read-only native review; no
numerical run, imports, source modification, new external source or runtime
measurement. Existing baseline and verified-improvement status remain unchanged.
