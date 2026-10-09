# H037 limited-independence Newton source factory

Status: PAPER mathematical and cost reviews COMPLETED. No executable
improvement. The construction's leading collision limit survives, but its
arithmetic advantage over competent independent-source preparation is unsupported.
Develops the unscreened correlated-source card from independent GPT6Sol H036.
No code, numerical experiment, H034 rerun or implementation admission.

In the SCALAR field F_q choose r independent uniform coefficient pairs(A_j,B_j)
and compute R_j=A_jG+B_jQ. Define

    P_i=sum_{j<r} binom(i,j)*R_j, 0<=i<n<q, r<q.

The coefficient labels use the same Newton evaluation. Distinct evaluation
rows have the Vandermonde rank property because factorials j! are invertible;
any at most r source labels are independent uniform pairs. Maintain forward
differences D_j initialized to R_j, and advance simultaneously
D_j'=OLD D_j+OLD D_{j+1} for j<r-1. The next D0 is the next source point.
All point additions, scalar-label updates and old-state storage are paid.

Potential gain is replacing n independent scalar-multiplication preparations
with r initial preparations and n*(r-1) additions. This concerns a subleading
setup term, not the ECDLP exponent or the leading paired-key kernel. Compare
with competent fixed-base/window/MSM preparation, not only naive independent
double-and-add. Full-size materiality may be negligible even if this works.

The missing mathematical step is crucial: r-wise independence is not full
independence. For fixed s, intersections of s four-source collision equations
match the IID experiment once r>=4s. A slowly growing r might preserve the
capped Poisson collision law through factorial moments or inclusion-exclusion.
But IID total-variation convergence alone does not establish moment convergence;
rare large clusters could invalidate that inference. No such transfer is yet
accepted. The graph/schedule must be fixed independently of source values.

Global null-recovery conditioning also requires care. Newton coefficient arrays
A+kB remain independent of B, but a selected source relation might lift to the
zero vector on Newton coefficients, creating a structural useless collision.
Its absence or contribution needs proof. Algebraic source-label tracking is
not a free discrete-log oracle; every R_j and subsequent point is computed.

Native Astra /root/h007_additive_relations reviews rank, collision-law transfer
and null recovery. Native Sol /root/h034_c4_implementation independently prices
the concrete construction against competent IID preparation, with all setup,
exceptions, labels and memory. Both read-only, no runs/imports/edits/children.
Cheapest falsifier is the missing limited-independence law or a cost comparison
that removes the setup gain. No broader machine/decoder infrastructure needed.

Current reference remains square-root work. Verified executable improvement NONE.

## Completed mathematical review

Native Astra independently confirmed the Newton/Vandermonde rank and forward
difference recurrence. Ascending in-place updates preserve the OLD right-hand
values; descending updates do not. All labels and point operations remain paid.

The missing moment step can be proved for the admitted H034 collision forms.
Let X count distinct four-support signed zero forms at t=x*sqrt(q), with
N=O(q) forms. For a fixed s-tuple of forms with rank d, choose d basis forms.
All remaining forms lie in the union of their at most4d support coordinates.
Each has coefficients in{0,±1}, so at most3^(4d) choices exist on that union.
The number of such tuples is at most C_s*N^d. Under IID sources each tuple
vanishes with probabilityq^-d, hence E[X^s]=O_s(1). Higher fixed moments give
uniform integrability, so the existing IID Poisson limit also yields factorial
moment convergence. This does not infer moment convergence from total variation
alone; the additional bounded-support argument supplies the missing step.

Any s four-support events use at most4s sources. Once r>=4s, Newton and IID
sources give exactly the same intersection probability and factorial moment.
For r(q)->infinity, finite Bonferroni bounds and then increasing truncation order
give Pr(X=0)->exp(-x²) under the existing fixed graph/prefix hypotheses. Lower
support events and seed exceptions retain their negligible union bounds because
each uses a bounded number of sources. Thus for fixed cap A*sqrt(q),

    E[min(T,A*sqrt(q))]/sqrt(q) -> integral_0^A exp(-x²)dx,
    E[min(T,A*sqrt(q))²]/q -> 1-exp(-A²).

This is a leading limit, not the former quantitative O(q^(3/10)) remainder.
With r=ceil(loglogq), a slowly vanishing distribution error could overwhelm any
saved setup work. The proof does not automatically extend to coefficient-colored
forms whose alphabet grows with q.

For recovery, C_j=A_j+kB_j is jointly uniform and independent of the entire B
vector. Geometry selects a relation v using only C. A nonzero relation on at
most4 sources lifts to L_j=sum_i v_i*binom(i,j), which is nonzero forr>=4 by
Vandermonde independence. Conditional on all geometry, sum_j L_j B_j remains
uniform, giving null probability1/q. This does not forbid dependencies on more
than r sources; difference-register/helper points are not extra detectors.

## Preliminary competent cost correction

Root and Sol independently identified a stronger IID-source comparator: paid
fixed-position tables for the two bases G,Q can use window widths proportional
to log(N), where N=Theta(q^(3/10)) is the number of desired roots. With a fixed
number of window positions and total table size O(N/polylog(q)), each IID
source then needs O(1) group additions, not O(logq) independent double-and-add.
Projective accumulation and one final batch normalization avoid an affine
inverse per source. Setup, table reads, random scalar generation and storage
must still be charged. This is an allowed comparator, not hidden advice.

The Newton route uses O(Nr) point/label updates, so r->infinity does not show an
asymptotic arithmetic gain in that allowed-memory regime. It does reduce ideal
randomness consumption, which is a distinct price/semantics question. No concrete
finite machine gain follows. The final separate cost report will fix the exact
table construction and scope; no implementation or experiment is admitted.

## Final cost screen and disposition

Sol completed the independent cost review. Affine forward differences batch
the r-1 additions within EACH source advance, so they still pay one inverse
per advance. Regular cost is(5(r-1)-3)M+(r-1)S+6(r-1)A+I, plus labels and
traffic; with I=O(logq) this is O(N(r+logq)). Complete projective branches and
paid final normalization reduce point-field work to O(Nr+logq), not O(N).
There are2(N-1)(r-1) scalar-label additions. Intermediate states can be infinity
or have equal abscissae; emitted-source seed checks do not remove those cases.

For competent IID generation take separate fixed-position base tables with
2^w=Theta(N/(logq)²). Because N=Theta(q^(3/10)), w=Theta(logq), so both scalars
have O(1) chunks. Every source costs O(1) table accesses/projective additions;
table construction and extra storage cost O(N/(logq)²). Batch normalization
and source storage remain paid. Root notes that both constructions can normalize
chunks of(logq)² outputs before storing affine sources; this avoids assuming
an entire additional projective source array is free. Chunk inverses contribute
O(N/logq) under the stated inverse expansion. Exact finite peak still needs a
separate implementation-specific check.

Under the declared fixed-price projective/indexed-access model, IID preparation
therefore has O(N) group-field work, versus Newton O(Nr) for growing r. This
defeats the proposed asymptotic arithmetic-saving premise in the allowed O(N)
memory regime. It is not a measured machine comparison or an exclusion under
every tighter precomputation-memory constraint.

Ideal coefficient entropy falls from2N*log2(q) to2r*log2(q). Random-bit costs,
scalar-word sampling and arithmetic are distinct charges. A fixed short PRNG
seed does not instantiate this ideal distribution or the growing-r proof.

The unavoidable r-th finite difference uses r+1 sources and vanishes in both
label coordinates, so searching it supplies no recovery information. For fixed
r=4, a concrete alias of distinct functionals is

    P0+P4+P7+P11 = P1+P2+P9+P10.

The index multisets have equal power sums through degree3. This illustrates
finite-r dependence, not a guaranteed useless leaf or failure in the actual
bipartite graph. The growing-r limit does not justify a finite-size rate.

Both factories remain subleading q^(3/10)*polylog(q) to the sqrt(q) search; the
relative scale is q^(-1/5)*polylog(q). No complete-work percentage follows.
Park this as a valid randomness-saving construction, without an arithmetic-gain
claim. No further test is warranted without a named tighter memory/randomness
cost regime that could change full work. No Lean infrastructure or solver run.
