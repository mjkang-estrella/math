# Discovery investigation: Chauhan–Dubey Conjecture 3.12

Status: unresolved; no outcome nominated, credit 0. This is a research handback,
not an acceptance decision. Counts remain 3/30 additional and 33/60 total.

## Selection and source fidelity

Read ancestor and campaign AGENTS.md, ledger.json, NEXT.md and
prior-campaign-context.json, and the matrix/algebra histories in
pi-matrix-discovery-r3, astra-algebra-matrix-r2, the preceding
pi-matrix-discovery-r6 and twenty-proof-matrix-lane before selecting.
All expressly excluded families were left alone. The selected record, 373375,
was only an undeveloped lead in the older matrix lane. No result is inferred
from its cached open label.

Primary source: Bharat Pratap Chauhan and Dipti Dubey, *On semimonotone
matrices of exact order two*, https://arxiv.org/html/2603.00639v1 . Actual
Definitions 3.1 and 3.7, Theorems 2.1–2.3, 3.3, 3.9, Conjectures 3.11–3.12,
Remark 4.1 and Theorem 4.8 were read in the body. The abstract history lists
only v1, submitted 2026-02-28 13:14:26 UTC. The journal article was published
online 2026-02-27, LMA 74(5), 671–685, DOI
https://doi.org/10.1080/03081087.2026.2636706 . Its body returned 403 and was
not retried. That comparison remains a SOURCE GAP.

For a real square matrix B, E0 means: for every nonzero x>=0, some i with
x_i>0 has (Bx)_i>=0. For n>=3, A is E0 of exact order two when every principal
(n-2)-block is E0 and every principal (n-1)-block and A itself are not E0.
Conjecture 3.12 asks, for every such A in every dimension, det A<0 and
A^{-1} has nonpositive off-diagonal entries. This is the full objective here.
The Z-restricted hypotheses of 3.11 are NOT substituted for this question.

## Early screening and chronology

Used the fresh complete registry caches and current-head receipts supplied by
sol-fresh-analysis-discovery-r7 (retrieved 2026-10-29 04:39–04:43 UTC), rather
than a rate-limited GitHub API traversal. Omega head
67b4fae085cf19003a33f8027410c383b49e5046; OpenAI math head
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; count-ex-machina head
dbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Complete Problems and D5 path
lists and the other cached registries were screened for source names, number,
identifier and terminology. No relevant match; the OpenAI path matches for
"exact-orders" concern anticanonical linear systems and are unrelated.
See registry-screen.json for complete cache hashes. This is path-level bounded
coverage, not a global content search or a novelty clearance. No GitHub API
requests were made in this lane.

Public searches on 2026-10-29 UTC for the exact title, source identifier,
semimonotone/exact-order/conjecture and authors/3.12 found the primary paper,
its journal entry, and the old MathDB question, not a resolution. MathDB's
prior 403 is respected: no direct requests to that host were made. Search
results are indexed evidence only, not a current MathDB-body readback.

Closest primary body material exposed in official search extraction:
Tsatsomeros–Wendler, LAA 578 (2019), Corollary 5.4 gives an almost-E0 matrix
an existing nonpositive inverse; and Wendler, Special Matrices 7 (2019),
Theorem 3.4 gives the 3x3 determinant/adjugate characterization. Wendler's
Conjecture 4.1 includes a *separate* determinant sign claim for almost-E0;
nonpositive inverse alone does not justify a determinant sign. The 2023
Chauhan–Dubey follow-up DOI10.1016/j.laa.2022.12.008 explicitly reports
refutation of the unique-negative-eigenvalue assertion and proves a symmetric
case. Its full body is unread here. No prior endpoint or complete classical
subsumption of 3.12 has been established. These remain novelty/subsumption gaps.

## Mathematical work and failed routes

1. Each principal (n-1)-block is almost E0, because E0 is hereditary to
principal blocks. Hence it is nonsingular with entrywise nonpositive inverse,
by the source's Theorem 2.2. This is a known reduction, not a discovery.
Replacing the original question by this necessary local condition cannot be
justified as an equivalence unless the smaller-block E0 condition is retained.

2. The Z-restricted inverse assertion is routine from the source's own
block formula: for each excluded coordinate i, Theorem 3.9 has a positive
scalar Schur complement and nonpositive cross blocks in A^{-1}. Varying i
covers all off-diagonal entries. This does NOT solve unrestricted 3.12 and
receives no credit. Nor does proving the leading block for only one partition
constitute a new result.

3. General two-coordinate Schur attempt. Suppose a principal (n-2)-block H
is invertible and write A=[[H,u,v],[r,a,b],[s,c,d]]. Set
alpha=a-r H^{-1}u, delta=d-s H^{-1}v,
beta=b-r H^{-1}v, gamma=c-s H^{-1}u.
The two almost-E0 principal (n-1)-blocks force alpha<0 and delta<0 from
the corresponding inverse diagonal entries (their scalar reciprocals are
nonzero and <=0). Their cross-block signs force H^{-1}u,H^{-1}v,rH^{-1},
sH^{-1} entrywise <=0. However det A=det H*(alpha*delta-beta*gamma),
and these local facts do not fix beta*gamma or the signs of the full block
inverse. Moreover H may be singular. These are explicit missing steps, not
assumed bridges. The Z-case argument uses sign information on H^{-1} which
is unavailable for an arbitrary E0 block.

4. Cofactor route. For an invertible A, Jacobi gives
(A^{-1})_{jj}-(A^{-1})_{ji}(A^{-1})_{ij}/(A^{-1})_{ii}
=(A[delete i]^{-1})_{jj} whenever the denominators are nonzero.
If positive diagonal of A^{-1} were already known, this would force same-sign
nonzero off-diagonal pairs and a product bound. But positivity of those
diagonal entries requires a determinant-sign argument that is not available.
Assuming it would be circular. Also this identity cannot settle singular A.

5. A symbolic non-Z family was checked to understand the source examples:
A(p,q)=[[1,p,-1,-1],[q,1,-1,-1],[-1,-1,1,0],[-1,-1,0,1]].
For p,q<1 and pq<=1 all two-blocks are E0; the (n-1)-adjugates are
entrywise nonnegative with negative determinants, so A(p,q) is E02.
Writing D=pq-2p-2q+3=(1-p)(1-q)+(2-p-q)>0, det A=-D and its exact inverse
numerator is stored in check_exact.py. Every off-diagonal numerator is
nonpositive. This is a routine extension of the source example, NOT a
nominated outcome or resolution of the full question. It also explains why
that simple positive-entry perturbation route does not refute the question.

## Bounded diagnostics and their limits

check_exact.py uses exact rational/symbolic arithmetic and validates the
source's nonsymmetric 4x4 example (det=-3/2), its 5x5 example (det=-9),
and the polynomial inverse identity for A(p,q). The fixed examples inspect
15 and 31 principal supports respectively; this is not unbounded exponential
enumeration. The E0 classifier uses the known almost-E0 inverse theorem,
including its contrapositive in the singular case. These are source-example
and identity checks, not proofs of Conjecture 3.12.

diagnostic.py: 30,000 deterministic 4x4 one-entry mutations, 23,287 retained;
diagnostic5.py: 20,000 5x5 mutations, 13,682 retained. Both preserve numerical
local E0/almost-E0 tests and found no determinant or inverse-sign violation.
The largest retained determinant was -0.215755... (n4) and -6.342424... (n5);
closest inverse off-diagonal -0.000380... and -0.000383.... Floating tolerances,
seed dependence and local exploration mean this supplies no universal theorem
and no exact counterexample. No optimization or numerical evidence is called
proof. Source examples and their parameter family earn no discovery credit.

Run from this lane:
`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python check_exact.py`
`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python diagnostic.py`
`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python diagnostic5.py`
Each script imposes RLIMIT_AS=512MiB before importing numerical/symbolic
packages, and sets BLAS/OMP/MKL threads to one. The diagnostic ru_maxrss field
reported 622320 KiB despite the active 512MiB address-space cap; it is not used
to claim a measured peak below the cap (a child can inherit the parent's peak
accounting). No independent per-process resident-memory measurement was made.

## Strongest objection and remaining gap

No complete proof or counterexample exists in this lane. The central obstacle
is passing from all principal (n-1)-inverse signs and smaller-block E0 to global
nonsingularity, negative determinant and full inverse signs, without adding
Z, symmetry, P0 or nonsingular smaller-block hypotheses. A successful proof
must close these for arbitrary dimension, including singular smaller blocks.
A counterexample needs an exact certificate of all E02 hypotheses.

Even after mathematical success, the actual journal body, closest 2023/2024
companion bodies, a broader subsumption screen and current registry body-level
coverage would need completion. No global novelty claim, full Lean endpoint,
independent review, paper, acceptance or count increase is made. No PROOF.md
was created, because the full objective is unresolved.
