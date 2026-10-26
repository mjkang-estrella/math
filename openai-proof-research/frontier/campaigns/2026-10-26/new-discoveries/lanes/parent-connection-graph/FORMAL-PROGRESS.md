# Formal development checkpoint

26 October 2026. Discovery credit remains **0**; accepted campaign tally remains
**13/30**. The source/math/bounded-novelty preliminary review passed. No full
Lean endpoint, manuscript, final review, or extracted packet exists yet.

Fourteen modules now pass a **fresh isolated strict replay: 161 declarations**, with
pinned Lean 4.34.1/mathlib and `warningAsError=true`; every declaration type and
axiom report was read. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
The main theorem remains absent: the manifest explicitly identifies this as an
incomplete development checkpoint, with credit 0.

The completed scope includes scalar estimates, graph incidence/energy
identities, the literal intersection-matrix block identity, exact sorted sums
for signed arrays, the finite-dimensional Ky Fan inequality, the normalized
positive connection eigenvector family (including zero/repeated Q eigenvalues),
both connection lower bounds, and the edgeless comparison. The vertex/edge
indexing is proved bijective with a downward-closed family of nonempty faces
of cardinality one or two, and its connection matrix is the literal
face-intersection matrix. The boundary and Dirac matrices are also defined
directly on actual faces, and their spectral sums are proved equal to the
block-indexed sums. A finite family containing every vertex singleton and only
singleton/pair faces is reconstructed exactly from its canonical graph edges.
This permits the final endpoint to quantify over the actual source face
family. Spectral reindexing is proved using characteristic-polynomial roots
with multiplicity and uniqueness of the sorted value list; negative values
and repeated eigenvalues are included. Classical ingredients receive no
separate credit.

The earlier 135-declaration checkpoint is preserved in
`verification/development-audit.json`; the expanded checkpoint is in
`verification/source-bridge-audit.json` and its corresponding checks log.

The positive-Dirac-eigenvector argument and D upper bounds are assigned to a
Pi/GLM 5.3 Flash implementation worker at standard speed, in its separate lane.
They and the full graph comparison endpoint are still required. No numerical
check or already-proved helper is counted as an outcome.

## Clarifications to the preliminary review

The review correctly recommends eligibility subject to the remaining gates.
Its “3 gate evaluations” are not three outcomes, and change no tally. Its
novelty conclusion is a bounded search, not a proof that no prior body exists.

Two numerical explanatory slips in the report do not affect the proposal:
for a single edge, the largest eigenvalues are **1+sqrt(2)** for L and
**sqrt(2)** for D, whose difference is 1 (they are not 2 and 1). For an edge
{i,j} and z=e_i+e_j, the quantity ||Uᵀz||² equals delta_i+delta_j+2 **≥ 4**;
it need not equal 4 when further edges meet its endpoints. The parent proof
already states the correct lower bound. Neither informal slip is used in Lean.

## A variational route that avoids unnecessary full-spectrum equalities

The original handproof remains valid. For the formal proof we may use weaker
intermediate inequalities sufficient for the same closed graph endpoint.
This avoids treating a full SVD/rank-counting assertion as an assumption.

Let w_i=(a_i,b_i) be an orthonormal family of positive D-eigenvectors,
with eigenvalues mu_i>0. The block equations give

    C b_i = mu_i a_i,     Cᵀ a_i = mu_i b_i.

For any i,j, adjointness gives mu_i <b_i,b_j> = mu_j <a_i,a_j>
and mu_j <b_i,b_j> = mu_i <a_i,a_j>. Adding these identities and using
mu_i+mu_j>0 shows <a_i,a_j>=<b_i,b_j>=delta_ij/2. Thus the
vectors sqrt(2) a_i form an orthonormal family of H-eigenvectors with
eigenvalues mu_i². Ky Fan plus H≤2Delta and Cauchy therefore give the
required upper bound for any selected positive D eigenvalues; negative
selected eigenvalues can only decrease their sum. No claim about exact zero
multiplicities is needed on this alternative route.

For L, each Q-eigenvector u with eigenvalue q≥0 gives a positive eigenvector

    ((phi(q)+1)u, phi(q) Uᵀu).

The identity phi(q)²-q phi(q)-1=0 verifies this uniformly, even at q=0.
Vectors constructed from an orthonormal Q-eigenbasis are pairwise orthogonal;
their norms are strictly positive. Ky Fan supplies the needed lower sums.
These construction and normalization steps are now formalized in
`ConnectionLift.lean` and used by `LowConnection.lean`.

For large k one can alternatively avoid a full inertia theorem as follows.
The quadratic identity xᵀ(L+I)x=||a||²+||a+Ub||² proves every L eigenvalue ≥−1.
Write g=sum_i 1/phi(q_i)>0. Then sum_i phi(q_i)=2m+g, and Cauchy gives
v²≤(2m+g)g. Simplicity implies 2m≤v(v−1), hence g≥1. Consequently
S_v(L)≥2m+1 and S_k(L)≥2m+v+1−k for k≥v. The diagonal Ky Fan bound
also gives S_k(L)≥k, so S_k(L)≥m+v/2+1/2. Together with the original
D upper bound m+v/2 this yields gap ≥1/2. The L-side argument is now formalized
in `HighConnection.lean`; the D upper bound and combined endpoint are pending.
