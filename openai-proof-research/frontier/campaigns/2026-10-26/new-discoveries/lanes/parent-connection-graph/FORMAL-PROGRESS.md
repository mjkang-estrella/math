# Complete formal development, pending final review

26 October 2026. Discovery credit remains **0**; accepted campaign tally remains
**13/30**. The preliminary source/math/bounded-novelty review passed. The complete
source-level Lean endpoint and a rendered three-page manuscript now exist.
Final independent review and an extracted deterministic packet replay remain.

**Seventeen modules / 211 declarations pass a fresh isolated strict replay**
with pinned Lean4.34.1/mathlib and warningsAsError. Every declaration type and
axiom report has been read; only propext, Classical.choice and Quot.sound occur.
The record is verification/complete-audit.json and complete-checks.log.
Historical checkpoints135/161/185 declarations remain in separate receipts.

The Pi implementation contributed DiracPositive.lean (22 declarations), copied
byte-for-byte into the parent and recompiled against the current dependencies.
It explicitly proves positive-Dirac vertex-component normalization, handles
repeated eigenvalues, and derives the small-index degree bound and global bound.
GraphComparison.lean combines these with the two L-side bounds and the edgeless
case. Its closed source_graph_strict_gap endpoint quantifies over the actual
finite downward-closed face family, all faces of size1or2, and all1<=k<=#faces.
Support restriction handles unused ambient vertices. Both matrices are literal
face-indexed source matrices; signed sorted eigenvalue sums and all reindexing
are proved, including repeated and negative eigenvalues. No rank/spectral
existence assumptions survive as endpoint premises.

The implementation author will not serve as final independent reviewer. No
helper, constant, finite numerical example or known spectral ingredient is
counted as a separate discovery. Higher-dimensional source conjecture untouched.

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
D upper bound m+v/2 this yields gap ≥1/2. The L-side argument is formalized in `HighConnection.lean`; the D bounds and
combined endpoint are now formalized in `DiracPositive.lean` and
`GraphComparison.lean`.
