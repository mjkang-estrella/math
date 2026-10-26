# Proposed strict connection–Dirac spectral dominance in dimension at most one

Parent mathematical discovery proposal, 26 October2026. Credit0: no independent review/full Lean endpoint/paper/packet yet. This is ONE prospective general graph-case theorem for MathDB372758 / Knill2601.18071v2Conjecture1. It does NOT settle higher-dimensional complexes.

## Exact source and scope

Actual latest2601.18071v2 (July29,2026), sections1.6,1.7,5.1–5.5 and10 read. The conjecture asks S_k(L)≥S_k(D) for EVERY finite abstract simplicial complex and all ordered spectral sums1≤k≤number of faces. The source separately asks questions about g=L⁻¹; those are NOT this theorem. A known July2026George2-skeletonK5counterexample already disproves its spectral-radius comparison and even the g weak-dominance direction; never count that as a new finding. Likewise repeated positive maximal eigenvalues of g for K_n1-skeleta follow immediately from the old hydrogen identity and receive no credit here.

Proposed theorem: let G be ANY nonempty finite abstract simplicial complex with faces of cardinality at most2. Equivalently, take a finite simple graph as its vertex-and-edge complex, including isolated vertices and disconnected graphs. No higher clique is filled in: for example a3-cycle means its boundary1-complex, not a filled triangle. Let v≥1 be the number of vertices, m the number of edges and N=v+m. For every1≤k≤N,

    S_k(L) - S_k(D) ≥ sqrt(2)-1 >0.

One may omit the quantitative constant and retain strict dominance if that simplifies a first source endpoint, but no new outcome/helper counts result. The theorem is a substantive infinite-class case of the source conjecture, not the full higher-dimensional conjecture. Novelty and suitability under the campaign standard remain subject to serious independent review.

## Complete matrix model

Order simplices with vertices first. Let U be the v×m unsigned incidence matrix (two1entries in every edge column), C an arbitrarily oriented incidence matrix (one+1,one−1 per column), Delta=diag(delta_i) the vertex degree matrix, Q=U Uᵀ and H=C Cᵀ. Then

    L = [[I_v, U], [Uᵀ, UᵀU-I_m]],
    D = [[0, C], [Cᵀ, 0]].

These are EXACT literal source matrices. In the lower block of L, two distinct simple edges have at most one common vertex, and the diagonal of UᵀU is2. Thus this block is precisely the connection indicator matrix on edges. Simplicial boundary orientations change D by orthogonal diagonal conjugation and cannot change the result.

## Spectrum of L (old identity/block reduction, credited)

Let q1≥...≥qv≥0 be the eigenvalues of Q, and put

    phi(t) = (t+sqrt(t²+4))/2.

If u is a unit Q-eigenvector with q>0, set w=Uᵀu/sqrt(q). The vectors (u,0),(0,w) are orthonormal and L restricts to

    [[1,sqrt(q)],[sqrt(q),q-1]],

whose eigenvalues are phi(q)>0 and -1/phi(q)<0. Different Q-eigenvectors yield orthogonal invariant2-planes. The remaining vertex-kernel vectors give eigenvalue1; remaining edge-kernel vectors give−1. Consequently L has EXACTLYv positive andm negative eigenvalues, with its positive spectrum precisely phi(q1),...,phi(qv) (phi(0)=1). Since phi is increasing,

    S_k(L) = sum_{i=1}^k phi(q_i)   (k≤v).

The identity L−L⁻¹=diag(Q,UᵀU) is Knill's OLD2018hydrogen identity1803.01464, actual sourceTheorem1 andsections2.16–2.18 read and credited. The positive-branch formula is the elementary block diagonalization of that same identity, not itself a claimed new theorem. The source2018paper's Schur discussion bounds the largest spectral values; no comparison of ALL ordered partial sums with the SIGNED Dirac operator was found in the sections inspected. A serious broader novelty check is pending.

## Upper bound for D from degrees

For every real z,

    zᵀ H z = sum_{edges {i,j}} (z_i-z_j)²
            ≤ 2 sum_i delta_i z_i².

Thus H≤2Delta in the ordinary Loewner order. Write ell1≥...≥ellv≥0 for the eigenvalues of H and delta1↓≥...≥deltav↓ for the sorted degrees. Eigenvalue monotonicity gives ell_i≤2delta_i↓ for each i.

The nonzero spectrum of D is ±sqrt(ell_i). If r=rank C, D has r positive/r negative eigenvalues and N−2r zeros. Since r≤m, this zero multiplicity is at least v−r. Hence for every k≤v the top-k sum of D is EXACTLY the sum of the firstk entries of sqrt(ell1),...,sqrt(ellv), including zeros. Cauchy–Schwarz yields, with T_k=sum_{i≤k}delta_i↓,

    S_k(D) = sum_{i≤k}sqrt(ell_i)
            ≤ sqrt(2k T_k).

All claims also hold when m=0 (then H=D=0).

## Lower bound for L and strict comparison when k≤v

The diagonal of Q is the degree vector. Schur–Horn / KyFan variational principle gives

    sum_{i≤k}q_i ≥ T_k.

Moreover phi(t)≥1+t/2, with excess e(t)=sqrt(t²+4)/2−1≥0. Therefore

    S_k(L) ≥ k + T_k/2 + e(q1).

The elementary inequality k+T_k/2≥sqrt(2k T_k) follows by squaring: the difference of squares is (k−T_k/2)²≥0. Thus S_k(L)−S_k(D)≥e(q1).

If m>0 choose an edge{i,j}. For z=e_i+e_j,

    zᵀQz = delta_i+delta_j+2 ≥4,  ||z||²=2,

so q1≥2 by Rayleigh's principle. Consequently e(q1)≥e(2)=sqrt2−1. This proves the stated quantitative gap for allk≤v when m>0. If m=0, L=I_N,D=0, and the gap equalsk≥1>sqrt2−1.

## Remaining indices v≤k≤N

All eigenvalues after the firstv of L are strictly negative. Since tr L=N,

    S_k(L) ≥ N.

The largest possible top-k sum of D is its positive spectral sum. Using sqrt(t)≤(t+1)/2 for all t≥0 and tr H=2m,

    S_k(D) ≤ sum_{i=1}^v sqrt(ell_i) ≤ m+v/2.

Hence S_k(L)−S_k(D)≥v/2≥1/2>sqrt2−1. Together with the previous case this proves the theorem for every allowedk. No connectivity, nonzero-degree or rank assumption is left as a hypothesis.

## Checks and honesty ledger

check_graphs.py independently constructs the two literal block matrices and computes all ordered eigenvalues for2400seeded random graphs, v1..12,200each, including disconnected graphs/isolates. Every claimed intermediate bound and strict dominance passes (smallest observed numerical gap about1). This is numerical supporting evidence ONLY, not a proof or novelty certificate. Proposed general proof above supplies the mathematical argument; it needs independent checking and a full Lean matrix/graph/spectral bridge before any credit.

Known ingredients credited: unsigned/signed incidence formulas, SVD/eigenbasis block reduction, Knill2018hydrogen identity, Schur–Horn/KyFan, Loewner eigenvalue monotonicity, Cauchy–Schwarz and scalar AM–GM. No claim to have invented these. The prospective new contribution is their universal source-faithful all-k comparison (with a uniform strict gap) for all1-dimensional finite complexes. If a known theorem already states or immediately subsumes that comparison, discovery credit must remain0. No current independent novelty screen, no absolute priority claim, no source QuestionB/C/g extra credit.
