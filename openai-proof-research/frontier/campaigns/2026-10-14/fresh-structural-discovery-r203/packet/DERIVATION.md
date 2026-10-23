# Author derivation for the entire frozen r203 scope

This proves the statement in FROZEN.md, whose SHA-256 is `850bd50cd2888d4f184e8b164f1e8dfbd2258181f65adf22dc4b21d71ea52576`. It is an author proof, not an independent correctness verdict. All numerical symbols below have exactly the definitions in that statement. Every vector space and functional is real. The operative Source327 constructions at the stipulated pin are taken as true.

## 1. Finite Ramsey bookkeeping

We first verify the explicit Ramsey majorant used twice below. R_k(s,c) is an upper bound for the c-color Ramsey number for k-element subsets and a homogeneous set of size s. For k=1 this is pigeonhole. Suppose the claim holds for k−1 and put t=R_{k−1}(s,c)+1. Starting with N=(t+1)c^(t^k) vertices, greedily choose ordered vertices v_1,…,v_t. After choosing v_i, and for each (k−2)-subset of the preceding vertices, restrict the remaining reservoir to a largest color class for the k-set consisting of that subset, v_i, and a future vertex. There are at most

    sum_{i=1}^t binom(i−1,k−2) = binom(t,k−1) ≤ t^k

such restrictions in total. After a restrictions and i deletions the reservoir has at least N/c^a−i vertices; taking integer ceilings can only improve this lower bound. Thus it stays nonempty. Every (k−1)-subset of the first t−1 vertices now has a well-defined color for every later extension. Applying the induction hypothesis to this induced coloring yields s vertices homogeneous for the original k-coloring. This proves the recurrence. (All applications have s≥k and c≥2.)

Consequently S(a,h,c) has the following simultaneous property: any coloring of the k-element subsets, with at most c colors separately for each 1≤k≤a, has a common h-element set homogeneous at every arity. Thin in the order k=1,…,a, retaining b_k vertices at the kth step. Earlier homogeneity survives restriction.

## 2. A dimension bound for the paid chart construction

Use the Source327 action from `lem:action`, with, for example, the intervals

    [α_u,β_u]=[1/10,2/10],       [α_v,β_v]=[3/10,4/10],
    [α_{u^{-1}},β_{u^{-1}}]=[5/10,6/10],
    [α_{v^{-1}},β_{v^{-1}}]=[7/10,8/10].

They have pairwise disjoint closures. The paper defines the increasing periodic homeomorphisms h_s, h_{s^{-1}}=h_s^{-1}, and proves their displacement bound |h_s(y)−y|<2 and the two-level identities. We use precisely those maps and identities, not an external characterization of their dynamics.

For horizon n, the landmark set `eq:landmarks` has at most

    8L + (L+4n+1) sum_{j=0}^n 4^j = m

points: 2 endpoints for each of 4 letters in each of L translates, and at most sum 4^j words with each of L+4n+1 shifts. Coincidences reduce its size. Write λ for its actual cardinality. The order and each partial map h_s|_{D_s} are finite and exact.

Here is why the source's finite-order averaging and chart transport can use coefficient indices {1,…,B} with B as frozen. If necessary pad the landmark order to m elements. The number R of ordered equal-length subtuple comparisons is at most 4^m=r_0. In the separation proof of `lem:order-averaging`, bin each dual scalar function in [−1,1] into intervals of width at most

    d_0 = 1/(20 n r_0).

There are at most 40 n r_0+2 bins, so the combined color at each arity uses at most c_0=(40 n r_0+2)^(r_0) colors. The simultaneous Ramsey bound B=S(m,m,c_0) supplies the homogeneous order. Each dual pairing with the source comparison vector has absolute value at most R d_0≤1/(20n), strictly below ε=1/(10n). The source's finite-dimensional separation argument therefore gives a chart law whose required total-variation discrepancies are below ε. Restricting from the padded order to the actual landmarks preserves these discrepancies.

Apply the maximal-coupling construction of `prop:chart-transport`. It yields a finite stationary reversible marked chain on increasing charts C:Λ→{1,…,B}, with four independent uniform successive letters. At stationarity each step obeys

    C'(a)=C(h_s(a))   for every a∈D_s

with probability at least 1−1/(10n). There are at most B^λ≤B^m=A chart states and at most 4A² oriented marked edges. The reversal is (C,s,C')*=(C',s^{-1},C), so all star orbits have two elements. The stationary edge mass satisfies exact detailed balance. States of zero stationary mass are discarded. Nothing here depends on X or its norm, and no Markov inequality has been assumed.

## 3. Finite approximate spreading from the triangular array

Assume the hypothesis of Theorem A. Reverse the array of vectors. Color every increasing k-subtuple of the reversed array, for 1≤k≤H, by the rounded norms of all its combinations with coefficients in

    G_k={−1,−1+1/J,…,1}^k.

Use bins of width η/2. A norm is between 0 and k≤H. Thus there are at most ceil(2H/η)+2 choices per grid value, and at most (2J+1)^H grid values. The number of colors is at most c_1. Since M=S(H,H,c_1), the Ramsey construction gives H vectors x_1,…,x_H, still ordered as a reversed original subtuple, homogeneous at every arity.

Define a seminorm on coefficient arrays of length at most H by

    N_0(a)=||sum_i a_i x_i||_X,

appending zeros whenever necessary. We do not need it to be positive definite. It satisfies N_0(a)≤||a||_1 and is 1-Lipschitz for the coefficient ℓ_1 norm. For coefficients in [−1,1]^k, approximate by a grid point within 1/J in each coordinate. Norms on two k-subtuples differ by at most

    η/2 + 2k/J ≤ η/2 + 2H/J ≤ η.

Homogeneity, with the zero vector handled separately, gives the approximate-spreading inequality

    |N_0(sum_{i=1}^k a_i b_i) − N_0(sum_{i=1}^k a_i b_{q_i})|
        ≤ η||a||_∞ ≤ η||a||_1,                         (1)

for 1≤q_1<…<q_k≤H. This applies also to arrays with zero coefficients.

The triangular functionals give a lower bound which survives all subsequent subdivisions. If x_i=y_{j_i}, then j_1>…>j_H. The functional f_{j_k} takes values within σ of θ on x_1,…,x_k, and within σ of zero on x_{k+1},…,x_H. Therefore

    N_0(a) ≥ θ max_k |sum_{i≤k}a_i| − σ||a||_1.       (2)

Indeed, apply f_{j_k}, use ||f_{j_k}||≤1 and the triangle inequality for the scalar error, then maximize k. This requires neither completeness nor separation assumptions about X. It is equally valid for every finite subarray used below.

## 4. Finite subdivision averaging with an explicit error

For a positive integer d let F_d replace each coefficient a_i by d consecutive copies of a_i/d. For varying positive integers d_i, write F_bold_d for the corresponding blockwise subdivision. Each preserves the coefficient ℓ_1 norm. If d_i≤e_i, choose uniformly a d_i-element subset of the e_i positions in block i, and put a_i/d_i in the chosen positions, zero elsewhere. Every sample is a spreading of F_bold_d a. Its mean is F_bold_e a. Convexity and (1) imply, whenever the arrays fit in H coordinates,

    N_0(F_bold_e a) ≤ N_0(F_bold_d a)+η||a||_1.       (3)

Now define, on arrays of length at most BQ,

    N(a) = [T^(-1) sum_{j=0}^{T−1} N_0(F_{Q^j}a)^p]^(1/p).  (4)

Every array in (4) fits in H=BQ^T coordinates. This is the exact seminorm of the linear map

    U(a)=T^(−1/p)(sum_i(F_{Q^j}a)_i x_i)_{j=0}^{T−1}
           into V=ℓ_p^T(X).

In particular N is symmetric, homogeneous, convex, and 1-Lipschitz for ℓ_1. Formula (1) and the reverse triangle inequality in ℓ_p imply

    |N(a)−N(spread(a))|≤η||a||_1,                     (5)

whenever both arrays have length at most BQ. Refined blocks give an increasing injection into H coordinates, so (1) applies at each scale with the same ℓ_1 bound.

For a of length at most B and 1≤d_i≤Q, put

    v_j=N_0(F_{Q^j}a),
    w_j=N_0(F_{Q^j}F_bold_d a),       0≤j<T.

Formula (3), first between Q^j and Q^j d_i pieces, then between Q^j d_i and Q^(j+1) pieces, gives

    v_{j+1}−η||a||_1 ≤ w_j ≤ v_j+η||a||_1.

Moreover all v_j lie in [0,||a||_1]. The pth powers of the shifted and unshifted averaged ℓ_p norms differ by (v_T^p−v_0^p)/T. For nonnegative u,v and p≥1, |u−v|^p≤|u^p−v^p|. It follows that these two averaged norms differ by at most T^(−1/p)||a||_1. Applying the ℓ_p triangle inequality to the componentwise bounds proves

    |N(F_bold_d a)−N(a)|≤δ||a||_1,
    δ=T^(−1/p)+η.                                   (6)

This is a finite estimate. No rate of convergence of an infinite subdivision limit is assumed. Equally importantly, U maps into an ℓ_p sum, not into X; Section 7 below will eliminate that sum by selecting a coordinate of an actual finite-chain inequality.

## 5. Approximate consecutive merging, including cancellation

For any coefficient array a of length at most B, let merge(a) combine two adjacent coefficients. We prove

    N(merge(a)) ≤ N(a)+ζ||a||_1,
    ζ=4δ+4/Q+6√η ≤ ξ.                               (7)

The zero array is trivial. Set W=||a||_1 and write the pair as (u,v), with sum s. If uv≥0, choose an integer 0≤r≤Q with |u−rs/Q|≤|s|/Q, and replace the pair by (rs/Q,(Q−r)s/Q). The total ℓ_1 perturbation is at most 2W/Q. If 0<r<Q, subdivide these two coefficients into r and Q−r parts respectively; subdivide their merged coefficient s into Q parts. Keep every other coefficient unsplit. The resulting arrays are identical. Applying (6) twice gives error at most 2δW. If r=0 or Q, insertion/removal of one zero is handled by (5), with error at most ηW≤2δW. Thus in the same-sign case

    |N(merge(a))−N(a)|≤eW,  e=2δ+2/Q.                (8)

For the opposite-sign case first suppose |s|≥τW, where τ=√η. By multiplying the whole array by −1 if needed, take s>0. The point (u,v) lies outside the segment joining (s,0) and (0,s). One endpoint is a convex combination α(u,v)+(1−α) times the other endpoint, with α=s/max(|u|,|v|)≥τ. The unchanged other coordinates are included in this convex combination. Both endpoint norms differ from N(merge(a)) by at most ηW, by (5). Convexity therefore gives

    N(merge(a))≤N(a)+2ηW/α≤N(a)+2τW.                (9)

If |s|<τW, perturb v so that the new sum s' has absolute value τW, choosing its sign to agree with s and choosing positive sign when s=0. The perturbation is at most τW, and the new coefficient mass W' is at most (1+τ)W. The original and merged arrays together pay at most 2τW by ℓ_1 Lipschitz continuity. If the new pair has the same sign, (8) costs at most eW'≤2eW. Otherwise the same endpoint argument costs

    2η(W')²/|s'| ≤ 2(1+τ)²τW.

Here τ=ξ/24≤1/24<1/4, so 2(1+τ)²+2≤41/8<6. Thus this last subcase costs at most 6τW including the perturbation. All cases are bounded by (2e+6τ)W, which is the first expression in (7). This proof explicitly covers s=0, mixed signs, and zero coefficients.

Finally T^(−1/p)≤ξ/16, 1/Q≤ξ/16, η=ξ²/576, and 0<ξ≤1. Therefore

    ζ ≤ ξ/4+4η+ξ/4+ξ/4 = 3ξ/4+ξ²/144 ≤ ξ.

A partition into consecutive blocks is obtained by at most B adjacent mergers. Since merging never increases coefficient ℓ_1 mass, its total error is at most Bξ times the original mass.

## 6. Robust form of the source's chart walk

Use the chart chain from Section 2 and exactly the raw labels from Source327 `eq:labels`. For positive letters s, set

    g(C,s,C')=sum_{j=0}^{L−1}(b_{C(α_s+j)}−b_{C(β_s+j)}),

and define the negative labels by oddness. These are arrays in the first B coordinates. Define

    D_k=N(1,−1,…,1,−1), with k pairs.

At every subdivision scale the vector F_{Q^j}(1,−1)^L has ℓ_1 mass 2L and a prefix sum 1. Formula (2) therefore implies

    D_L≥θ−2Lσ=θ/2>0.                                (10)

Formula (5) shows that every edge label has

    N(g(e))≤D_L+2Lη≤2D_L,                            (11)

because 2Lη≤2Lξ=θ/(2048B)≤θ/2. This also handles negative labels, by symmetry of N.

Consider n steps, all satisfying the chart match, and let ℓ>0 be the reduced length of their word. The source's exact scalar construction (`lem:two-levels`, `eq:transport-rank`, `eq:F-cocycle`, `eq:F-levels`) gives the following facts about G=sum_{i=1}^n g(E_i): its total coefficient sum is zero; ||G||_1≤2Ln; and there are interlaced ranks r_j<t_j<r_{j+1}, L/4≤j≤3L/4, where its prefix sums equal V_0=−n_- and U_0=n_+, respectively. Here U_0−V_0=ℓ, 0≤U_0≤ℓ, and |V_0|≤ℓ. These facts depend only on the labels, charts, action, and word, not on any norm hypothesis. All selected ranks and cuts fit inside {1,…,B}, exactly as proved in the source; in particular the final compressed block is nonempty.

Compressing at these ranks yields

    h=(V_0, ℓ,−ℓ,…,ℓ,−ℓ, −V_0), with L/2 inner pairs.

Put E=2BLnξ. By (7), N(G)≥N(h)−E. Remove the two endpoints by the triangle inequality and use (5) for the interior and endpoint placements. This gives

    N(G)≥ℓ(D_{L/2}−D_1)−E−ηℓ(L+2).                 (12)

Independently, compress at a single r_j or t_j. The resulting arrays are (V_0,−V_0) and (U_0,−U_0). The same error bound gives

    N(G)≥max(|V_0|,U_0)D_1−E≥(ℓ/2)D_1−E.          (13)

For nonnegative a,b, max(a−b,b/2)≥a/3. Apply this to (12)–(13). Also splitting the 2L alternating coefficients into two consecutive blocks gives

    D_L≤2D_{L/2}+ηL,

since the second block is a spreading of the first. We obtain

    N(G)≥ℓ D_L/6−E−2ηn(L+2).                        (14)

The quantitative losses are small enough uniformly over the entire construction. Since B≥3, L≥16, and η≤ξ,

    E+2ηn(L+2) ≤ 2BLnξ+6Lnξ
                ≤ 4BLnξ = θn/1024 ≤ θn/96 ≤ nD_L/48.  (15)

The letters are independent uniform choices from four inverse-paired letters. The conditional expected increment of reduced-word length is 1/2 away from zero and 1 at zero. Thus Eℓ≥n/2. Since ℓ≤n,

    P{ℓ≥n/4}≥1/4.

A union bound for the n matching failures gives probability at most 1/10. Consequently all chart matches hold and ℓ≥n/4 with probability at least 3/20. Equations (14)–(15) imply on this event

    N(G)≥nD_L/48.                                   (16)

This is the required robust version of the source's exact-spreading walk. It was derived for the finite seminorm N; it does not improperly apply `prop:walks` to an approximately spreading norm.

## 7. An actual finite-chain map into X

Let r be the number of unoriented marked edge pairs. Then 1≤r≤2A². Choose one representative e_j of each pair and give these displacements +u_j in Z^r, with reversed edges receiving −u_j. Set R=4nA² and use the source's lattice lift on

    S = {chart states} × {−R,…,R}^r.

Propose marked edges with their original probabilities and reject an attempted move leaving the cube by staying at the full current state. Detailed balance holds for the product of the chart law with the uniform cube law: accepted opposite transitions have equal stationary mass, and rejections add self-loops. The resulting unmarked state chain is finite, stationary, and reversible. Marked loops carrying nonzero labels cause no difficulty because their lattice coordinates change.

The state-count bound is

    |S|≤A(2R+1)^r≤A(8nA²+1)^(2A²)=C(n).             (17)

Define the V-valued potential

    Ψ(C,a)=U(sum_{j=1}^r a_j g(e_j)).

Its accepted increment on a marked edge e is U(g(e)); rejected increments are zero. Hence (11) gives

    E||Ψ(Z_1)−Ψ(Z_0)||_V^p≤(2D_L)^p.                (18)

An initial lattice point in {−R+n,…,R−n}^r accepts every possible n-step proposed path. This event is independent of the marked trajectory, and its probability α satisfies

    α=(1−2n/(2R+1))^r≥1−2nr/(2R+1)>1/2.

On that event the potential displacement is U(G). By (16),

    E||Ψ(Z_n)−Ψ(Z_0)||_V^p≥(3/40)(nD_L/48)^p.       (19)

There is no infinite-volume limit in (17)–(19).

Write Ψ=(Ψ_0,…,Ψ_{T−1}) in V=ℓ_p^T(X), and let v_j,u_j be the corresponding one-step and n-step p-costs in X. Then (18)–(19) imply

    sum_j u_j ≥ (3/40)(n/96)^p sum_j v_j.            (20)

The right denominator sum_j v_j is positive: otherwise every one-step coordinate increment would vanish almost surely, and by stationarity every increment through time n would vanish, contradicting (19). The same argument shows v_j=0⇒u_j=0. Therefore some coordinate j with v_j>0 satisfies

    u_j/v_j≥(3/40)(n/96)^p.

Take F=Ψ_j/v_j^(1/p). Its image lies in the real span of the original y_i. Its one-step cost is exactly 1, and its n-step cost obeys the frozen lower bound. This proves all of Theorem A. The only normalization is scalar multiplication in the original norm of X.

## 8. Quantitative J-convexity

Assume the hypotheses of Corollary B. At n=n_* the conclusion of Theorem A would contradict Markov type, because

    n_*^(p−1)>(40/3)(96K)^p.

Thus X has no triangular array of length M_* with θ=1 and entry error at most ε_*=1/(4L_*).

Suppose, toward a contradiction, that x_1,…,x_{M_*} in the unit ball have every admissible signed sum of norm strictly greater than M_*−ε_*. For j=1,…,M_*, use real Hahn–Banach to choose a norming functional g_j of norm at most 1 for

    S_j=sum_{i≤j}x_i−sum_{i>j}x_i.

Set g_0=−g_{M_*}. Since each signed summand g_j(±x_i) is at most 1 and their sum is greater than M_*−ε_*, each individual deficit is less than ε_*. Consequently g_j(x_i) is within ε_* of +1 for i≤j, and within ε_* of −1 for i>j. The same description for j=0 follows from g_0=−g_{M_*}.

For j=1,…,M_*, put

    f_j=(g_{M_*}−g_{j−1})/2.

These have norm at most 1. For i<j the two terms both approximate +1, so |f_j(x_i)|≤ε_*. For i≥j they approximate +1 and −1, so |f_j(x_i)−1|≤ε_*. Thus (x_i,f_j) is the prohibited θ=1 triangular array. This contradiction gives an admissible j with ||S_j||≤M_*−ε_*, exactly as frozen. Dividing by M_* gives the displayed normalized J-convexity deficit.

The zero space satisfies the conclusion trivially; a nonzero space satisfying ordinary Markov type necessarily has K≥1 by a nonconstant two-state test at time 1, consistent with the stated assumption. No step assumes infinite dimension or separability. Completeness is never used. For a complex space the argument may be applied to its underlying real space, but the frozen theorem makes no separate assertion about complex-linear functionals or complex renormings.

## 9. What is and is not supplied

The full frozen scope has an author derivation above. The paid source operations are the action/two-level identities and reversible-chart mechanism; the finite-state lattice lift is used in its explicit reflected-cube form. The added quantitative operation is (4)–(7), together with its propagation through the source walk and coordinate extraction. Ramsey thinning, scalar Hahn–Banach, convexity, and ℓ_p summation are classical operations and are not credited as inventions.

This proof does not supply a renorming power, renorming distortion, an endpoint martingale-type implication, optimal dependence, a downstream manuscript, or formal proof coverage. The comparator's `sorry` is not evidence for this theorem. Whether the quantitative finitarization is sufficiently substantial after the strongest known reduction remains a separate contribution-review question. No favorable grade, acceptance, or count is assigned here.
