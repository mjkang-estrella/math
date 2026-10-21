# Integrated prefreeze calculation: Source039

Status: PREFREEZE / no nominee. These are working reductions and finite diagnostics, not a frozen theorem, author-proof submission, or a contribution verdict. The question remains the whole homogeneous postulation formula in `feasibility.md`, for every r>=10, d>=0, m>=1 over C at very general distinct plane points. It is the classical homogeneous SHGH question, not a newly named conjecture. No bounded-m replacement is offered.

## What the source already pays

The pinned plane proof supplies the strict Nagata inequality, including unequal multiplicities and square r. On the very general blow-up let E denote the sum of the exceptional curves and N=sqrt(r)H-E. Then N is strictly nef and N^2=0. For D=dH-mE, h0(D)=0 when d<=m sqrt(r). When d+3>(m+1)sqrt(r), the integral class

    D-K = (m+1)N + (d+3-(m+1)sqrt(r))H

has positive square and positive intersection with every curve. Nakai and Kodaira vanishing give H1(D)=0. H2(D)=0 because K-D has negative H-degree. Riemann–Roch gives the required dimension. This standard argument, also present in Ciliberto–Miranda's Proposition 2.3, is not a contribution. The initial strip left by this composition is

    m sqrt(r) < d <= (m+1)sqrt(r)-3.                 (1)

It is an upper enclosure of the remaining work, not a claim that every case in it is unresolved. The full proof of Ciliberto–Miranda 2011 was read: its d/m>=174/55 region for r=10 includes genuine one- and two-throws, matching restrictions, transversality and exceptional-case calculations. The Dumnicki 2007 determinant cuts and fixed-m reduction induction, including the published m<=42 conclusion, were read; ancillary finite computations were not replayed. These are compatible paid operations, not missing bridges.

A late read of Roé's 10 October 2012 author manuscript identifies Theorems 1–2 covering r>=4m^2 and square r. Its differential Horace trace/residual construction and termination proof were read in parts, with broken HTML formulas and transitive omissions; see READING.md. Those theorem regions are credited in the comparison. The earlier notes' broader strip was not a novelty claim. Thus a useful enclosure after these known inputs has r nonsquare, r<4m^2, m>42, and (1), also removing the Ciliberto–Miranda region for r=10. This enclosure is still not an exhaustive literature classification.

## Dimension preservation through the cubic normal limit

The source's necessary-normal-polynomial proposition is stated for nonzero sections. A dimension claim must retain the whole kernel. Here is the elementary finite-dimensional refinement used in these calculations.

Fix d>3m and nine distinct points P on a smooth plane cubic B with equation G. Let V9=H0(P2,I_(mP)(d)). The residual sequence along B at each step j<m is

    0 -> I_((m-j-1)P)(d-3j-3)
      -> I_((m-j)P)(d-3j)
      -> O_B(d-3j)(-(m-j)P) -> 0.

Each right-hand line bundle has degree h=3(d-3m)>0 and hence H1=0 and h0=h. At j=m the remaining plane sheaf is O(d-3m), whose H1 vanishes. Descending induction therefore makes all these restriction maps on H0 surjective and H1 vanish. Beyond j=m, the ordinary cubic restriction sequence has the same surjectivity, using H1(O_P2(t))=0 for every integer t. Consequently the G-adic associated graded of V9 is exactly the direct sum of the source coefficient spaces, not just a subspace:

    j<m: H0(B,O_B(d-3j)(-(m-j)P));
    m<=j<=floor(d/3): H0(B,O_B(d-3j)).

The final summand has dimension one if d-3j=0. The source change w=sigma_P v and division by sigma_P^m identifies this sum with W. In particular

    dim W = binom(d+2,2) - 9 binom(m+1,2).         (2)

Choose a basis adapted to this finite filtration. A lift in filtration degree j is G^j R. In local coordinates (zeta,t), t=G in a frame, the substitution t=s w followed by multiplication by s^(-j) turns the lift into w^j R(zeta,sw), regular at s=0 with the prescribed graded basis vector as limit. For each s!=0 this rescaling of the basis is invertible. Keep the first nine points stationary on B. Move the additional q=r-9 points along holomorphic paths (zeta,t)=(zeta_i,s c_i), with distinct zeta_i off P. At these moving points the rescaling is a local biholomorphism for s!=0; all ordinary derivatives of order<m form a finite matrix converging to the W jet matrix. Multiplication by the nonvanishing sigma_P factors changes jets invertibly. Thus any rank-R minor for W persists for small s. It bounds the actual kernel by dim W-R. The elementary lower bound from the number of imposed conditions gives equality whenever R=min(dim W,q binom(m+1,2)). Rank openness then passes from this special witness to general tuples; countably many fixed triples can be imposed on a common very general locus.

This pays the existence-to-dimension refinement without assuming that independently chosen normal-polynomial limits remain independent. It is standard finite filtration and minor persistence, consistent with the source's transfer lemmas and the classical diagram method. It does not construct the missing uniformly maximal minor.

## The finite interface has more freedom than one collided diagram

The source's theta limit provides bases converging with all fixed derivatives to z^K v^j. For its nonsquare choice alpha=3(sqrt(r)-3), h=3(d-3m), and rational 0<Delta<1/2, the interval starts are

    U_j=(d-3j)alpha/3-h Delta/9                (j<=m),
    U_j=(d-3j)(alpha-Delta)/3                 (j>m),

with lengths h and 3(d-3j), respectively. Integral (j,K) satisfy U_j<K<U_j+n_j, together with the degree-zero terminal singleton. The exact cardinality is (2). The functions `floor_quad` and `diagram` make these choices by rational comparisons and integer square roots.

The special value of alpha is needed for the below-slope polygon estimate, not for defining the cubic, bundles, coefficient spaces or theta convergence. At a fixed d,m one may instead choose any real alpha avoiding the finitely many integral-endpoint conditions, with eta=(sum x_i+alpha)/3. All coefficient multipliers and normalized theta bases remain valid. Rational alpha is also allowed if the endpoints are nonintegral. Therefore a deficit in one alpha/Delta chart is not a geometric obstruction.

Nor must the q points be collided. Arbitrary distinct torus base positions and nonzero fiber coordinates are allowed normal displacements. A finite jet minor at such points persists first through the theta limit and then through the cubic normal limit. In the tests, z positions 1,2,3,4 and fiber values 1,3,2,4 have logarithms lying in a disk of radius less than pi; for sufficiently small tau that disk is embedded and disjoint from P. Thus the uncollided test is compatible with the actual covering-space charts. The collision used by the source is an optional flat limit to (x^q,y)^m. Its rows become K^ell j^b, b<m and ell<q(m-b), after invertible changes between ordinary and logarithmic jets.

Dumnicki's affine separating cuts apply to these Laurent exponent sets after translating them to nonnegative exponents (a monomial is a unit at the torus points). The strict separating functional isolates a unique extremal block term in the determinant. Consequently this classical gluing operation is available simultaneously with the theta and normal transfers. It has not been proved here that a suitable cut sequence exists for every triple in (1).

## Exact diagnostic repairs and their limits

At (r,d,m)=(13,11,3) with Delta=1/1000, the 24-by-24 collided matrix has rank exactly 22 over Q, not merely rank 22 modulo a prime. `finite_repair.py` computes two rational left-null vectors and checks them. One is a degree-eleven polynomial in K vanishing on all the represented K-levels. Nevertheless Delta=49/100 gives rank 24 modulo 1000003; alternatively, keeping Delta=1/1000 and using the four uncollided points above gives rank 24 modulo that prime. A nonzero modular determinant certifies a nonzero rational determinant. Two compatible repairs therefore invalidate an interpretation of the first rank defect as an unpaid geometric bridge. This low-m example is already in classical territory.

For q=1 the transposed matrix is evaluation of bivariate polynomials of total degree<m on the exponent set. Two elementary sufficient certificates were used. For injectivity of this polynomial evaluation, successively choose lines containing at least m,m-1,...,1 remaining points. Bezout forces a degree<m polynomial vanishing on the set to contain all m distinct lines, so it is zero. For surjectivity, choose successive lines with at most m,m-1,... remaining points and exhaust the set. Newton correction on the ith line uses the product of the previous line equations times a univariate polynomial; its degree is at most m-1 and it preserves previous values. These certify maximal rank on the appropriate side of the rectangular matrix. Neither greedy failure nor the fixed list of twelve line directions proves rank deficiency.

For ten points, 43<=m<=150, all eighteen integer triples in strip (1) received such certificates among 49 Delta choices. The saved lines are independently checkable with rational arithmetic. This finite computation is not an induction, a nominated multiplicity extension, or evidence of substantial contribution.

To expose the missing unbounded step concretely, put x=2d+3,y=2m+1. The zero-expected-dimension condition is x^2-10y^2=-9. Multiplication by 19+6sqrt(10) preserves this equation and odd positive coordinates. Starting from (x,y)=(41,13) gives (d,m)=(19,6),(778,246),(29599,9360),... . These pairs lie in (1): x<sqrt(10)y gives d-m sqrt(10)<(sqrt(10)-3)/2, while positivity follows from x-sqrt(10)y=-9/(x+sqrt(10)y). For the displayed start and all successors the resulting difference is positive. The ratios tend to sqrt(10), eventually below 174/55. This is only an illustrative infinite test sequence inside the working question, not an assertion that the sequence is unknown in the literature. At (778,246), the greedy twelve-direction test failed for Delta=4/25,1/100,49/100 after 27,27,34 lines respectively. Other parameter choices, non-greedy choices, general cuts, higher-order theta terms and geometric degenerations were not excluded.

## What is actually still unpaid here

There is no proof in this packet that produces maximal rank for all remaining nonsquare triples at unbounded m, after the known theorem regions and the compatible operations above. In this route, a sufficient missing step is a uniform construction of maximal minors, allowing the multiplier, Delta, uncollided points, cuts and differential/geometric degenerations to vary with the triple. Failure of this particular sufficient interface would not refute SHGH: nonzero higher-order terms can restore rank even when every chosen leading diagram is deficient. The original all-r,d,m question is unchanged.

The higher-dimensional and positive-characteristic companions' exact graded filling and interpolation mechanisms were also read at their operative saturation/interpolation endpoints. Their fixed compact-interior and sufficiently-large-degree conclusions already pay asymptotic jet generation. No assertion is made that the unread companion bodies or other classical compositions cannot give more. This round supplies neither an all-degree boundary argument nor a new substantial theorem. No freeze was made; no correctness, contribution, acceptance or count is assigned.
