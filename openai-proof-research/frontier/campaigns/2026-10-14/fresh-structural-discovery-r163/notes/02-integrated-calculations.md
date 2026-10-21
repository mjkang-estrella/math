# Prefreeze calculations: a paid channel transfer, not a nominee

These are feasibility calculations after reading all operative pinned source sections, DOS Appendix A, and the relevant original trace-history passages. They do not freeze a theorem, assign a contribution grade, or replace the unchanged heterogeneous/Markov targets. No new mathematical obstruction is inferred from failure to identify a substantial operation.

## Channel and exact classical map

Use n known input signs x_i in {-1,+1}, n>=2. Independently for every input position and every observation, emit G_i fair independent signs, with P(G_i=g)=(1-s)s^g for integer g>=0; then retain the original sign with probability p>0 and, if retained, independently flip it with probability e<1/2. Assume known rational 0<=s<1,0<p<=1,0<=e<1/2. Put a=1-2e>0, q=1-p. No inserted sign is a copy of an input sign, and every source position emits at most one informative sign. These precise hypotheses matter.

DOS 1612.03148v1, Appendix A.1–A.3 (author PDF internally dated December12,2016), supplies this channel and the first-moment map

    G(u)=(1-s)/(1-su),   g(u)=G(u)(q+pu),   h(u)=pa G(u),
    r=(p+qs)/(1+s),      v(w)=(w+s)/(1+sw).

Direct multiplication gives g(v(w))=1-r+rw and h(v(w))=pa(1+sw)/(1+s). Thus

    r/h(v(w))=c/(1+sw),  c=(p+qs)/(pa).

The disk map is already classical, including its improved effective retention when insertions are present at low p. It is not discovered here.

## Full tuple identity, retaining the trailing length

For k>=1 and complex variables u_0,...,u_k, let A_k(u) be the expectation of the sum over 1<=l_1<...<l_k<=L of

    product_j Y_(l_j) · u_0^(l_1-1)
      · product_(j=1,...,k-1) u_j^(l_(j+1)-l_j-1) · u_k^(L-l_k).

Here L is the entire observed length. Define the finite input polynomial

    S_k(z)=sum_(1<=i_1<...<i_k<=n) product_j x_(i_j)
           · z_0^(i_1-1) · product_(j=1,...,k-1) z_j^(i_(j+1)-i_j-1)
           · z_k^(n-i_k).

The identity is

    A_k(u)=[product_(j=0,...,k-1) h(u_j)] S_k(g(u_0),...,g(u_k)).       (1)

To derive it, condition on all block lengths and all retain/delete decisions. If a selected output is an inserted fair sign, integrating that sign kills the summand. Nonzero terms therefore select exactly k retained original signs at distinct input positions. Each selected sign contributes pa and its preceding insertion run contributes G evaluated at the corresponding preceding-gap variable. Each unselected input block contributes g in its gap, and every block after the last selected source contributes g(u_k). The ordering makes these disjoint factors; there is no product of expectations from different traces and no unobserved original-position thinning. Absolute convergence on the closed polydisk follows from E binom(L,k)<infinity. Formula (1) therefore holds there by continuity and in its interior analytically.

Let B_k(w) be the same joint rank/total-length generating polynomial under the ordinary deletion channel with retention r and no flips/insertions. Its exact identity is r^k S_k(1-r+rw_0,...,1-r+rw_k). Consequently

    B_k(w)=c^k product_(j<k)(1+sw_j)^(-1)
                 A_k(v(w_0),...,v(w_k)).                           (2)

This is an identity of polynomials on the left and an analytic composition on the right, for every deterministic input x. All transforms are linear in input sign monomials, so the same identity extends to any truncated moment functional of adequate degree; positivity is not being inferred for the signed estimator itself.

The trailing variable is essential. For a desired bit rank set I, letting m=max I, a subset J of I in the expansion of product_(i in I)(1+Y_i)/2 still requires the event L>=m, even if max J<m. Merely using ordinary sign moments of J drops this event and is wrong. This was caught during the calculation before any candidate statement or freeze.

For J nonempty of size k, fixed virtual total length t>=m, the desired signed quantity is the coefficient of B_k at preceding gaps from J and trailing exponent t-max J. Sum over t=m,...,n, and then over J subset I with factor 2^(-|I|). The J=empty term is P(Bin(n,r)>=m), known exactly. This recovers exactly the source's ordinary bit moment T_I at retention r, with the correct missing-rank convention.

## Stable finite coefficient transform

For integers g,d>=0 define

    C_(g,d)=[w^g] (w+s)^d/(1+sw)^(d+1),
    E_(g,d)=[w^g] ((w+s)/(1+sw))^d.

On |w|=1, |v(w)|=1, so Cauchy's integral gives

    |C_(g,d)|<=1/(1-s),  |E_(g,d)|<=1.                              (3)

No exponential-in-d inverse cost is incurred. For rational s these are rational numbers with explicit finite binomial formulas. For C,

    sum_(j=0,...,min(d,g)) binom(d,j) s^(d-j)
           (-s)^(g-j) binom(d+g-j,g-j).

For E and d>0 replace the last binomial by binom(d+g-j-1,g-j); E_(g,0)=1_(g=0). Exact summation may exhibit cancellation, but bit length remains polynomial in d+g and the encoding length of s. At s=0 both transforms are the identity.

Given a record of length l, the coefficient estimator in (2) sums its ordered k-subsets, using C for its k preceding gaps and E for its trailing gap, multiplying by c^k and the selected output signs. By (3) its absolute value is at most

    A^k binom(l,k),  A=c/(1-s) >=1.                                (4)

For a bit moment of order <=D, all J-subsets and the <=n+1 virtual lengths give the common envelope

    H(l)=(n+1) A^D (1+l)^D.                                       (5)

The factor 2^(-|I|) cancels the number of subsets, so no uncontrolled extra 2^D is necessary. The empty-subset deterministic term is bounded by the same envelope. This is the strongest compatible low-order transfer explored here; it neither estimates the entire trace law nor couples M traces at an exponentially precise per-trace TV tolerance.

## Tail, concentration and bounded computation entrance

A concrete coarse tail calculation pays the unbounded geometric lengths. Set t0=(1-s)/4. Since e^(t0)<=1/(1-t0) and 1-s e^(t0)>=(1-s-t0)/(1-t0), E exp(t0 G)<4/3. Hence E exp(t0 L)<=2^n, using L<=n+sum_i G_i. For integer D>=1,

    (1+l)^D <= e^(t0(1+l)/2) (2D/t0)^D.

Therefore truncating the coefficient estimator to zero on L>N has bias at most

    (n+1) A^D (2D/t0)^D exp(t0/2) 2^n exp(-t0 N/2).                (6)

Choose N to make (6)<=zeta/64, where zeta is the source dyadic feasibility tolerance at effective retention r, and also ensure M·2^n exp(-t0 N)<=1/64. To avoid circular dependence through M, define for example

    W=n+log(64/zeta)+D log(2+A+D+1/t0)+1,
    N=ceil(K W^2/t0^2),
    H=(n+1)A^D(1+N)^D,
    R=sum_(j=1,...,min(D,n)) binom(n,j),
    M=ceil(K H^2 zeta^(-2) log(64(R+1)))

with a sufficiently large absolute K. The quadratic W allowance dominates both the tail numerator in (6) and log M: log N=O(log K+log W+log(1/t0)), D<=W, log(1/t0)<=W, and all products are O(W²). This is a deliberately coarse prefreeze resource calculation, not an optimized constant claim. Chebyshev with an additional R factor would also suffice and keeps the same quasipolynomial scale; bounded-variable concentration gives the displayed form. Independent truncated observations are bounded by H. Simultaneously estimate all R source moments to error zeta/32, add bias <=zeta/64 and dyadic rounding <=zeta/64, leaving <zeta/8. The source's *unchanged* correct-prefix slack and wrong-prefix separation now apply.

For a true sequential stream, do not pretend arbitrary unbounded records can always be fully read in bounded time. Read at most N+1 bits of each requested record. If a record exceeds N, terminate the whole computation immediately with a fixed default n-bit answer; no search for its ending delimiter is needed. On the event all M genuine lengths are <=N, these empirical statistics coincide with those in the bounded analysis. The union loss is at most1/64. Every run halts after at most M(N+1) received bits plus the deterministic rational computation; the statistical event and the source feasibility slack yield the success margin. The whole sample/estimator/feasibility process uses rational operations with capped loops. Enumeration costs (N+1)^(O(D))(n+1)^(O(D)) and polynomial bit lengths, which are bounded by a fixed polynomial in the deliberately enlarged resource budget.

For fixed rational p>0,s<1,e<1/2, effective r is fixed, D=O(log²n), log(1/zeta)=O(log³n(1+log log n)^6), N is polynomial in n and that exponent, and log H=O(log³n). Thus the calculation reaches quasipolynomial resources without a new separation theorem. For parameter-varying claims one must retain A,t0,D,zeta,N,M explicitly; no parameter-uniform simplified optimum is asserted. This calculation does not extend to arbitrary insertion laws or dependent deletion masks, and does not claim such a larger theorem.

## What this does and does not establish for discovery

The paid operation is a tensorized classical Möbius coefficient transform with one tail-length bookkeeping variable, elementary Cauchy coefficient bounds, geometric tail truncation, concentration, and the stipulated rational moment decoder. It avoids an artificial unpaid insertion-separation gap. It is an independent-channel transfer of exactly the type that the brief says is not by itself a substantial finding. No correctness/contribution gate is assigned here. No full author-proof nominee is frozen on this basis.

The same calculations do not supply the unchanged H152 arbitrary heterogeneous separation or i128 stationary Markov separation. They are not offered as a weaker replacement. No new counterexample, impossibility, worldwide-priority, or exhaustion claim is made. The unpaid discovery requirement is an identifiable substantial operation beyond these compatible existing ingredients; it is not a named open bridge relabeled as a result.

## Stronger compatible primary operation, read late and integrated

After the preceding geometric calculation, read Cheraghchi–Downs–Ribeiro–Veliche, arXiv:2102.09490v2, complete model and Theorem1 proof in §§1.3–4, including the local analytic inverse Lemma6 and its proof. This is a late primary read relative to the feasibility calculation, not a claim that it preceded it. Its arbitrary oblivious synchronization model and mean-based conclusions are much broader than the present channel calculation. It does not itself state a higher-moment efficient quasipolynomial theorem. Its local inverse operation nevertheless strengthens the transfer just calculated.

Here is the compatible operation, rather than an assertion that the Möbius case is the limit. If a fixed output-length pgf g is analytic around1 with g(1)=1 and g'(1)=mu>0, its local inverse f satisfies f(1+h)=1+h/mu+O(|h|²). There is a finite constant C such that

    |f(1+h)|² <= 1+2 Re(h)/mu+C|h|²

throughout a sufficiently small neighborhood. For |w|<=1 and h=r(w-1), |h|²<=-2r Re h. Choose a sufficiently small fixed positive rational r with 2r inside this neighborhood and Cr<=1/mu. Then f(1-r+rw) lies in the closed unit disk. Thus a small tangent disk has a bounded analytic inverse image. A local inverse near1 is enough; global univalence of the original pgf is unnecessary. All constants depend on the fixed channel here.

For a fixed channel that emits independent fair filler signs and at most one informative sign per input, allow the informative sign to have arbitrary random preceding and following filler counts. Let

    h(u,v)=E[ B S u^G_before v^G_after ],

where B indicates that an informative sign exists, and S is its +/- multiplier relative to the input sign; conditional on all these variables, filler signs are independent and fair. The length law is independent of the input. Assume a fixed bounded block length, rational finite block-structure probabilities, and h(1,1)!=0. The complete marked tuple identity becomes

    A_k(u)=product_(j=1,...,k) h(u_(j-1),u_j)
                 S_k(g(u_0),...,g(u_k)).                           (7)

It is proved by the same conditional zero-mean calculation; several selected informative signs cannot come from one source block. Shrink the rational r further so |h(f(1-r+rw),f(1-r+rz))|>=|h(1,1)|/2 for all |w|,|z|<=1. Substitute these inverse maps into (7) and divide the h factors to get the ordinary-r deletion generating polynomial. On the closed (k+1)-polydisk every single observed tuple's transformed analytic function has modulus at most (2r/|h(1,1)|)^k. Multivariate Cauchy therefore bounds every coefficient by that number. With block length <=K fixed, observed length <=Kn deterministically, so the same tuple enumeration and full trailing-length reconstruction cost exp(O(D log n)), with channel-dependent constants and D=O(log²n). There is no geometric-tail issue in this bounded case.

The finite rational channel has a polynomial pgf of fixed degree. The inverse branch at 1-r is an isolated simple real algebraic root, separated from other roots after the disk choice. Bisection on a fixed isolating rational interval and the implicit power-series coefficient recursion compute its Taylor coefficients to any requested precision in polynomial time in that precision and degree bound. Products, reciprocal series with the fixed nonzero lower bound on h, and truncation to degree <=n per variable give the needed coefficients to precision exp(-polylog n) with exp(polylog n) work; error tolerance is divided by the explicit number of terms. One need not claim rationality of the exact inverse coefficients. Fixed constants and root-isolating intervals may be built into the fixed-channel algorithm. This is not a uniform algorithm over unspecified distribution oracles, unbounded encodings, or growing block support.

This stronger, still routine, analytic tensor transfer removes the temptation to describe non-Möbius inversion itself as an unpaid operation. It does not assert anything for multiple correlated informative copies in one block, zero h(1,1), unknown channels, or dependent deletions. Those are outside this calculation; no new target with those obligations is parked or nominated. The discovery outcome remains no identified substantial operation beyond compatible primary/source composition.
