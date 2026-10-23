# Completed Source329 reductions; no candidate frozen

These are research derivations, not a manuscript, acceptance decision, or contribution grade. All Source329 statements and operative proofs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The purpose is to carry the strongest compatible elementary construction far enough to identify what, if anything, is left to contribute. The quantitative statements below are complete deductions; their having proofs does not establish substantial status.

## 1. Conventions and source interfaces

All real bodies live in an explicitly specified finite-dimensional real coordinate space with its standard pairing. A convex body is compact, convex, origin symmetric, and has nonempty interior. Its polar is defined by the inequalities `<x,y> <= 1`. All covers use closed translates and arbitrary ambient centers. Every logarithm in this note is natural.

Source329, `build/sections/02-matrix-contract.tex`, Lemma `lem:matrix-to-bodies`, gives the following exact operation. Let a finite real matrix have rows R_x in R^Y, with pairwise sup distance at least 1. If the absolute convex hull of its columns, viewed as functions on X, admits a uniform epsilon-approximation list of size M, then

    K = 3 absconv{R_x : x in X} + t B_infinity^Y,    L = B_infinity^Y

satisfy

    N(K,L) >= |X|,
    N(L^polar,(6 epsilon+2t) K^polar) <= M.                       (1)

The list centers can be outside the column hull. The source clusters coefficient vectors and chooses an actual representative in B_1^Y in each cluster. This doubles the approximation error and bounds the added cube contribution by 2t. This operation is retained in full, including the factor 6 and arbitrary-center convention. It gives genuine full-dimensional bodies even if the real matrix has a kernel or deficient rank. We never replace |Y| by matrix rank.

For partitions L_i of X, indexed by i in [u], the source graph for T joins points in the same L_i-fiber for some i in T. Source `prop:compression` uses sets T missing at most theta*u indices, cutoff h with log(3)/log(h+1) <= theta, and s=ceil(1/theta). Its profiles are

    phi_h(d) = max(0,1-log(1+d)/log(1+h)),    phi_h(infinity)=0,

and its columns are g_(v,T)(x)=phi_h(d_T(x,v)). The positive column hull has approximation error 3theta with

    log Q <= hs log q + log u
             + hs 2^u log(1+s2^u/theta).                       (2)

Signed splitting gives error 6theta and list size at most Q^2. The source already proves the failure of every universal pair of constants, an entropy ratio tending to zero, and separation from convexified packing. Those conclusions are not proposed again here.

The field construction uses

    X=Sym^h((F_p^r)^*),   D_j=binom(r+j-1,j),
    D=D_h,               d=D_(h-1),
    u=ceil(2hD/theta),    p>max(h,h^2 u^(2h)).

Source `prop:robust-directions` supplies simultaneous robust nonvanishing for every nonzero symmetric form, with bad-event probability at most `(h^2 u^(2h)/p)^D < 1`. Source `prop:separated-rows` then gives |X|=p^D, at most p^d labels per partition, pairwise row distance exactly 1, and real dimension

    n = |Y| = p^D * |mathcal T|,     1 <= |mathcal T| <= 2^u.     (3)

All direction choices, the simultaneous union bound, repeated-index handling, graph-path contradiction, and body realization belong to the source.

## 2. Two classical operations that must be credited

### Affine zero patterns

Let V affine linear equations be given on a d-dimensional vector space over any field. The number of realized zero/nonzero patterns is at most

    R(V,d) = sum_(j=0)^d binom(V,j) <= (V+1)^d                  (4)

for d>=1; for d=0 it is at most 1. Terms with j>V are zero. This is the linear case of Ronyai--Babai--Ganapathy, *On the number of zero-patterns of a sequence of polynomials*, Theorem 1.2, with its proof in Section 5. Their actual minimal-basis proof was read, not just a theorem citation.

Here is the precise affine version used. At a point z take all equations vanishing at z. Their common zero set is nonempty. Select a basis of their linear parts, of size at most d. Since all selected and unselected equations vanish at the same z, the corresponding affine equations have exactly the same common solution set as the full vanishing set. An equation from the original list vanishes at z if and only if it vanishes identically on this affine solution set: the forward implication is construction, and the backward implication holds because z is in the solution set. Thus a selected subset of at most d equations determines the pattern. Choose the lexicographically first basis to make the assignment injective. Consistency is essential: no basis for an empty affine solution set is being counted. Identically zero equations and repeated equations cause no difficulty. The last bound in (4) follows by encoding a subset of size at most d as a sorted d-tuple padded with a zero symbol. If V=0 the count is one.

### Empirical approximation on finitely many coordinate patterns

Let A be a finite family of {0,1}-valued functions on a finite domain, including the zero function. Suppose the evaluation vectors `(a(x))_(a in A)` have at most R distinct values. For any convex combination F of A and eta>0, set

    m = ceil(log(4R)/(2 eta^2)).

There is an average of m members of A whose uniform distance to F is at most eta. Indeed sample m independent atoms from the combination. At each distinct evaluation vector the samples are Bernoulli with the appropriate expectation. For one Bernoulli variable B, the logarithm of E exp(t(B-EB)) has value and first derivative zero at 0 and second derivative at most 1/4: under exponential tilting it is a Bernoulli variance. Integrating twice gives a bound t^2/8 for either sign of t. Markov's inequality with t=4eta gives, for the sample mean,

    P(|sample mean-F(x)|>eta) <= 2 exp(-2m eta^2).

The union bound over R patterns is at most 1/2. In particular an appropriate sample exists. The list of *all* ordered m-tuples of atoms works for every convex combination and has cardinality at most |A|^m. One common random sample is not required to work for every combination; the deterministic enumerated list does.

This is the classical empirical/Maurey method with a finite-coordinate concentration bound. Hu--Peale--Reingold (PMLR 167, 2022), Lemma 9 and its full proof, explicitly uses this concentration-plus-union-bound operation. Their Theorem 11, including its proof through Lemmas 8--10, was read. Mendelson (JMLR 2, 2001), Section 2.1, provides relevant L2 convex-hull context; its Lemma 2.2 is an assertion there, not a printed proof of Maurey's lemma. No new sampling principle is claimed here, and an L2 estimate is not silently used as a uniform estimate.

## 3. Graph balls for linear partitions

Let X be a D-dimensional vector space over F_p and let every partition map L_i be linear. Write H_i=ker L_i. A walk of length at most ell in the T-graph is exactly a decomposition of its displacement as a sum of at most ell vectors, each in some H_i with i in T. Consequently

    {z : d_T(z,0)<=ell}
       = union_(S subset T, |S|<=ell) H_S,
    H_S = sum_(i in S) H_i,       H_empty={0}.                 (5)

For the reverse inclusion, order the summands in a decomposition and form the successive partial sums. Zero increments can be omitted. For the forward inclusion, sum the increments of a path. Repeated uses of one H_i can be combined because it is a linear subspace. This proves (5) in disconnected graphs too; no finite-distance assumption for all pairs is needed.

For fixed source pivots z'_(j,k), the original source indicators `d_T(x,z'_(j,k))<=2j+1` therefore are Boolean combinations of affine linear equations. Choose an annihilator basis of H_S for each S with |S|<=2h-1, and translate those equations by each of the hs pivots. At most

    V_0 = hs D sum_(ell=0)^min(2h-1,u) binom(u,ell)

equations suffice. Formula (4) bounds all coordinate patterns by `(V_0+1)^D`, independently of p. Apply the empirical approximation of Section 2 to the source's unrounded grouped pivot combination. Its coefficient mass is at most one, since for each j the grouped weights sum to at most one and the gamma_j sum to one. Add the zero atom for any deficit.

This is already a complete compatible composition of the source and classical operations. It replaces the exponential-in-u rounding cost of (2) by

    log u + m_0 log(1+hs 2^u),
    m_0=ceil([log4+D log(V_0+1)]/(2theta^2)).                  (6)

The source's interval f-2theta<=F<=f+theta becomes f-3theta<=A<=f+2theta after sampling. The uniform error remains 3theta, so the source signed and body steps remain unchanged. It is incorrect to present merely obtaining a field-size-independent cost as an unpaid operation after this reduction.

## 4. Common-kernel saturation sharpens that composition

There is a sharper version that uses the common index already selected by the source. Assume rank L_i <= d for all i, where d>=1, and |L_i(X)|<=q. Use the same index i_0, assigned pivot sets U_j, grouped weights w_(j,k,T), and fixed label representatives as in `prop:compression`. Retained T all contain i_0.

Replace the source's radius-(2j+1) indicator by

    b_(j,k,T)(x) = 1{ x-z'_(j,k) is in H_(i_0)+H_S
                     for some S subset T with |S|<=2j }.      (7)

This is a saturation by the common kernel, not a quotient of the final real convex bodies. Both error directions can be proved on the original graph.

* If column (v,T) is assigned to pivot z_(j,k), then d_T(v,z_(j,k))<=j and z_(j,k)-z'_(j,k) is in H_(i_0). If also d_T(x,v)<=j, their two paths have at most 2j increments. Thus (7) holds. All assigned matches are retained.
* If (7) holds, there is a path from x to z'_(j,k) of at most 2j+1 edges. Since d_T(z'_(j,k),v)<=j+1, one gets d_T(x,v)<=3j+2. Thus the exact same logarithmic-profile dilation bound from `lem:log-profile` applies.

The omitted mass is at most theta, and the unassigned residual mass at each level is at most theta. Therefore the saturated unrounded combination F still satisfies

    f-2theta <= F <= f+theta.                                (8)

Every indicator (7) factors through X/H_(i_0), of dimension rank L_(i_0)<=d. In that quotient, take an annihilator basis for the image of H_S, for every S subset [u] with |S|<=2h-2. Its size is at most d. For the hs pivot slots, the resulting affine equations determine every indicator, regardless of T. Put

    S_* = sum_(ell=0)^min(2h-2,u) binom(u,ell),
    V   = hs d S_*,
    R   = (V+1)^d,
    m_* = ceil([log4+d log(V+1)]/(2theta^2)),
    B   = log u + m_* log(1+hs 2^u).                          (9)

If the actual quotient has dimension zero, its one pattern is still bounded by R. This covers zero contraction directions without adding a nonzero-direction assumption. Different common indices and different pivot labels may give different quotient equations, but the uniform numerical bound R is the same. The equations and representatives are shared data defining the list, not extra choices charged to each approximant.

For each fixed common index and list of hs labels, enumerate all m_*-tuples from the at most `1+hs|mathcal T|` indicators and zero. Section 2 gives probability at least 1/2 of approximating any specified F within theta. There are at most u q^(hs) choices of the common index and labels. Hence one deterministic finite list has size Q with

    log Q <= hs log q + B                                    (10)

and approximates the entire positive column hull uniformly within 3theta. Signed splitting gives error 6theta and at most Q^2 centers, exactly as in the source. Sampling does not have to hold simultaneously over all coefficients for a single draw; enumeration is what gives a simultaneous list. Row separation, row count, full-dimensionality, and the source support-function calculation are all preserved.

The saturation step is a genuine modification of the intermediate indicators, and simply asserting that ordinary graph balls descend to X/H_(i_0) would be false. The forward and backward implications above are the compatibility proof. Nevertheless, the operation is elementary and uses the source's entire pivot/common-index machinery. It must be compared with that machinery and the two classical operations, not advertised as independent construction of the counterexamples.

## 5. Exact controlled dimension for the completed reduction

Fix real a,b>=1. Define, in this order,

    theta=1/(1000a),             s=ceil(1/theta),
    h=ceil(3^(1/theta)),
    r=ceil(16b h^2 s)+1,
    D=binom(r+h-1,h),            d=binom(r+h-2,h-1),
    u=ceil(2hD/theta).

Define S_*, V, m_*, B by (9). All these numbers are independent of the field prime. Set

    P=max{2,h,h^2 u^(2h),exp(16bB/D)},
    J=ceil(P).

By the classical Bertrand postulate choose a prime J<p<2J; in particular p>P and p<=4P. We use that standard prime-existence theorem as a classical dependency, not as a claim about the algorithmic cost of finding p. No numerical search is used to establish existence.

Use the source robust directions, the source partitions and row profiles, and the saturated compression of Section 4. The source direction event has strictly positive probability, so choose one realization for which *all* nonzero forms meet the required condition. Conditional on this fixed realization, the finite-list argument in Section 4 is deterministic and covers *all* coefficient vectors. There is no interchange of those quantifiers or invented independence.

With K=3 absconv rows + theta L and L=B_infinity^Y, (1) gives

    N(K,L)>=p^D,
    N(L^polar,38theta K^polar)<=Q^2.

Since 38theta<a^(-1), monotonicity of covering in the second argument gives the same upper bound at a^(-1)K^polar. Moreover,

    log(Q^2)/(D log p)
       <= 2hs d/D + 2B/(D log p)
        = 2h^2 s/(r+h-1) + 2B/(D log p)
        < 1/(8b)+1/(8b) = 1/(4b).                            (11)

Thus the source's strict counterexample inequality holds with ample margin. The constructed objects satisfy

    theta L subset K subset (3+theta)L,
    n=p^D |mathcal T|,
    0 < log N(K,L),
    log N(L^polar,a^(-1)K^polar)/log N(K,L) < 1/(4b).           (12)

The first containment and the constants are source consequences, not additional geometric constraints newly paid for here.

An exact dimension upper bound is

    log n <= F(a,b)
           := D(log4+2log h+2h log u) + 16bB + u log2.         (13)

Indeed log n<=D log p+u log2. Since h^2 u^(2h)>=max(2,h) for the chosen parameters and max(x,y)<=x+y for nonnegative x,y,

    log p <= log4+2log h+2h log u+16bB/D.

This proves (13) without suppressing any p-dependent quantity. The ambient is the real coordinate space R^Y, with positive integer dimension n; all finite-field vector spaces are only index/encoding spaces.

For clarity, the implied-constant consequence is also proved. With a fixed, h,s,theta are fixed. For b>=1 there are constants depending only on a for which

    r <= c_a b,       D <= c_a b^h,      d <= c_a b^(h-1),
    u <= c_a b^h,     log(V+1) <= c_a log(2+b).

For example, bound each factor in the product formula for the binomial coefficients by r+h and use r<=c_a b. The sum S_* is bounded by (u+1)^(2h-2), by the padded-tuple encoding used in (4). Therefore

    m_* <= c_a b^(h-1) log(2+b),
    log(1+hs 2^u) <= log(1+hs)+u log2 <= c_a b^h,
    B <= c_a b^(2h-1) log(2+b).

Substitution into (13) proves the complete consequence

    n <= exp(C_a b^(2h) log(2+b)),   h=ceil(3^(1000a)).          (14)

Here C_a is finite and independent of b, n, and p; (13) supplies an explicit replacement whenever a named constant is undesirable. No dimension-free norm-equivalence claim appears.

For comparison, the *unsaturated* direct classical composition (6) uses D in place of d in the sample count and proves the weaker exponent 2h+1 in (14). The source's own rounding term (2) instead contains 2^u, with u on the order of b^h for this parameter choice, leading to a doubly exponential upper schedule. The improvement in (14) is therefore not obtained just by writing down the source's unspecified large prime. It comes from replacing its encoding, with the strongest classical and source components explicitly credited.

## 6. Higher contractions: carry the compatible source shortcut too

A tempting further improvement is to replace contraction by one direction with contraction by k directions. It is important to carry this route rather than call it an unpaid operation.

Fix k>=1 and a positive integer H with log3/log(H+1)<=theta. Put h=kH and delta=theta/k. For the source robust-direction proposition use degree h, deletion fraction delta, dimension r, D=D_h, and

    u=ceil(2hD/delta),   p>max{h,h^2 u^(2h)}.

Let block indices be all ordered k-tuples I=(i_1,...,i_k) in [u]^k, with repetitions allowed. For each block define a linear partition map

    L_I(x)=x(t_(i_1),...,t_(i_k), dot,...,dot)
              in Sym^(h-k)((F_p^r)^*).

Its rank is at most d_k=D_(h-k), without a surjectivity assumption. For every original admissible T set S_T=T^k. Since |T|/u>=1-delta,

    |[u]^k \ S_T|/u^k <= 1-(1-delta)^k <= k delta=theta.       (15)

The family {S_T} is fixed and nonempty. The map T -> T^k is injective (diagonal tuples recover T), so it has at most 2^u members, not necessarily 2^(u^k).

For distinct x,y use source robust directions for Z=y-x and choose T on which every ordered h-tuple evaluates nonzero. Suppose an S_T-graph path had ell<=H edges. Each displacement Delta_j is killed by the k-fold contraction attached to that edge. Concatenate the ell edge blocks and pad the resulting k*ell directions to h=kH arguments by any direction from nonempty T. By symmetry and multilinearity, every Delta_j evaluates to zero on this h-tuple, because its own contraction block occurs among the arguments. Their sum Z would also evaluate to zero, contrary to robust nonvanishing. Repetitions within blocks, across edges, or in the padding are explicitly allowed by the source. Thus the graph distance exceeds H and the source profile with cutoff H separates the rows by exactly one.

Now apply the source's *general* partition compression, or its Section 4 saturation above, with number of partitions U=u^k, cutoff H, q=p^(d_k), and family size at most 2^u. This is a complete compatible construction. No independence of directions, polynomial factorization theorem, equality of kernel sums with a higher-contraction kernel, or quotient rank equality is needed.

For the saturated version set

    V_k = Hs d_k sum_(ell=0)^min(2H-2,U) binom(U,ell),
    m_k = ceil([log4+d_k log(V_k+1)]/(2theta^2)),
    B_k = k log u + m_k log(1+Hs 2^u).

The bound is

    log Q <= Hs d_k log p+B_k,
    log(Q^2)/(D log p) <= 2Hs d_k/D + 2B_k/(D log p).          (16)

The ratio of dimensions is exactly

    d_k/D = product_(j=0)^(k-1) (h-j)/(r+h-1-j) <= (h/r)^k.   (17)

The inequality uses r+h-1-j>=r, valid as k<=h, and h-j<=h. For example choose r>h(16bHs)^(1/k), and then choose log p>16bB_k/D as well as the source field threshold. Equations (1), (15)--(17) give the same strict entropy separation. The real dimension remains p^D times the number of original T's; duplicate block labels and repeated direction tuples do not invalidate any count.

This produces an r^(-k) ratio for fixed h,k as r grows, but that alone is not a stronger ambient-dimension theorem. For fixed a,H,k and b growing, the stated choices give

    r=O_(a,k)(b^(1/k)),   D=O_(a,k)(b^H),
    d_k=O_(a,k)(b^(H-1)), u=O_(a,k)(b^H),
    B_k=O_(a,k)(b^(2H-1) log(2+b)).

The calculation uses log U=k log u, so log(V_k+1)=O_(a,k)(log(2+b)). Bertrand's postulate applied after these choices again gives

    log n=O_(a,k)(b^(2H) log(2+b)).                            (18)

Thus the faster ratio in the auxiliary rank parameter does not improve the proved exponent 2H in ambient dimension. The code must still describe an original T for each sampled indicator. This is an explicit calculation of the strongest compatible block route considered here, not a claim that no better construction exists.

## 7. Comparison and the remaining research obligation

The strongest completed reduction is (13)--(14), together with the higher-contraction route (15)--(18). Its ingredients are:

1. The source's simultaneous finite-field nonvanishing, graph separation, logarithmic profile, common-index pivot compression, signed splitting, and full-dimensional body realization.
2. Classical affine zero-pattern counting and empirical approximation.
3. The explicit kernel-sum description (5), the saturation compatibility (7)--(8), and the complete coding/dimension accounting.

Items 2 are fully available primary operations, and item 3 is a short adaptation to the source's linear partitions. The author has not identified a further operation whose nonroutine substantial character survives this strongest composition. The derived bounds are retained, but this note does not certify them as substantial or freeze them as a nominee. This is not a mathematical claim that their contribution has been independently graded technical.

A concrete next obstacle is visible in (9): after reducing the number of coordinate patterns, each sampled indicator still records a whole T. Its logarithmic cost is at most u log2. The complete current argument gives `B` of order `d*u*log u` for fixed a, and choosing the field to absorb it yields the `b^(2h)` dimension schedule. A materially sharper construction would need a proved smaller dictionary or different encoding for these T-dependent indicators, *while keeping every pair of rows separated and uniformly approximating every signed column combination*. A per-vector or per-row dictionary, an empirical sample good only for one coefficient vector without a fixed enumerated list, or a guessed bound on the number of relevant T's would not discharge that obligation. No statement asserting such a dictionary is frozen or claimed here.

The higher-contraction route has been completed rather than left as a named gap; (18) shows what it actually yields. Likewise direct sums, polarity, smoothing, operator reformulation, and the source convexified-packing corollary would supply no unpaid operation for this round. No infinite-dimensional operator result, optimized exponent, efficient sampler, worldwide novelty, or exhaustive-history assertion is made.
