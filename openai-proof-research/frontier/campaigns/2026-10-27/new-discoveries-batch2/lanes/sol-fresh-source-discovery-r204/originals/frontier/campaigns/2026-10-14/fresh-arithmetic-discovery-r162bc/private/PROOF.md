# Author proof for the unchanged frozen r162bc statement

Status: complete author argument, submitted for independent adversarial correctness and separate actual-primary contribution review. This document assigns neither gate nor grade. The frozen statement is `STATEMENT.md`, SHA256 `ffb70a869024e8ebf88964edb0a41575d2d3922976579e93dd593a2d4ed3f528`. Its field-independent threshold and full shared-gate model are retained. All constants denoted C below are absolute positive real numbers and may increase from one occurrence to another. Every use of “eventually” means for every integer n beyond one absolute threshold. There are finitely many such requirements, so they can be imposed simultaneously.

## 1. Parameters and the rank map

Put t=floor(n^(1/4)). Work throughout with n sufficiently large that t>=16. Define

    sigma = 1 - 1/t + 1/t^3,
    lambda_* = sigma/(1+sigma),
    k = floor(n lambda_*), m=n-k, lambda=k/n, rho=k/m,
    s=m-k, v=k n^2, u=m n^2,
    a=ceil(v/(t-1)), alpha=a/(a+v),
    b=ceil(u alpha^rho/(1-alpha^rho)), beta=b/(b+u),
    q=alpha^((1+rho)/2).

The variables of k whole matrix layers form V; those of the other m layers form U. Every one of the n^2 entries of each layer is retained, whether or not it occurs in the endpoint entry of IMM. Thus |V|=v and |U|=u. The order of the layer types is specified in Section 5.

For r>=1 and d>=0 write h(r,d)=binom(r+d-1,d), and let H_E(d) be the space of homogeneous degree-d polynomials in the variables E. Define

    D=h(v,a)h(u,b),
    F_g = g_[k,m](partial_V,U): H_V(a) tensor H_U(b)
                              -> H_V(a-k) tensor H_U(b+m),
    R(g)=rank(F_g).

Here g_[k,m] is the indicated bidegree component of a homogeneous polynomial g of total degree n. Substitution by differentiation in V and multiplication in U gives commuting operators; this fact is used only after taking the separate bidegrees of factors. Rank is subadditive in g. This is the actual Source135 rank map, Section 2, equation `eq:rank-map`, with new parameters; the following estimates verify that its operative dimension and moment calculations still apply.

We have k,m=Theta(n), 1-rho=Theta(1/t), v,u=Theta(n^3), and a,b=Theta(n^3/t). More precisely,

    1/t <= alpha <= t^(-1) exp(C/a), alpha^(-1)<=t,
    alpha^rho <= beta <= alpha^rho exp(C/b),
    1/t <= q <= 2/t, beta<=2/t,
    a>=k, 2n<=min(a,b)/2.

To check these statements, lambda differs from lambda_* by less than 1/n, and the map x/(1-x) has bounded derivative in a fixed neighborhood of 1/2. Consequently rho=sigma+O(1/n), with rho<=sigma and 1-rho=Theta(1/t). For a_0=v/(t-1), the increasing function x/(x+v) has logarithmic derivative v/[x(x+v)]<=1/x. Since a_0<=a<a_0+1 and a_0/(a_0+v)=1/t, the first alpha bounds follow. Then

    alpha^rho=t^(-1) exp(O(log(t)/t+1/a)).

Applying the same logarithmic derivative argument to b_0=u alpha^rho/(1-alpha^rho) gives the beta bounds and b=Theta(n^3/t). Similarly

    q=t^(-1) exp(O(log(t)/t+1/a)).

As alpha<1 and (1+rho)/2<1, q>=alpha>=1/t. All remaining inequalities follow from these growth estimates. In particular

    n^2/a+n^2/b+n^2/v+n^2/u=O(t/n),
    (1-1/(a+v))^(-n)<=2.

All these conclusions and thresholds are numerical, independent of any field or circuit.

## 2. Product-rank estimate with its complete error budget

For an integer e>=1 let

    H_e = sum_{i=0}^e q^|i-lambda e|,
    d_e = dist(lambda e,Z).

For homogeneous positive-degree factors Q_1,...,Q_r of degrees e_j summing to n, over any field,

    R(product_j Q_j) <= 2D product_j H_(e_j).                 (2.1)

Here and below factors are polynomials, not circuit gates with a support restriction. In particular each may involve all variables.

Proof: expand each factor into bidegree components. In a contribution with sum i_j=k, put delta_j=i_j-lambda e_j, so sum delta_j=0. Apply first the commuting operators with positive delta_j. If their total bidegree is (I,J), their output lies in H_V(a-I) tensor H_U(b+J); I<=k<=a and J<=m. Successive binomial ratios give

    h(v,a-I)/h(v,a) <= (a/(a+v-1))^I,
    h(u,b+J)/h(u,b) <= ((b+u)/b)^J.

Since beta>=alpha^rho, the intermediate dimension divided by D is at most

    alpha^(I-rho J)(1-1/(a+v))^(-I)
      <= 2 alpha^(I-rho J).

Also I-rho J=(1+rho)sum_(delta_j>0)delta_j
              =((1+rho)/2)sum_j|delta_j|.
Thus this contribution has rank at most 2D product_j q^|delta_j|. Summing ranks and dropping the constraint sum i_j=k proves (2.1). Zero components contribute zero; the empty positive-discrepancy set causes no problem. This proves, at the new parameters, the full operation in Source135 `lem:product-rank`, rather than invoking its displayed old-parameter corollary.

For q<=1/2, enlarging the integer sum to all of Z gives

    H_e <= q^d_e(1+4q^(1-2d_e)) <=5.                         (2.2)

Indeed, after retaining one nearest integer, all other terms total at most 2q^(1-d_e)/(1-q). This covers ties as well.

We need small multiplicative error even when d_e tends to zero. Set d_0=1/(16t). For d in [d_0,1/2], logarithmic convexity of

    f(d)=q^(1-2d)/d

follows from (log f)''=1/d^2. Therefore its maximum on the interval is at an endpoint. At d_0, using q<=2/t and log(1/q)<=log t,

    f(d_0)<=32 exp(log(t)/(8t))<=64.

At 1/2 it equals 2. Consequently 4q^(1-2d)<=256d. Let L=log(1/q). Eventually L>=512, and hence (2.2) gives

    d_e>=1/(16t)  ==>  H_e<=q^(d_e/2).                    (2.3)

This possibly very large absolute threshold is allowed in the frozen statement. There is no hidden factor raised to the number of selected factors: the nearest-integer error is absorbed into each factor's own distance.

## 3. Degree bands and exact circuit decomposition

First establish three distance bounds:

    t^2/2 <= e < t^2  ==> d_e>=1/(16t),
    t/2   <= e < t    ==> d_e>=1/16,
    e=1                ==> d_e=lambda>=1/3.                (3.1)

Put sigma_0=1-1/t and lambda_0=(t-1)/(2t-1). Direct subtraction gives

    lambda_*-lambda_0 = 1/[t^3(1+sigma)(1+sigma_0)]
                     in [1/(4t^3),1/(3t^3)]

for t>=4. Since 0<=lambda_*-lambda<1/n<=1/t^4, for e in the first band the displacement h=e(lambda-lambda_0) satisfies

    1/(8t)-1/t^2 <= h <=1/(3t),

so h>=1/(16t) when t>=16. The number lambda_0 e lies on the grid of denominator 2t-1. If it is an integer, the distance of lambda e is h. Otherwise its distance to the nearest integer is at least 1/(2t-1); perturbation by h leaves distance at least 1/(2t-1)-1/(3t)>=1/(6t). This proves the first bound. In the second band,

    lambda_0 e=e/2-e/(4t-2).

For even e its distance is e/(4t-2)>=1/8 and at most t/(4t-2)<1/3. For odd e its distance is 1/2-e/(4t-2)>1/6 for t>=4. The perturbation is at most 1/(3t^2); hence both cases have distance at least 1/16 eventually. Finally lambda tends to 1/2 from below, proving the third bound.

Let S be the number of computational gates of a nonzero circuit in the frozen model computing a homogeneous degree-n polynomial. We prove that its output is a sum of at most S^3 scalar multiples of products, each having one of the following lists of distinguished factors and at most ONE additional positive-degree factor:

    A: t^2-1 factors, each of degree in [t^2/2,t^2);
    B: t-1 factors, each of degree in [t/2,t);
    C: t factors, each of degree 1.                         (3.2)

All factor degrees in a summand total n. This is a product-depth-three instance of the actual degree-band decomposition in AGKST Lemma 4.1; the direct proof here controls shared gates and the number S^3 without a conversion to a formula or a wire bound.

Discard zero contributions and absorb scalar factors into the outer scalar. Every surviving gate of positive formal degree computes a homogeneous polynomial of that degree. The output's formal degree is n, since its nonzero polynomial has degree n. Each sum has at most S distinct computational predecessors: repeated incoming occurrences can be combined by adding their edge coefficients. Thus the top sum gives at most S products of middle-sum polynomials. Positive-degree factor occurrences in each product have total degree n, and are retained with multiplicity.

If every factor in such a product has degree <t^2, repeatedly merge two factors of degrees <t^2/2 while possible. Each merger has degree <t^2. At termination all but at most one factor have degree in [t^2/2,t^2). The number r of these factors is at least t^2-1: indeed n<(r+1)t^2 unless there is no leftover, when the same strict bound still holds, whereas n>=t^4. Select t^2-1 of these factors and multiply ALL remaining factors into one polynomial. If its degree is zero absorb it into the scalar. This is case A. A merger is a polynomial grouping, not an operation charged as a new circuit or a restriction on the original circuit.

Otherwise choose one occurrence of a middle-sum factor of degree >=t^2. Expand that one sum, with at most S resulting terms. In each term it supplies a product of lower-sum factors of total degree >=t^2. If all its positive factor degrees are <t, the same merging procedure with threshold t gives at least t-1 factors of degree in [t/2,t). Select t-1, and collect every other factor, including all factors outside the selected middle sum, into one polynomial. This is case B.

Otherwise choose one occurrence of a lower-sum factor of degree >=t and expand that sum, again into at most S terms. Each resulting lower-product term is a product of bottom-sum gates. Each positive-degree bottom sum is a homogeneous linear form: its leaves have common degree one, and may be any ambient variables. Its degree-zero bottom sums are scalars. A nonzero product of total degree >=t therefore contains at least t linear occurrences. Select t and group every other factor into one polynomial, giving case C.

At most one sum is expanded at each of the three sum levels, so the total is at most S^3. Some branches stop earlier, and S>=1. A selected occurrence of a shared gate is expanded without expanding its other occurrences; all other occurrences remain in the collected polynomial. This is legitimate algebraic distributivity. Arbitrary fan-out and repeated product inputs do not change the term bound. Zero gates of positive formal degree may be discarded when their contribution vanishes but are never reassigned a smaller degree. Empty gates, unary gates, degree-zero products, coefficients and zero coefficients are covered by the stated scalar and zero handling. No count of wires or input leaves was used.

In each case the sum of the distinguished distances is at least t/32: for A it is (t^2-1)/(16t), for B it is (t-1)/16, and for C it is at least t/3. Equations (2.1)--(2.3) and the bound H_e<=5 for the single leftover factor now give, over every field,

    R(g) <=10 S^3 D q^(t/64)
         <=10 S^3 D t^(-t/128).                           (3.3)

For the last inequality q<=2/t<=t^(-1/2) eventually. If no leftover factor exists the bound only improves. The estimate is for the full seven-layer class, with no set-multilinearity or bottom-support assumption.

## 4. Full occupation and path moment identities

We now work over C only for the positive inner-product calculation. Give H_E(d) the orthonormal monomial basis z^M/sqrt(M!). A domain basis index consists of independent uniform weak compositions of a into v parts and b into u parts. Put

    A=a/v, B=b/u, mu=A^k(1+B)^m, L=n-1,
    T=tr(F_f^*F_f), T2=tr((F_f^*F_f)^2), f=IMM(n,n).

For a uniform composition M of h into r parts and nonnegative integers d_i with H=sum d_i,

    E product_i (M_i)_(d_i) = (h)_H/r^(overline H) product_i d_i!.

This follows by extracting y^h from product_i[d_i! y^(d_i)/(1-y)^(d_i+1)] and dividing by binom(h+r-1,h). For independent geometric variables of mean h/r the corresponding factorial moment is (h/r)^H product_i d_i!. Their ratio is product_(j=0)^(H-1)(1-j/h)/(1+j/r) when H<=h, and the composition moment is zero when H>h. The ratio is at most one, and when H<=H0<=h/2 it is at least exp(-H0^2/h-H0^2/(2r)), by log(1-x)>=-2x and log(1+x)<=x. These comparisons extend termwise to every polynomial having nonnegative falling-factorial coefficients. This is the complete operation of Source135 `lem:occupation-moments`. It does not assume independence of the composition coordinates.

A path P has p_0=p_n=1 and p_1,...,p_(n-1) in [n]; there are n^L paths. Write E_j(P) for its matrix-entry coordinate in layer j. Its operator changes the occupation vector by

    epsilon_P=-sum_(j in V) e_(E_j(P))+sum_(j in U) e_(E_j(P)),

and its coefficient on index M is

    c_P(M)=sqrt(product_(j in V) M_(E_j(P))
                     product_(j in U)(M_(E_j(P))+1)).

Invalid indices have coefficient zero. Each path uses a distinct coordinate in each layer; path shifts are distinct. It follows that

    T=D sum_P E[product_(j in V)M_(E_j(P))
                      product_(j in U)(M_(E_j(P))+1)]
      >=D n^L mu exp(-C t/n)>0.                            (4.1)

The lower factorial-moment comparison applies with orders at most n in each group (even order 2n is allowed by Section 1), and the total logarithmic loss is O(n^2/a+n^2/b+n^2/v+n^2/u)=O(t/n). Endpoint-inactive coordinates remain among the composition coordinates.

The second trace is exactly

    T2=D E_M sum_(P,Q,R,S: epsilon_P-epsilon_Q=epsilon_R-epsilon_S)
                c_P(M)c_Q(M')c_R(M)c_S(M'),
    M'=M+epsilon_P-epsilon_Q.                              (4.2)

The equality follows by writing and squaring each entry of F_f^*F_f; M' is determined, not independently summed. In one layer, if p,q,r,s denote the four edge coordinates, e_p-e_q=e_r-e_s has exactly these alternatives:

    N: p=q=i, r=s=j;
    D: p=r=i, q=s=j, i!=j.

All-equal belongs to N. The local four-coefficient polynomials are

    V: N gives M_i M_j,          D gives M_i(M_j+1);
    U: N gives (M_i+1)(M_j+1),  D gives (M_i+1)M_j.

These identities include zero-extended invalid-index contributions: a negative shifted coordinate in a D layer makes M_i=0 in V or M_j=0 in U, which annihilates the displayed factor; unavailable derivatives in N do likewise. Repeated N coordinates give z^2=(z)_2+(z)_1 or (z+1)^2=(z)_2+3(z)_1+1. All four local polynomials, and their products over disjoint layers, have nonnegative falling-factorial coefficients. Apply the upper composition-to-geometric comparison in both groups.

Dividing each geometric expectation by A^2 in V and (1+B)^2 in U, the local weights become

    N: 1+c_j 1_(i=j),       D: c_j,
    c_j=alpha^(-1) in V,   c_j=beta in U.                 (4.3)

For example E Z^2=2A^2+A and (A+1)/A=alpha^(-1). For U, E(Z+1)^2=2B^2+3B+1 gives 1+beta on equality. Normalization over all layers is mu^2. These identities are Source135 `eq:four-path-trace`, `eq:local-polynomials` and `eq:local-weights`, with the assumptions rechecked rather than a changed diagonal convention.

## 5. Joint collision estimate: both layer types retained

This section is the additional operation proposed for contribution review. Unlike the source's final reduction, it does not bound U-layer collision corrections pointwise by (1+beta)^m. Such a bound at the present parameters would have logarithm of order n/t, exceeding the circuit saving. Instead all equality corrections are expanded together and charged to their common path labels.

Drop the inequalities i!=j at D layers, keeping their assigned weights c_j. This enlarges a nonnegative sum; the artificial weight on a newly admitted tuple is not asserted to equal its occupation moment. Expand every N weight in (4.3), for V AND U, into an undecorated N term of weight 1 and an E term of weight c_j enforcing i=j. Thus E identifies all four path edge coordinates, while N and D impose their respective two-pair partitions.

For a word omega in {N,D,E}^n, consider an internal path vertex. It has two free labels if the adjacent layers are NN or DD. Every other ordered pair of types forces all four labels equal, leaving one free label. The reason is that N and D are distinct perfect matchings of the four paths, whose union is connected, and E already identifies all four. Equality of edge coordinates imposes these equalities at both ends; because all matrix entries exist, there is no further constraint between vertices. All external labels are fixed to 1. Consequently the count is exactly n^(2L-b(omega)), where b counts internal adjacencies other than NN and DD. Hence

    T2/(D n^(2L) mu^2) <= Z3,
    Z3=sum_omega n^(-b(omega)) product_(j:omega_j!=N)c_j.    (5.1)

This is one joint count; equality events in adjacent layers are not treated as independent.

Fold E to D, yielding a binary word y. Let w(y) be its switch count and r(y) its number of D runs. The layer weight is unchanged by folding. Within a D run of length ell, select a subset A of positions to be E. Every internal edge of the run touched by A costs an extra factor 1/n compared with y; let j(A) be their number. Every selected position other than the first position of the run has its own distinct preceding internal edge, so

    j(A)>=|A minus {first position}|.

The sum of extra factors is therefore at most

    sum_(A subset [ell]) n^(-j(A)) <=2(1+1/n)^(ell-1).

This remains valid for ell=1 and endpoint runs. Across all runs, multiplying the bounds gives at most 2^r(y)(1+1/n)^n<=e*2^r(y). The all-N word has its single preimage and obeys the same inequality; the all-D word is handled as one run, including both endpoints. We have proved the useful general folding inequality

    Z3 <= e sum_(y in {N,D}^n) 2^r(y) n^(-w(y))
                                   product_(j:y_j=D)c_j.  (5.2)

It holds for arbitrary positive layer weights c_j and width n>=2. No lost factor depending on the number of U layers occurs.

It remains to bound the binary sum for the chosen schedule. Order the variable groups as

    V U^(ell_1) V U^(ell_2) ... V U^(ell_k),
    ell_i=1+floor(i s/k)-floor((i-1)s/k).

Eventually 0<s/k<1, so each ell_i is 1 or 2, and their sum is k+s=m. For every interval I of layers put d(I)=#V(I)-rho #U(I). Then

    d(I)<=1+rho,  d([n])=0.                               (5.3)

Indeed r consecutive complete chunks starting after chunk j contain r V's and r+E U's with E=floor((j+r)s/k)-floor(js/k), |E-rs/k|<1. Their discrepancy is rho(rs/k-E)<rho. A proper initial part of a chunk has discrepancy at most 1, a proper terminal part only U's and nonpositive discrepancy. Decomposing an arbitrary interval into these parts and complete chunks proves (5.3), including an interval in a single chunk. This is the source's full interval-discrepancy operation; no prefix-only assertion is substituted.

Each D run I has weight

    product_(j in I)c_j
       =alpha^(-#V(I)) beta^(#U(I))
       <=alpha^(-d(I)) exp(C #U(I)/b)
       <=t^2 exp(C #U(I)/b).                              (5.4)

The last step uses alpha>=1/t and rho<1. Runs are disjoint, so all rounding factors total at most exp(Cn/b). In a mixed binary word let r be the number of interior D runs and e_0 the number touching one endpoint. Then e_0 in {0,1,2}, there are r+e_0 runs, and w=2r+e_0. No mixed run touches both endpoints. Initial type and switch positions determine a word, so for each r,e_0 there are at most 2 binom(n-1,2r+e_0) words. Its total contribution to the binary sum is bounded by

    2 binom(n-1,2r+e_0) 2^(r+e_0)
       n^(-2r-e_0) t^(2r+2e_0) exp(Cn/b)
    <=2 (2t^2)^(r+e_0)/(2r+e_0)! exp(Cn/b).

Summing r>=0 and e_0=0,1,2 is at most

    2(1+2t^2+4t^4) exp(sqrt(2)t+Cn/b),

because (2r+e_0)!>=(2r)! and sum_r x^(2r)/(2r)!<=exp(x). This overcounts some impossible r,e_0 values harmlessly. The constant word N contributes 1. The constant word D contributes at most 2exp(Cn/b), since alpha^(-k)beta^m<=exp(Cm/b) by rho m=k. Incorporating the prefactor e in (5.2), and n/b=O(t/n^2), proves

    T2<=D n^(2L) mu^2 exp(Ct).                            (5.5)

All polynomial factors in t were absorbed into exp(Ct). Endpoint runs and the all-D word were included explicitly; neither was assigned a spurious two-switch charge.

The positive semidefinite matrix F_f^*F_f has nonnegative eigenvalues. Cauchy--Schwarz on its nonzero eigenvalues, (4.1), and (5.5) now give

    R_C(IMM(n,n))>=T^2/T2>=D exp(-Ct).                    (5.6)

This completes the hard-polynomial estimate at the new balance. It is the same rank map, same paths, same occupations and same layer schedule throughout; the circuit and hard-polynomial bounds do not use different measures or different parameter choices.

## 6. All characteristic-zero fields and the frozen constant

In ordinary (unnormalized) monomial bases, the finite matrix F_f has integer entries: f has integer coefficients, and formal differentiation supplies integer falling-factorial coefficients. Its rank over C is its rank over Q. For any characteristic-zero field K the injective embedding of Z into K preserves which integer minors are zero, so its rank over K is the same. No embedding of K into C, coefficient-height restriction, or finitely generated subfield argument is required. Thus (5.6) holds over EVERY characteristic-zero field at the same absolute threshold. This is Source135's actual integer-minor transfer, now applied to our same integer matrix. The circuit upper bound (3.3) was already valid over every field.

Combining (3.3) and (5.6), cancelling the positive integer D, yields

    10 S^3 t^(-t/128)>=exp(-Ct),
    log S >= t log(t)/384 - Ct/3 - log(10)/3.              (6.1)

Eventually t>=n^(1/4)/2 and log t>=log n/5. The leading term on the right of (6.1) is therefore at least n^(1/4)log n/3840. Because log t tends to infinity, the two negative terms consume at most half that leading term after increasing the one absolute threshold. Hence

    log S >= n^(1/4)log n/7680
           >=n^(1/4)log n/20000.

Exponentiating proves the exact frozen computational-gate lower bound, and counting additional leaf vertices cannot reduce size. All eventual requirements in Sections 1--6 concern only the numerical integer n and absolute inequalities, so their maximum is one absolute n_0 independent of K and of the circuit. Nothing is claimed for a specified small n. The circuit is a finite DAG with arbitrary finite fan-in/out, arbitrary coefficients, shared subcomputations and repeated occurrences, exactly as frozen.

## 7. Dependency and scope of this author argument

The proof credits the stipulated Source135 rank factorization, occupation identity, four-path local table, balanced scheduling and integer-minor transfer at their strongest operative scope. Those components have been restated and checked with the new parameters. Its entire old depth-five lower bound and all-field block expansion upper bound remain paid and are not nominated again. The degree-band idea and choice of a slope with a higher-order perturbation are credited to the actual AGKST residue/decomposition operation; the specialized arithmetic and S^3 decomposition are given explicitly here.

The additional proposed operation is (5.1)--(5.2): simultaneous expansion of both kinds of collision corrections into a third equality state, followed by one runwise folding estimate on the common labels. This removes the exp(Theta(n/t)) pointwise-U cost when t=n^(1/4), while preserving the whole ordinary homogeneous circuit model. Parent review must decide whether this constitutes a substantial contribution after the strongest actual primary composition. The argument does not self-certify that decision or assert worldwide priority.

No prior frozen target is replaced or weakened. No characteristic transfer beyond zero, border assertion, nonhomogeneous assertion, wire lower bound in place of gates, set-multilinear restriction, or algorithmic construction theorem is smuggled into the conclusion. Bounded finite tests support only the local arithmetic and counting checks documented separately; they are not proofs of (5.2), (5.6), or the theorem, and are not review gates.
