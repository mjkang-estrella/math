# Full shifted Jacobi denominator law: ordinary proof

Written 2026-10-28 UTC. Research candidate, solo verification only. No independent
review or complete Lean certificate yet; discovery credit remains 0.

## Exact statement and adopted source bridge

Let kappa_r be **literally** Definition 2.1, equations (6)–(7), of
Iván Area, arXiv:2608.23006v2 (5 October 2026), expressed in the independent
variables u=alpha^2-1/4, v=beta^2-1/4. For every integer r>=1, the maximum
2-adic denominator exponent among all its coefficients is

    delta_r = 2r + v2((r-1)!).

Here coefficients are rational, and Z_(2) means rationals with odd denominator.
This is the shifted-variable question of Remark 3.8, not the original-variable
law already proved in arXiv:2609.29531v2 (14 October 2026). There is no assertion
about identifying these formal constants with analytic phase constants.

We use the ordinary formal bridge already proved in the r3 lane and checked
by root in root-jacobi-riccati-adoption-r3/ADOPTION.md. Explicitly, put

    D=-(1+t^2)d/dt,  V=u(1+t^2)+v(1+t^-2),
    s_1=V,
    s_(n+1)=-D s_n - sum_(a+b=n; a,b>=1) s_a s_b.

Then s_n are integral Laurent polynomials with parameter degree at most
ceil(n/2), divisible by 1+t^2, and s_n(-t)=(-1)^(n+1)s_n(t). For odd n let
J_t(s_n) be its unique odd Laurent D-primitive and J(s_n)=J_t(s_n)(1). The
literal source definition gives

    kappa_r=(-1)^r J(s_(2r-1))/2^(4r-2).                 (1)

This is not an additional conjectural interface: r3 derives
D^2 F+2iZ DF-VF=0 directly coefficientwise from equation (6), then takes the
formal logarithmic derivative. Its imaginary part is odd in t, so the
constant of integration is zero. Root has validated that ordinary argument.
The same source construction is independently compared with the coordinates
below in check.py. A literal Lean encoding of that established ordinary bridge
still remains required; this file does not claim a completed formal endpoint.

The supplied attainment theorem is

    [u^r]kappa_r=Catalan_(r-1) I_r/2^(4r-2),
    I_r=sum_(j=0)^(r-1) binom(r-1,j)/(2j+1),
    v2([u^r]kappa_r)=-2r-v2((r-1)!).                    (2)

Its all-order coefficient formula is proved by r3's highest-degree Riccati
recursion. The valuation uses the primary's Theorem 1.4 and elementary
factorial/Catalan valuations. We do not claim a new attainment argument here.
It suffices to prove the upper bound for every coefficient. In fact we prove
r3's stronger degree-specific guess:

    (d-1)! [degree d] J(s_(2r-1))
            belongs to 2^(2r-2) Z_(2)[u,v], 1<=d<=r.   (3)

## 1. An integral midpoint algebra and the exact scaling

Work first with independent parameters a,b over Z in

    R=Z[x,w]/(w^2-x^2-1).

Every element of R has a unique expression A(x)+w B(x). Define a derivation
partial by

    partial x=-(1+x^2)=-w^2,   partial w=-wx.

It respects the relation: partial(w^2-x^2-1)=0. The ideal (w) is stable under
partial. The map into Q[t,t^-1] defined by

    x=(t-t^-1)/2,  w=(t+t^-1)/2

is injective and becomes an isomorphism over Q, with inverse t=w+x,
t^-1=w-x. In these coordinates D=2 partial. In particular all manipulations
can be made integrally in R before this embedding; no claim that x,w are
integral Laurent polynomials in t is being made.

Put a=u+v, b=u-v, and define

    P=a w^2 + b wx.

Direct substitution gives V=2P. Let h_n in R[a,b] satisfy

    h_1=P,
    h_(n+1)=-partial h_n - sum_(i+j=n; i,j>=1) h_i h_j.   (4)

They have integral coefficients. For their homogeneous degree-d parts,
coefficientwise induction in the displayed recurrences proves

    [degree d]s_n = 2^(n+1-d) [degree d]h_n              (5)

after a=u+v,b=u-v and the embedding into Q[t,t^-1]. The derivative term gains
one factor 2; in a product with i+j=n and e+f=d the scaling exponent is
(i+1-e)+(j+1-f)=n+2-d, exactly the exponent for s_(n+1).
All occurring d satisfy 1<=d<=ceil(n/2), so these are nonnegative powers.

Two involutions will be used separately. First, rho(x)=x,rho(w)=-w commutes
with partial. Since the a-part of P is rho-even and the b-part is rho-odd,
the coefficient of a^i b^j in h_n has w-parity j modulo 2. Second,
tau(x)=-x,tau(w)=-w anticommutes with partial. P is tau-even, and induction
in (4) gives tau(h_n)=(-1)^(n+1)h_n. For odd n this says the normal form
of h_n is A(x^2)+wx B(x^2).

Every h_n also belongs to the ideal (w): P does, partial preserves it,
and products of its elements do. In the unique normal form, membership in
(w) says that the w-even part is divisible by 1+x^2 in Z[x]. These assertions
hold separately for every parameter coefficient and every homogeneous degree.

## 2. The binary-degree filtration (all orders)

Write sigma(k) for the number of ones in the binary expansion of k, including
sigma(0)=0. For a nonzero bidegree alpha=(i,j), define

    q(alpha)=sigma(i)+sigma(j)-1 >=0.

Two elementary binary facts are

    sigma(k+l)<=sigma(k)+sigma(l),  sigma(2k)=sigma(k).

Consequently, for nonzero alpha,beta,

    q(alpha+beta)<=q(alpha)+q(beta)+1,
    q(2alpha)=q(alpha).                                (6)

Let C be the additive subgroup of R[a,b] consisting of polynomials with no
parameter-constant term whose coefficient at each a^i b^j is divisible by
2^q(i,j) **in the integral ring R**. It is stable under partial.
It has the following two closure properties:

    f,g in C ==> 2fg in C,   f in C ==> f^2 in C.        (7)

For the first, use the first inequality in (6) on each coefficient product.
For the square, pair distinct parameter monomials to obtain 2 f_alpha f_beta.
For equal parameter monomials the coefficient is f_alpha^2, divisible by
2^(2q(alpha)), hence by 2^q(2alpha) since q(alpha)>=0. This proves (7) without
assuming C is a subring; usually it is not a subring.

The initial P is in C, since its two parameter monomials have q=0. In the
convolution in (4), pair the distinct spectral indices i,j; each pair is
2h_i h_j. If n is even there is also the single diagonal square h_(n/2)^2.
Thus (7) and strong induction prove

    [a^i b^j]h_n belongs to 2^(sigma(i)+sigma(j)-1) R
    for all n>=1 and all i+j>0.                        (8)

This is the needed all-order mechanism. No finite-range inference occurs.

For j odd, sigma(j)=sigma(j-1)+1. If i+j=d, binary subadditivity gives

    sigma(i)+sigma(j)-1
       =sigma(i)+sigma(j-1)>=sigma(d-1).                (9)

The w-odd part is precisely the part with j odd. Combining (8) and (9),
for every n,d its entire degree-d w-odd component is divisible by

    2^sigma(d-1) in R[a,b].                            (10)

## 3. Odd primitives preserve this divisibility at the midpoint

Fix odd n and d. By the support properties in Section 1 its degree-d piece
has the normal form

    H=(1+x^2) A(x^2) + wx B(x^2),                      (11)

where A,B belong to Z[a,b][X], homogeneous of parameter degree d. Moreover
all coefficients of B are divisible by 2^sigma(d-1) by (10).

The partial-primitive of the first term can be chosen to be the odd polynomial

    -sum_k A_k x^(2k+1)/(2k+1).

It belongs to Z_(2)[a,b,x], vanishes at x=0, and is tau-odd.
For the second term seek a primitive w f(X), X=x^2. Direct differentiation
in R gives

    partial(w f(X))=-wx [ f(X)+2(1+X) f'(X) ].         (12)

The operator T f=f+2(1+X)f' is an automorphism of Z_(2)[X] as a module
(preserving every finite-degree submodule). Its diagonal coefficient on X^k
is 2k+1, an odd unit; its next coefficient is 2(k+1). More explicitly, if
B=sum_(k=0)^N B_k X^k, set f_(N+1)=0 and define downwards

    f_k=(-B_k-2(k+1)f_(k+1))/(2k+1).                  (13)

Then T f=-B. All divisions are by odd numbers, and downward induction proves

    f in 2^sigma(d-1) Z_(2)[a,b][X].                  (14)

Thus the sum of these two primitives is tau-odd, and its value at x=0,w=1
belongs to 2^sigma(d-1) Z_(2)[a,b]. Under t=w+x it is an odd Laurent
polynomial. The kernel of D on rational Laurent polynomials consists of
constants; its odd subspace therefore has zero kernel. This proves that this
constructed primitive is exactly the unique odd primitive used in (1),
with the scaling below. There is no unidentified integration constant.

From (5) and D=2 partial, the odd D-primitive of the degree-d part of s_n is
2^(n-d) times this partial-primitive. At t=1 we have x=0,w=1, so

    [degree d]J(s_n)
      in 2^(n-d+sigma(d-1)) Z_(2)[a,b].                (15)

This statement concerns the integral a,b coordinate polynomial before the
substitution. Substitution a=u+v,b=u-v has integer coefficients and preserves
its divisibility. We never use the inverse substitution u=(a+b)/2,v=(a-b)/2
to transfer an integrality claim.

## 4. Completion of the all-coefficient law

For n=2r-1, Legendre's formula
v2((d-1)!)=d-1-sigma(d-1) rewrites the exponent in (15) as

    2r-1-d+sigma(d-1)=2r-2-v2((d-1)!).

This proves (3) for every r and every 1<=d<=r. Since (d-1)! divides (r-1)!,
it follows that

    (r-1)! J(s_(2r-1)) in 2^(2r-2) Z_(2)[u,v].         (16)

This is exactly the previously missing GAP. Equations (1) and (16) give
all coefficients of kappa_r valuation at least -2r-v2((r-1)!). Equation (2)
attains that value, so the common dyadic denominator exponent is exactly
2r+v2((r-1)!) for every r>=1. This proves the full literal shifted law.

## Adversarial checks and limits

The binary filtration is not asserted to be multiplicatively closed: the
factor 2 on off-diagonal terms is indispensable. For example (a+b)^2 has
coefficient 2 at ab, whereas (a)(b) has coefficient 1, which fails q(1,1)=1.
The proof uses both pairings, first by spectral index and then by parameter
monomial inside a diagonal square. Omitting either pairing invalidates (8).

There is no coefficientwise t-Laurent primitive divisibility claim. The
r=2 primitive t+t^3/3 remains the mandatory counterexample to such a claim;
in midpoint coordinates its nonvanishing-at-midpoint component has gained
the required factor. There is no generic shifted-binomial-moment estimate:
464/315 remains a counterexample to that proposed estimate. No generic WKB
arithmetic theorem is invoked.

check.py independently compares (i) the normalized quotient-ring recurrence,
(ii) the original integral t-Laurent recurrence and primitives, and (iii) the
literal source inverse-factorial/cumulant construction, in small fixed ranges.
It also checks each algebraic involution, multidegree filtration and primitive
recurrence in those ranges. These diagnostics can falsify implementation or
normalization errors but are not the proof of the unbounded statements.

Classical ingredients: Riccati recurrence, quadratic-algebra coordinates,
binary subadditivity/Legendre, odd-unit triangular inversion, and the already
published binomial valuation. The research deduction here is their exact
filtered-ring combination closing (16). No worldwide novelty/priority claim;
current-source and bounded registry chronology are in source/registry-screen.md.
A complete literal Lean endpoint and independent root gates remain outstanding.
