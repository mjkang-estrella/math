# W014 B: independent carry-image review

2026-10-08 America/Los_Angeles / 2026-10-09 UTC.
**Disposition: accept the composite-denominator image theorem as stated;
accept the carry-image consumer with the explicit input and cost guards below.**
No error was found in the stated constants or quantified image bound. One
integration qualification is needed when normalizing a family of certificates:
different reduced denominators do not automatically give the same powered base
if alpha is kept fixed. Section 5 gives an exact transformation that preserves
the original shared table and giants.

**Verified complete factoring improvement: NONE.** The result obstructs a
particular explicit-list generator on full residue systems at fixed degree.
It is not an all-factoring lower bound, an implicit-product lower bound, a
useful-certificate acquisition theorem, or a new factoring algorithm. The
parent remains principal researcher. W014 A, W014 C, and W013's quartic-budget
correction were not re-audited.

## 1. Frozen authority and evidence

The [original brief](W014-carry-image-review-evidence/original-brief.txt) and
[input manifest](W014-carry-image-review-evidence/input-manifest.json) freeze the
five requested instruction/contract files, STATE, W014, the complete parent
carry-image proof, and the accepted W013 review. STATE was read for context,
not used as a mathematical premise. The principal mathematical inputs are:

- `research/hypotheses/W014.md`, SHA-256
  `aef28d3145145d1720e4c31a1ad7d526d74654777c09cbd9fa3c5d24e30b409d`;
  only Card B is this audit's subject.
- `research/findings/W014-carry-image-bound.md`, SHA-256
  `3f19d9238a7c53a9f51c320925ece5cfc0b49cd65fadb834a01fc4c1553c92d1`;
  every step of this proof is audited below.
- `research/findings/W013-hidden-period-review.md`, SHA-256
  `d672a6201942143266f630188480a872b32292c923ba979d777b4f27ecf7f472`;
  its accepted conditional collision machinery is the baseline, not a new
  claim of W014.

All three are copied under
`W014-carry-image-review-evidence/frozen/research/` with their original paths.
The [drift record](W014-carry-image-review-evidence/source-drift.json) found a
concurrent STATE change and preserves its observed bytes and diff. The three
mathematical inputs were unchanged at that check. The frozen versions above
remain the review authority; the STATE update was not imported as a premise.

The [preregistration](W014-carry-image-review-evidence/preregistration.md) fixed
ten exact algebra cases before script creation/execution. The single
[certificate execution](W014-carry-image-review-evidence/certificate-output.json)
passed **10/10 cases and 79/79 checks**, exit 0, with empty stderr and no timeout.
All cases, including deliberately unsafe variants, are retained. The script is
an arithmetic certificate using known fixture factors, not an N-only solver or
an implementation of the general integer-root algorithm. No performance run,
parameter/prime/degree sweep, installation, delegation, publication, commit,
or shared solver/Lean/state/registry edit was performed.

## 2. Carry-image consumer: complete conditional contract

Let N>1 be composite. Supply a unit alpha modulo N, a common integer M>=1,
and K certificates. Certificate i has integer X_i>=2, a finite integer block
of offsets (or a retained subset of such a block), q_i>=1 integer, an integer
polynomial P_i of degree at most a fixed d, and E_i>=0 **integer**. Define

    A_i(h) = floor(P_i(h)/M),
    r_i(h) = P_i(h) - M*A_i(h),       0 <= r_i(h) < M.

The supplied literal list R_i must include the Euclidean remainder for every
retained offset used by its certificate. A superset suffices. A list of
congruent but noncanonical integer representatives is not automatically the
same input: replacing r by r+Mt changes the error index. Reduce representatives
to [0,M) before invoking this contract. Duplicate records can be removed with
paid processing; otherwise charge their actual multiplicity.

The success premise is that some prime p|N lies in a covered retained domain
and, at h=p-X_i,

    |A_i(h) - q_i*N/p| <= E_i.

A uniform certificate on the entire block is sufficient, but the consumer
only uses the statement at the covered prime. Coverage of a retained domain,
its image, the approximation bound, and any required membership operations
must be acquired and charged. They are not inferred by the collision search.

Check gcd(alpha,N) before taking powers with possibly negative exponents.
A proper gcd is a factor; gcd=N rejects the proposed base. For a unit, use
an actual inverse modulo N and ordinary signed binary exponentiation. A
rational/nonintegral error bound must first be converted to a justified
nonnegative integer radius, charging the resulting list size. All coefficients,
parameters, exponents, endpoints and list indices have their actual binary
widths included in the cost; a polynomial-in-log-N specialization requires
these widths to be polynomial in log N.

### 2.1 Transfer and all signed indices

Write c=N/p and e=A_i(p-X_i)-q_i*c. Both c and e are integers. With

    D_i = P_i(1-X_i) - M*q_i*N,

the exact difference is

    D_i - (M*e+r_i(p-X_i))
      = P_i(1-X_i)-P_i(p-X_i) - M*q_i*(N-c).

Since p-X_i is congruent to 1-X_i modulo p-1 and N-c=(p-1)c, this proves
the claimed transfer. This uses the integer polynomial P_i, not a false
polynomial-congruence rule for floor(P_i/M). **There is no division by M
modulo p-1**, so gcd(M,p-1)=1 is not needed.

For B>=1 integer, take beta=alpha^M and babies beta^j, 0<=j<B. Since
-E_i<=e<=E_i, Euclidean division gives the unique pair

    e+E_i = kB+j,    0<=j<B,
    0<=k<ceil((2E_i+1)/B).

For the true r, the proposed giant

    gamma_(i,r,k) = alpha^(D_i-r+M*E_i-M*kB)

is congruent modulo p to alpha^(M*j)=beta^j. The signs and range are
correct, including E_i=0, B=1, either error endpoint, negative D_i, and a
partially occupied final chunk. Padding can produce candidate e'>E_i; those
tags are still charged and can be checked as written. They cannot be the
true tagged collision once component uniqueness holds. The prime p=2
presents no transfer exception; its component order is only one.

### 2.2 Order guarantees are about beta, not alpha

With a valid promise ord_N(beta)>=B, check gcd(beta^j-1,N) for 1<=j<B.
No check can equal N under that promise. If a check is nonunit, it is a
proper factor. If all are 1, then every prime t|N satisfies ord_t(beta)>=B:
a smaller component order would be an index at which the gcd is divisible
by t. Thus all B babies are distinct modulo every prime component and
globally, including when N has repeated prime factors.

An implementation can instead run the checks without assuming the promise
in advance, but **gcd=N must then reject the base/B combination**, not be
treated as a harmless failure to split. Reacquisition or a smaller B must be
charged. For B=1 there are no checks. For a covered p=2 and B>1, a valid
global-order promise forces a proper gcd before continuation.

For units in any modulus,

    ord_N(alpha^M) = ord_N(alpha)/gcd(ord_N(alpha),M).

Consequently an order guarantee for alpha does not supply the required one
for beta. Certificate case 8 has N=35, alpha=2 of order 12, M=12 and beta=1.
The first check for B=2 gives N, not a factor. Base/order acquisition is a
separate paid success obligation; no factorization of an unknown group order
is implicitly available.

### 2.3 Full-modulus matches and proper extraction

Keep tags (i,r,k). If a true tagged giant equals baby j' modulo N, reducing
modulo its covered p gives beta^j'=beta^j. The component-order bound forces
j'=j, so e'=kB+j'-E_i is the actual integer e. Therefore p is a root of

    F_(i,r,e')(x) = x*(P_i(x-X_i)-r-M*e') - M*q_i*N.

Its degree is at most d+1 and F(0)=-M*q_i*N != 0. Thus it is never the
zero polynomial under the stated contract, even if P_i is constant. Search
its integer roots in the relevant containing block with an exact fixed-degree
root routine, and check every returned candidate for proper divisibility of N.
A root can divide q_i*N without dividing N, so the latter check is essential.
An actual factor recovered outside a retained subset is also a valid output;
retained membership is needed only if imposed as an extra procedural condition.

The exact fixed-degree integer-root procedure accepted in W013 suffices: use
finite-difference recursion to partition an integer interval into monotone
runs, then binary search transitions. Its degree-dependent constants and
arithmetic widths are paid. There are at most d+1 roots of the nonzero
top-level polynomial, and no factorization of its constant coefficient is
needed. This is a bit-cost argument, not a unit-cost root oracle.

Every full-match tag must be processed before its giant is discarded. Equal
giant residues can have different recovery equations. Global baby uniqueness
gives at most one baby per tag, hence at most G such root calls, where G is
the actual number of giant records. Incorrect r/e' matches are included.

After full matches are handled, form the product of (Y-gamma) over retained
giants and evaluate it at the babies, as in the accepted W013 consumer. A
retained true collision gives a nonunit value. A proper gcd succeeds. If
the product gcd is N, at least one leaf is a nonunit, and every leaf has
gcd<N because full-modulus matches were removed. A tree descent or one
scan therefore finds a proper factor. This applies to prime powers as well
as squarefree N and adds at most one G-leaf recovery scan, not B scans.

Case 6 verifies the signed full-match branch at N=35, M=2, P(h)=15-2h,
X=5, E=1, B=2: D=-47, true r=1, e=0, (k,j)=(0,1), giant exponent -46,
and F(x)=-2(x-5)(x-7). Case 7 shows precisely why component checks cannot
be omitted: N=21, M=5, alpha=2 gives beta=11 of global order 6 but order
2 modulo 3. With B=4 and the stated constant certificate, the true tag
globally matches the wrong baby if the check is skipped; its two global
recoveries have roots 7/3 and 7, neither in [3,4). The actual component
check returns factor 3. This falsifies the bypass, not the guarded consumer.

### 2.4 Total paid list cost

Put t_i=|R_i| after any paid deduplication, and

    T = sum_i t_i,
    S = sum_i t_i*(2E_i+1),
    G(B) = sum_i t_i*ceil((2E_i+1)/B).

Then G>=T, G>=S/B and G<=T+S/B. The precise conditional bit envelope is

    (B + G(B) + K)*poly_d(log N + w)
      + C_certificate + C_coverage + C_image + C_base/order,

where w bounds the actual operand/encoding widths, including log(B+G+K+2).
The polynomial factor also absorbs sorting and fast product/remainder-tree
operations; it is not a claim that arbitrary wide integers cost one step.
There are T initial giant exponentiations (or a cheaper paid shared
construction), each using the actual exponent width. Subsequent giants
advance by beta^(-B). Since T<=G, these costs fit the envelope. Reading
certificate coefficients and computing D_i are part of the K term.

The accepted monic polynomial product/evaluation machinery over Z/NZ needs
no inverses of arbitrary nonunits. Full recovery has at most G root calls,
the preliminary order screen at most B-1 gcds, and the final recovery at
most G more gcds. This explains why the displayed list bound is attainable
conditionally and is not secretly a B*G pairwise scan.

Ignoring order feasibility and acquisition only for the purpose of optimizing
the list expression, and assuming S>=1, its minimum is

    Theta(K + T + sqrt(S)).

For example B=ceil(sqrt(S)) attains the matching upper envelope. This B
still needs the paid order/coverage conditions above. If all E_i=0, then
G=T for every B; dropping T would incorrectly turn explicit image processing
into a square-root-size task. Empty image lists contribute zero but cannot
cover a nonempty successful domain. An empty whole input collection cannot
satisfy the success premise.

## 3. Floor-preserving normalization, including all degenerate cases

For M>=1 and P(h)=a0+sum_(j=1)^d a_j*h^j, let

    g=gcd(M,a1,...,ad)>0,   m=M/g,
    r0=a0 mod g,           c=(a0-r0)/g,
    Q(h)=c+sum_(j=1)^d (a_j/g)*h^j.

For any integer h, Euclidean division writes Q(h)=m*z+t with 0<=t<m,
even if Q(h) is negative. Hence

    P(h) = M*z + g*t+r0,
    0 <= g*t+r0 <= g*(m-1)+g-1 = M-1.

This proves both identities exactly:

    floor(P(h)/M) = z = floor(Q(h)/m),
    P(h) mod M = r0 + g*(Q(h) mod m).

The remainder map on the right is injective on {0,...,m-1}; image cardinality
is unchanged on **any fixed integer domain**. For full residue systems,
projection from Z/MZ onto Z/mZ is surjective, so the same statement compares
the two full images. Negative constants are handled by the nonnegative
Euclidean remainder, not by truncating division toward zero.

By the defining gcd,

    gcd(m,a1/g,...,ad/g)=1.

Thus for every prime ell|m, some nonconstant coefficient of Q is an ell-adic
unit. One such coefficient can differ from another prime's unit coefficient;
no single coefficient is required to be coprime to m. Zero coefficients cause
no problem. If all nonconstant coefficients are zero, g=M and m=1. More
generally, if they all vanish modulo M then m=1 even if Q is a nonconstant
integer polynomial. In either case there is only the normalized carry 0;
this does not remove the remaining error search or certificate cost.

Case 1 includes M=12, P=-13+18h^2, yielding g=6, m=2, r0=5 and
Q=-3+3h^2, as well as P=-13 with all nonconstant coefficients zero. This
normalization uses gcd, remainder, and exact division only; it does not
factor M.

## 4. Composite image theorem: independent proof with the stated constants

Fix d>=1. For m>1 and Q in Z[h] of degree at most d with
gcd(m,b1,...,bd)=1, the parent claims

    |Q(Z/mZ)| >= m / (C_d*(2d)^omega(m)),

with

    a_(ell,d) = floor(log_ell d),
    s_(ell,d) = a_(ell,d) + v_ell((d-1)!),
    C_d = product_(primes ell<=2d) ell^(2*s_(ell,d)+1).

This is correct, uniformly over m and all coefficient sizes, including
coefficients that vary with m. Set v_ell(0)=infinity when comparing valuations.
The logarithm floor means the exact largest a with ell^a<=d; no floating-point
evaluation is needed to define the constant.

### 4.1 Large primes: enough values have one regular preimage

Let ell^k divide m with ell>2d. Reduction of Q is a nonconstant polynomial
over F_ell of degree n between 1 and d. Since n<ell, its derivative is
nonzero and has degree at most d-1, so at least ell-d+1 input residues have
unit derivative. For each value y, the nonzero polynomial Q-y has at most
d roots in F_ell. The images of those inputs consequently number at least
(ell-d+1)/d.

Here a regular image means a value with **at least one** unit-derivative
preimage. Other preimages may be singular; this does not affect the argument.
Fix one regular preimage a of each selected value. Given a solution x modulo
ell^v to a desired lifted value, write its next digit as x+ell^v*t. For v>=1,

    Q(x+ell^v*t) = Q(x) + ell^v*t*Q'(x)  (mod ell^(v+1)).

Since Q'(x) is a unit, exactly one digit t modulo ell reaches any prescribed
next output digit. Every one of the ell^(k-1) values above the original
value is therefore attained. Distinct original values give disjoint lifts.
Thus

    |Q(Z/ell^k Z)| >= ell^(k-1)*(ell-d+1)/d
                    >= ell^k/(2d).

The last inequality follows from ell-d+1>=ell/2; the stated strict
threshold ell>2d safely implies it. It also covers k=1 and d=1. Case 4
checks Q=h^2 at ell^k=49: three regular values lift to 21 values, and the
additional singular value makes the full image size 22.

### 4.2 Small primes: the Newton argument really is uniform

Fix any prime ell<=2d dividing m. Put a=floor(log_ell d),
b=v_ell((d-1)!), and R=Q'. Some coefficient b_j of Q, j>=1, is an
ell-adic unit. Its derivative coefficient j*b_j has valuation v_ell(j)<=a.
Different derivative coefficients have different powers, so this coefficient
cannot disappear through cancellation with another derivative term. Thus

    min_(coefficients of R) v_ell(coefficient) <= a.

Let v=d-1 and suppose, for a contradiction, that all d integer values
R(0),...,R(v) are divisible by ell^(a+b+1). Each forward difference
Delta^j R(0), 0<=j<=v, is an integer linear combination of these values,
so it has the same divisibility. Newton interpolation gives the exact identity

    R(x) = sum_(j=0)^v Delta^j R(0) * binom(x,j).

For every j<=v, the polynomial

    v!*binom(x,j) = (v!/j!)*x*(x-1)*...*(x-j+1)

has integer coefficients (with the usual j=0 convention). Hence all
coefficients of v!*R are divisible by ell^(a+b+1). Removing v! shows that
all coefficients of R have valuation at least a+1, a contradiction.

Therefore some x0 in {0,...,d-1} satisfies

    s=v_ell(Q'(x0)) <= a+b=s_(ell,d).

This is a finite, nonzero derivative value. The proof works with missing
leading coefficients, arbitrarily large signed coefficients, repeated roots,
and a derivative that reduces to the zero polynomial modulo ell. Primitivity
does not assert that the polynomial *function* modulo a small ell is
nonconstant: Q=h^3-h is identically zero as a function modulo 3 despite
primitive nonconstant coefficients. That example (case 3) is handled here.

For d=1, v=0, 0!=1 and a=0. Newton interpolation is the single value
R(0); the derivative is the primitive linear coefficient and is a unit.
There is no missing degree-one edge case.

### 4.3 Taylor scaling and bijectivity

The exact Taylor expansion at an integer x0 is

    Q(x0+y)-Q(x0) = Q'(x0)*y + sum_(j=2)^d c_j*y^j,

where every c_j is an integer: expand each monomial by the binomial theorem.
Write Q'(x0)=ell^s*u with ell not dividing u and substitute y=ell^(s+1)*t.
The linear term becomes ell^(2s+1)*u*t. For j>=2, the remaining quotient
has ell-exponent

    j*(s+1)-(2s+1) = (j-2)*s+j-1 >= 1.

It follows that

    Q(x0+ell^(s+1)*t)-Q(x0)
      = ell^(2s+1) * H(t),
    H(t)=u*t+ell*V(t),       V in Z[t].

No denominator or characteristic-zero analytic Taylor estimate is hidden
here. For every r>=1, H induces a bijection on Z/ell^r Z. Modulo ell it
is multiplication by the nonzero u. If a solution is unique modulo ell^v,
then the same digit expansion shows

    H(t+ell^v*z) = H(t) + ell^v*z*H'(t) (mod ell^(v+1)),
    H'(t) = u (mod ell).

Thus exactly one next input digit reaches each specified next output digit.
Induction proves both existence and uniqueness for every target, not merely
that all derivatives are units. Case 2 checks the nonunit-derivative example
Q=h^4+h^2, ell=2, x0=1, s=1. Its scaled polynomial is
3t+2(7t^2+16t^3+16t^4), and its full image modulo 64 contains 2+8Z/64Z.

For k>2s+1, take r=k-(2s+1). Surjectivity of H modulo ell^r gives a full
coset of ell^(2s+1)Z/ell^k Z, of size ell^(k-2s-1). Every chosen integer
input is a legitimate input residue modulo ell^k. For k<=2s+1, one output
already gives the needed lower bound. Since s<=s_(ell,d), both cases yield

    |Q(Z/ell^k Z)| >= ell^k / ell^(2*s_(ell,d)+1).

This also explains why ignoring small-prime powers would be an invalid
shortcut: their exponents k are unbounded. The parent's proof does not
ignore them; it supplies an explicit loss independent of k and coefficients.

### 4.4 CRT, constants and the uniform asymptotic conclusion

CRT identifies the full input ring with the Cartesian product of its
prime-power rings, and polynomial evaluation is coordinatewise under this
identification. For any tuple of attainable output coordinates, choose one
input preimage in each coordinate and combine those inputs by CRT. Therefore

    |Q(Z/mZ)| = product_(ell^k || m) |Q(Z/ell^k Z)|.

Multiplying the established local bounds gives the stronger denominator

    product_(ell<=2d, ell|m) ell^(2*s_(ell,d)+1)
      * (2d)^(number of prime divisors of m exceeding 2d).

It is at most C_d*(2d)^omega(m). Missing small primes in the product and
the extra 2d factors only weaken the final bound, so the parent's specified
C_d is valid. For example C_2=2^3*3=24. Case 5 verifies exact image size
12 for h^2 modulo 72=8*9 and the corresponding CRT product. The stronger
prime-field-looking estimate m/d would fail there; it is not claimed by
the parent for composite m.

For completeness, write t=omega(m). The distinct prime factors have product
at least t!, so log(m)>=log(t!). If t grows, this gives
t/log(m)<=1/(log(t)-O(1)); if t remains bounded, t/log(m) tends to zero
directly. This is uniform: first choose a threshold for t, then a threshold
for m. Thus omega(m)=o(log m), and, for fixed d,

    log C_d + omega(m)*log(2d) = o(log m).

Consequently |Q(Z/mZ)|>=m^(1-o(1)), uniformly in the allowed coefficients.
Equivalently, for every epsilon>0 and fixed d there is m0(d,epsilon) such
that every allowed Q and every m>=m0 satisfy |image|>=m^(1-epsilon).
The upper bound |image|<=m then gives the corresponding logarithmic
exponent limit. It is not a uniform positive-density claim: for h^2 modulo
products of distinct odd primes the relative image size is the product of
(ell+1)/(2ell), which can tend to zero.

If m=1 the image is the singleton residue class and the normalization case
already suffices. For d=1, gcd(m,b1)=1 makes Q an affine permutation modulo
m, giving the stronger exact image size m. No use of the factorization of
m in this mathematical proof grants it free to a factoring implementation.

## 5. A family-normalization qualification and exact repair

The parent proof's statement that one can use Q,m directly is correct for a
single certificate. For a family, take M=6, P1(h)=2h, P2(h)=3h. They reduce
to Q1=Q2=h with m1=3 and m2=2. If alpha is kept fixed, the new babies use
alpha^3 and alpha^2, respectively. For alpha=2 modulo 35 these bases are
8 and 4, whereas the old common base alpha^6 is 29 (case 9).

The failed inference is: preserving each rounded A_i by itself preserves
one common powered base while alpha stays fixed. One repair is to group
certificates by their new denominators and pay separately for their tables
and order conditions. A more exact repair preserves the old computation:

    g_i = gcd(M, nonconstant coefficients of P_i),
    m_i=M/g_i,   alpha_i=alpha^(g_i),
    D'_i=Q_i(1-X_i)-m_i*q_i*N,
    r_i=r0_i+g_i*r'_i.

Then

    alpha_i^(m_i)=alpha^M=beta,
    D_i-r_i+M*E_i-M*kB
      = g_i*(D'_i-r'_i+m_i*E_i-m_i*kB).

Thus using alpha_i and m_i for certificate i reproduces **exactly the
same giant residue and common babies**, with the same component-order
condition. The recovery polynomial also satisfies

    x*(P_i(x-X_i)-r_i-M*e')-M*q_i*N
      = g_i*[x*(Q_i(x-X_i)-r'_i-m_i*e')-m_i*q_i*N].

Its integer roots are unchanged. Forming the alpha_i requires at most K
paid exponentiations of their actual widths, already compatible with the
conditional K polynomial-width term. This generalization uses one common
beta but permits certificate-specific units alpha_i. It produces no image
cardinality saving and no improvement in beta's order; it simply makes the
normalization/sharing interface exact.

## 6. Counterexample scope, literature and parent action

The proof resolves its stated full-residue, fixed-degree question. The
following distinguish genuine changes of computation from omitted hypotheses:

- **Omitting primitive normalization:** P(h)=m*h modulo m has one image
  value for arbitrarily large m. Its reduced denominator is 1. The constant
  coefficient is deliberately excluded from the gcd; an arbitrary constant
  merely translates the image and cannot repair nonconstant primitivity.
- **Sparse retained domain:** for Q(h)=h^2 modulo m=2^(2a), the retained
  inputs h divisible by 2^a have only the value 0, despite a primitive
  degree-two polynomial. Certifying that a useful factor offset belongs to
  this domain and obtaining the image without scanning all offsets are new
  acquisition obligations. The full-domain theorem cannot decide them.
- **Correlated CRT domain:** for Q(h)=h modulo 6 on {0,1}, there are two
  image elements, while the product of projected image sizes modulo 2 and
  3 is four. Coordinatewise attainment cannot be recombined when the input
  domain excludes the combined preimages. Prime exclusions or a sieve do
  not automatically preserve the full CRT image product.
- **Growing degree:** h^(ell-1) over F_ell has full image {0,1} and unit
  image {1}. Its degree grows with ell. At ordinary integer inputs >1,
  evaluating that integer power has bit length proportional to
  (ell-1)*log(input); the recovery degree grows too. Small modular output
  alone does not compute the required signed integer exponent or solve the
  recovery equation with fixed-degree costs.
- **Implicit images:** cardinality of the full image bounds the length of
  a list that actually enumerates it. It does not bound the size of a
  formula for it or the complexity of a scalar product that avoids listing
  it. A proposed implicit consumer must specify that operation and preserve
  the tagged full-collision recovery guarantee.

These statements include concrete failures of hypotheses stronger than the
parent claims; they are not counterexamples to the proved theorem. Other
excluded degeneracies are nonunit alpha (signed powers may be undefined),
q=0 (the recovery polynomial can be identically zero), unjustified real
radius arithmetic, and silently unbounded coefficient/exponent widths.
The consumer contract in section 2 names the exact guards that remove them.

A narrow primary-literature check read the introduction of
[Xuancheng Shao, *Polynomial values modulo primes on average and sharpness
of the larger sieve*](https://arxiv.org/html/1409.7160v1#S1). It discusses
the elementary reciprocal-degree finite-field image bound and a stronger
average-over-primes theorem. The field bound requires nonconstant reduction
at the prime in question. An average over primes for a fixed polynomial
does not replace the uniform small-prime-power argument needed here. The
[downloaded HTML](W014-carry-image-review-evidence/shao-1409.7160v1.html) and
[source manifest](W014-carry-image-review-evidence/source-manifest.json) are
retained. A sparse-polynomial paper's publisher abstract was also inspected;
no result from its unread full text is used. This is limited prior-art
context, not a novelty search or attribution of the composite theorem.

**Parent action:** accept the image theorem without changing its constants;
make alpha being a unit, E_i being an integer, q_i>=1, actual operand widths,
paid acquisition, and the beta-order failure branch explicit in Card B.
Qualify family normalization using section 5. Retain the list cost
K+sum_i|R_i|+sqrt(sum_i|R_i|*(2E_i+1)) only as the optimized conditional
list envelope with feasible paid order acquisition. A fixed-degree full
residue block cannot supply a fixed-power compression in the reduced
denominator by choosing it composite. The next potentially different
computation must furnish a paid factor-covering restricted-domain generator,
or an actual implicit collision-product algorithm with extraction, or a
different circuit with controlled exponent widths and recovery. None is
supplied or accepted here.

No shared build was run because no project implementation was changed; the
review-owned certificate was executed directly once under its preregistered
budget. Nothing in this audit is a new Lean verification claim. The
[delivery manifest](W014-carry-image-review-evidence/delivery-manifest.json)
and [SHA-256 inventory](W014-carry-image-review-evidence/SHA256SUMS) cover the
report and all scoped evidence; the inventory excludes its own bytes to avoid
self-reference and includes the delivery manifest.
