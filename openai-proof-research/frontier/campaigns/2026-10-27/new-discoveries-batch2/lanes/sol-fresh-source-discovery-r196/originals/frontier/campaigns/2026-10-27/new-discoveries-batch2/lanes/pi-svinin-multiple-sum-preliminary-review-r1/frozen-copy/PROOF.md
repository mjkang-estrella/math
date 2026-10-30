# Svinin Conjecture 3.1: a complete Laurent-polynomial proof candidate

2026-10-28. Credit 0. This is a new-to-project ordinary proof, not yet a
new-to-literature claim. No complete Lean certificate or independent review
exists. The author's 2019 J. Math. Sci. 239(2),159–171 follow-up has not yet
been read beyond its first-page preview and may subsume the result. The
published 2018 source body is indexed but its actual PDF has not yet been
visually compared. These are live gates. All algebraic tools below are
classical; the short/routine-corollary objection must be adjudicated.

## Exact source target and definitions

Svinin, arXiv:1610.05387v2 (1 March 2017), Conjecture 3.1, also MathDB334350.
The latest arXiv HTML is cached in sources/svinin2016-v2.html. Let j,n be
positive integers, k>=0, and M=j(n+1). Put

    s_(k,r)(n) = sum_(x_1,...,x_r in {1,...,n}) (x_1+...+x_r)^(2k+1),
    S_(k,j)(n) = sum_(r=1)^j binom(M,j-r) s_(k,r)(n).

This tuple definition is exactly the coefficient definition of s in the
source, since [z^q](z+...+z^n)^r counts tuples of sum q. The conjecture is

    sum_(1<=lambda_1<=...<=lambda_j<=jn)
        sum_(i=1)^j (lambda_i-(i-1)n)^(2k+1) = S_(k,j)(n).

No coefficient-positivity Conjecture5.2, polynomiality Conjecture5.1 or
Faulhaber-factorization Conjecture6.1 is claimed proved here. At most one
family could be credited if this proof survives all gates.

## A stronger finite identity

Work in Q[z,z^(-1)]. Define

    A_+(z)=z+...+z^n,         A_-(z)=z^(-1)+...+z^(-n),
    H(A)=sum_(r=1)^j binom(M,j-r) A^r,
    C(z)=sum_(weak lambda) sum_(i=1)^j z^(lambda_i-(i-1)n).

We prove the Laurent-polynomial identity

    C(z)-C(z^(-1)) = H(A_+(z))-H(A_-(z)).                 (1)

For any odd function f:Z->Q (indeed into any Q-vector space), the linear
map z^q |-> f(q) sends each side to twice the corresponding sum in the
conjecture. The right-hand map evaluates A_+^r as the literal tuple sum.
Taking f(q)=q^(2k+1) and dividing by 2 proves Conjecture3.1. No limiting
argument or numerical interpolation is involved.

## Pointed subsets

The bijection a_i=lambda_i+i-1 identifies weak tuples lambda with the
j-element subsets 1<=a_1<...<a_j<=M-1. If a=a_i and h=i-1, the number
of such pointed subsets is

    binom(a-1,h) binom(M-1-a,j-1-h),

and lambda_i-(i-1)n=a-h(n+1). With u a second formal variable this gives

    C(z)=[u^(j-1)] sum_(a=1)^(M-1)
         z^a (1+u*z^(-n-1))^(a-1) (1+u)^(M-1-a).       (2)

This is simply the independent choice of h elements below a and j-1-h
elements above it; out-of-range binomial coefficients are zero.

## Finite geometric summation

Compute in Q(z)[[u]], into which the Laurent-polynomial ring injects.
For R=z+u*z^(-n) and B=1+u, the sum in (2) equals

    z * (B^(M-1)-R^(M-1))/(B-R).

This follows by telescoping the finite geometric sum; M>=2. Moreover

    B-R = (1-z)(1-u*A_-).

Its constant coefficient 1-z is invertible in Q(z), so all following
formal-series divisions are legitimate. Define

    T(A)=sum_(r=0)^(j-1) binom(M-1,j-1-r) A^r.

The coefficient from B^(M-1)/(1-u*A_-) is T(A_-). The other coefficient is

    [u^(j-1)] R^(M-1)/(1-u*A_-)
      = sum_(r=0)^(j-1) binom(M-1,j-1-r)
          z^(M-1-(n+1)(j-1-r)) A_-^r
      = z^n T(A_+),

using M=j(n+1) and z^(n+1)A_-=A_+. Therefore

    C(z) = z/(1-z) * (T(A_-)-z^n*T(A_+)).                (3)

The calculation establishes a rational-function identity; C itself is a
finite Laurent polynomial. Consequently there is no singular evaluation
assumption on z, and nothing needs to be asserted separately at z=1.

## Inversion and Pascal cancellation

Replace z by z^(-1) in (3):

    C(z^(-1)) = 1/(z-1) * (T(A_+)-z^(-n)*T(A_-)).

Subtracting gives

    C(z)-C(z^(-1))
      = ((z-z^(-n))*T(A_-)+(1-z^(n+1))*T(A_+))/(1-z)
      = (1+A_+)*T(A_+) - (1+A_-)*T(A_-).                (4)

Here (1-z^(n+1))/(1-z)=1+A_+ and
(z-z^(-n))/(1-z)=-(1+A_-), both finite geometric identities.
Finally Pascal's rule gives the exact polynomial identity

    (1+A) T(A) = binom(M-1,j-1) + H(A).                 (5)

For powers A^r,1<=r<=j-1 this is binom(M-1,j-1-r)+binom(M-1,j-r)
=binom(M,j-r); the degree-j coefficient is one. For j=1 the same formula
is immediate: T=1,H=A. The constants in (5) cancel in (4), proving (1).
This completes the ordinary all-parameter proof.

## Verification and strongest objections

check_multiple_sum.py independently enumerates the literal weak tuples,
counts pointed subsets, builds H coefficients by integer convolution and
compares all antisymmetric coefficients. On 20 pairs n=1..4,j=1..5 it
passes 180 odd-moment identities k=0..8 and 60 exact symbolic identities.
These checks are diagnostics; the all-parameter proof is the algebra above.
All five printed anchors in the separate coefficient-shape investigation
also match, but its 13,230 positive coefficients are not a proof of5.2.

Potential decisive objections to investigate before investment:
1. The 2019 author follow-up may already prove this exact identity. Its
   abstract/first page do not settle that; no clearance from those is claimed.
2. A classical subset/cycle-lemma identity may directly subsume (1). No such
   exact bridge has yet been located; absence of a located bridge alone is
   not substantive eligibility.
3. Formal scope: a Lean endpoint must use literal weak tuples or a proved
   bijective reindex, actual tuple sums/source binomial coefficients and
   odd integer powers. An abstract assumed (1) does not certify the source.
4. Source version: exact arXiv3.1 read, journal indexed text read, but actual
   journal PDF visual comparison is still pending. Fresh MathDB open/empty
   status is recorded only as a status fact, never novelty evidence.

No manuscript, acceptance, external posting or numerical-evidence credit.
