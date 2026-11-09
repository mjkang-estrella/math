# W013 continuation — consume approximation errors through hidden periods

2026-10-08. Parent construction. No new factoring bound or novelty claim.
This changes the consumer of a reciprocal approximation: allow a large
error interval and search it with shared modular powers, rather than
enumerate its residues. The current W013 polynomial-filter audit completed
while this note was developed; its exact-equation extraction is consistent
with the full-collision handling below.

## 1. Exact transfer, for polynomial approximations of any fixed degree

Let p be a prime divisor of N and Q=N/p. A public block is
X<=x<X+H. Let q>=1 be an integer, A(h) an integer polynomial of fixed
degree d, and E>=0 an integer certified to satisfy

    |A(h)-q*N/(X+h)|<=E for integer 0<=h<H.

If p=X+h is in this block, define the integer error

    e=A(p-X)-q*Q,             |e|<=E,
    D=A(1-X)-q*N.

Since p=1 modulo p-1 and Q=N modulo p-1,

    D=e (mod p-1).                                      (1)

For any unit alpha modulo N this implies alpha^D=alpha^e modulo p.
Negative exponents use a paid inverse modulo N. No factorization or
primality of the auxiliary denominator q is required. This is the actual
way in which the modular-root gate of the original filter can be bypassed.

## 2. Shared baby table, including every full-collision branch

Suppose K public blocks/certificates cover a prime factor, with E_i and D_i
as above. Take a supplied unit alpha with ord_N(alpha)>=B, B>=1. Acquiring
such an alpha is separate paid work, not supplied hidden-factor advice.

Build beta_j=alpha^j for 0<=j<B. For each 1<=j<B, test gcd(beta_j-1,N).
A nonunit gives a proper factor because ord_N(alpha)>=B excludes beta_j=1
modulo N. If all are units, ord_p(alpha)>=B for EVERY prime p dividing N.
This is a simpler sufficient check than all pairwise baby differences.

For certificate i, write L_i=2E_i+1 and generate the tagged giant values

    gamma_(i,k)=alpha^(D_i+E_i-k*B),
    0<=k<ceil(L_i/B).

The true e gives e+E_i=kB+j with 0<=j<B and gamma_(i,k)=beta_j modulo p.
The last block may include extra j; they cannot hide the true pair.

First sort/match modulo N. Each giant has at most one global baby match.
For every global match with tagged (i,k,j), set e'=kB+j-E_i and find the
integer roots in the block of

    F_(i,e')(x)=x*(A_i(x-X_i)-e')-q_i*N.               (2)

Test each root as a proper divisor. This polynomial is nonzero, because
F(0)=-q_i*N != 0, and has fixed degree at most d+1. Exact fixed-degree
integer-root isolation has polynomial cost in coefficient bit lengths;
it is not a scan through the whole block. If a true prime collision was
also a global collision, uniqueness of the baby powers modulo p forces
j to be the true j, so (2) recovers p. Global matching with a wrong e does
not imply a factor, and its failed root check remains charged.

After these checks, remove globally matching giants. Deduplicate the
remaining residues if desired, preserving tags/counts for accounting.
Build the monic product of (Y-gamma) over the remaining values and evaluate
it at all beta_j. A nonunit value supplies a prime-component collision.
If the product gcd is N, inspect its factors (one product-tree descent or
one linear scan). Every leaf difference is nonzero modulo N, so a nonunit
leaf gcd is proper. At most one such recovery scan is needed before success.
The true collision cannot have been removed unsuccessfully, by the previous
paragraph. This proves the conditional coverage consumer, not the existence
of a faster certificate generator.

With G=sum_i ceil((2E_i+1)/B), the cost is

    (B+G+K)*poly(log N) + paid certificate/base acquisition, (3)

provided degree is fixed and all coefficients, exponents, parameters and
list lengths have the stated polynomial bit bounds. Product trees, modular
powers, comparisons, gcds, root checks, all tags and storage are included.
Polynomial multiplication gives the near-linear list cost; it is not a
unit-cost black box. Exponent arithmetic costs its actual bit length.
Up to logarithmic factors the useful envelope is

    K+B+(sum_i (2E_i+1))/B,

so optimizing B gives K+sqrt(sum_i(2E_i+1)). A table with too small order
does not license either removing global collisions or an uncharged restart.

## 3. Linear approximations recover the known one-fifth scale

For a block near X~sqrt(N), use A(h)=a_0+a_1*h. Continued fractions give
1<=q<=Q0 and |q*(-N/X^2)-a_1|<=1/Q0; choose a_0 nearest q*N/X.
The exact reciprocal remainder gives

    E=O(1+H/Q0+Q0*H^2/X).

Take Q0~sqrt(X/H). Then E=O(1+H^(3/2)/sqrt(X)). For K~X/H blocks,
the dominant consumer envelope is

    X/H + (X*H)^(1/4),

balanced at H~X^(3/5), cost X^(2/5)=N^(1/5). The q here is much smaller
than H. Constant error and modular-root enumeration were unnecessary
restrictions in the earlier proposed consumer.

For general dyadic X, the curvature term is Q0*N*H^2/X^3. The choices
H~X*N^(-1/5), Q0~X*N^(-2/5) produce E=O(N^(1/5)) and O(N^(1/5)) blocks
per dyadic interval when X>=N^(2/5).
Smaller factors can be handled by the known square-root-cost interval
product method at threshold N^(2/5), also N^(1/5) scale. All dyadic ranges,
rounding, base acquisition and coefficient sizes still need full accounting.

This is not new factoring machinery. After deriving the transfer, the parent
read Harvey's primary §§2.2–2.4, §3 discussion, Algorithm 4.2 and its proof:
https://arxiv.org/html/2010.05450 . His algorithm already shares one search
across linear-combination certificates, checks small component orders, handles
global matches by quadratic recovery and then removes them for batch gcds.
For A=a_0-a_1*h, our equation is a_1*p+q*Q=a_0+a_1*X-e, the same type of
linear-combination certificate. No claim that this note improves his bound
or reproduces its precise logarithmic factors is made.

Higher fixed degree with only weighted simultaneous-approximation guarantees
does not improve this envelope. The C audit corrected a tolerance-saturation
error in the original degree-four entry below. Let D_d=d(d+1)/2. To make each scaled
coefficient error at most order E/H^j, the usual pigeonhole budget is
q<=O_d(H^D_d/E^d), in the regime these tolerances are small. Keeping the
Taylor error at most E on a balanced range leads to

    E~H^((d+2)/2)/X^(d/(d+1)).

Substitution in (3), ignoring no claimed gain from coefficient correlation,
gives the balanced optimized N-exponent

    (d^2+d+2)/(2*(d+1)*(d+4)),

The first three entries are 1/5, 2/9, 1/4 for d=1,2,3; the third is a
constant-tolerance boundary. The formal fourth entry 11/40 is INVALID as a
sufficient budget: its E/H grows like X^(1/10), violating the small-tolerance
regime. The general box count is instead

    q<=O_d(product_(j=1)^d max(1,H^j/E)).

With the first coordinate saturated for d=4, q<=O(H^9/E^3) and the Taylor
budget gives E~H^(7/2)/X. Balancing E~X/H yields H~X^(4/9), E~X^(5/9),
and cost N^(5/18), still worse than the linear recipe. These are optimizations
of sufficient budgets, not lower bounds on special coefficients or factoring.
A constructive fixed-dimensional approximation routine and every boundary
regime are obligations, not supplied by mere pigeonholing.

## 4. A different repair: rational approximants and their exact normal form

The most natural way to escape W013's curvature obstruction is a rational
approximant A(x)/B(x), not another integer quartic. Suppose B has integer
coefficients. Divide by the monic polynomial x:

    B(x)=x*C(x)+b,       b=B(0),
    A'(x)=A(x)-N*C(x).

This is cheap polynomial coefficient arithmetic. At a prime factor p,

    A(p)-B(p)*Q = A'(p)-b*Q.                           (4)

Moreover the public exponent and integer recovery polynomial are unchanged:

    A(1)-N*B(1) = A'(1)-b*N,
    x*(A(x)-e)-N*B(x) = x*(A'(x)-e)-b*N.              (5)

Thus any integer-polynomial numerator/denominator presentation reduces to
the previous constant-denominator certificate, with its actual coefficient
sizes and error numerator preserved. In block coordinates h, divide B(h)
by X+h, so the surviving constant is B(-X), not B(0).

A tiny rational error is not yet a tiny searchable exponent error. When B(p)!=0,

    e=B(p)*(A(p)/B(p)-N/p).

The denominator must be nonzero on the claimed ratio-approximation domain,
and its magnitude must be paid in the error interval. Integer residuals (4)
still make sense at B(p)=0, but the undefined ratio supplies no bound there.
For the exact
choice A=N, B=x, normalization gives A'=0,b=0. All exponents match trivially
and the recovery polynomial for e=0 is identically zero. It supplies no
localization. Generally that degeneracy occurs exactly when b=0 and A' is
the constant polynomial e. If b!=0, the nonzero constant term rules it out.
For b<0, negate A', b, e and D to enter the q>=1 consumer. For b=0 with
nonconstant A', a separate q=0 extension uses the nonzero polynomial
x*(A'-e), excluding x=0 by the block/proper-factor tests. For b=0 and
constant A', exclude the certificate from coverage; do not remove a true
global match after pretending its zero polynomial has a finite root list.

Example: A=N+t, B=x+s normalizes to A'=t,b=s. The actual error is t-s*Q.
When s=0 it is the constant t for every factor and gives no information;
when s!=0 the cofactor uncertainty survives. Near-exact rationality alone
does not remove the search. This is a representation identity, not a proof
that all possible rationally generated certificates are poor.

## 5. Next gate

The shared exponent consumer genuinely replaces per-error enumeration and
known-modulus root acquisition, but recovers known-scale work. To improve
it one must actually reduce K or total error with paid coverage, or exploit
a specific implicit structure among the targets in (3). Merely increasing
degree, shrinking a rational approximation error before multiplying B, or
discarding full collisions does not do that. The rational normal form's
pointwise integer identities are proved in Factoring/ResidualNormalization.lean;
they assert no complexity gain or implementation of the complete consumer.
Independent audit will check the transfer, extraction, optimized budgets
and normalization. No numerical factoring-performance run is selected.
