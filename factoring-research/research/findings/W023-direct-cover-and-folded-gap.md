# W023: direct annihilators and the source of some folded witnesses

Parent derivations, 2026-10-08 local. No numerical experiment was run. These
are scoped symbolic comparisons, not independently accepted new algorithms.
Verified new complete factoring improvement: **NONE**.

## 1. Enumerate a factor through a quadratic annihilator

For N=pq and 2<=i<=L<N, define

    F_N(i)=(i-1)(N-i)=-i^2+(N+1)i-N.

At i=p it equals p(p-1)(q-1), a positive annihilator of every unit modulo
the squarefree semiprime N. Every candidate exponent is nonzero. Thus W021's
supplied quadratic-product primitive and W020's recovery can be composed
with this explicit coverage; there is no unknown coefficient or root input.

This is a real computation, but the comparison rejects it: its main cost is
L^(3/4+epsilon), whereas the ordinary product of the integers 2,...,L modulo
N can be evaluated with the classical product-tree/block method in soft
O(sqrt L) ring work. The latter directly covers the same factor and also
works without the semiprime promise. Setup, bit widths and gcd localization
are polynomial logarithmic overheads in both comparisons. For L~sqrt N the
quadratic route costs N^(3/8+epsilon), already worse than N^(1/4).

The failed assumption was that a cheaply supplied quadratic annihilator
would beat a linear factor cover. It does not. A useful quadratic-phase
application must cover inputs without enumerating a range already searchable
by that simpler product.

There is a narrow algebraic classification, with an elementary parent proof.
If one fixed F(Y,X) in Z[Y,X] satisfies BOTH p-1 | F(pq,p) and q-1 | F(pq,p)
for every pair of distinct odd primes, then

    F(Y,X)=(X-1)(X-Y) H(Y,X),  H in Z[Y,X].

Fix q and let p grow: reduction modulo p-1 shows that the fixed integer
F(q,1) is divisible by unbounded p-1, hence is zero. Infinitely many q give
F(Y,1)=0. Similarly, fix p and let q grow to obtain F(p,p)=0 and therefore
F(Y,Y)=0. Divide by X-1, then evaluate at X=Y; the integral-domain identity
(Y-1)H0(Y,Y)=0 implies the second factor X-Y. Monic polynomial division
keeps all coefficients integral.

This does NOT classify N-dependent floors/roots/coefficients, restricted
input families or bases, other groups, or other algorithms. It does not
prove that a multiplier H cannot add useful witnesses. It independently
explains the simple polynomial above; it does not import the unread broad
claims of W014's second review.

## 2. A direct factor-sum approximation also has a simpler comparator

Write S=p+q, D=q-p>=0. Then S^2-D^2=4N. For any public integer a,

    2a*S=a^2+4N+D^2-(S-a)^2.

This would enumerate a quadratic D and a small correction S-a to obtain a
multiple of phi(N). But if D<=H, then

    0<=S-2sqrt(N)=D^2/(S+2sqrt(N))<=H^2/(4sqrt(N)).

The sum S already lies in a public integer interval of length
O(1+H^2/sqrt N). A linear annihilator/collision search over that interval
has soft cost O(1+H/N^(1/4)), before its standard recovery overhead. The
two-parameter quadratic representation saves no work on this same promise.
Exact integer square roots and outward-rounded endpoints suffice; no real
precision oracle is intended.

## 3. Close gaps can create support AFTER cyclic folding

Let q=p+Delta, with p,q distinct odd primes, c an integer, and

    C=(1+cX)^N in (Z/NZ)[X]/(X^r-1).

Modulo p, two applications of Frobenius give exactly

    C=(1+cX^(p^2)) (1+cX^p)^Delta.

If gcd(p,r)=1 and a=p mod r, undo the permutation X -> X^a. The resulting
polynomial modulo p is

    (1+cX^a)(1+cX)^Delta.

Its support is contained in the two cyclic intervals [0,Delta] and
[a,a+Delta], hence has at most 2(Delta+1) coordinates. Cancellation can only
shrink this upper bound. If a=1 it becomes (1+cX)^(Delta+1). If a=-1 and
c=1 it becomes X^(-1)(1+X)^(Delta+1). These cases use at most Delta+2
coordinates. This is a different reason for sparse folded support from the
unfolded multiples-of-p rule; that original rule is not preserved by folding.

For the ALREADY FROZEN W021 case N=143=11*13, r=5, c=1, a=1, Delta=2,
C modulo 11 is (1+X)^3. Its X^4 coefficient is zero. Modulo 13,

    C=(1+X^4)/(1+X^3)^2.

The denominator is a unit because r is odd. Put y=X^3, so X^4=y^3 and
y^5=1. Then

    (1+y)^(-2)=(-3+y+y^2-3y^3+5y^4)/4.

The y^3 coefficient after multiplying by 1+y^3 is -3/2=5 modulo 13.
Thus the raw X^4 coefficient has gcd 11 with 143, exactly as the retained
W021 certificate reports. This paragraph is symbolic explanation of that
existing case, not a new run. It does not explain every recorded witness.

Forced zeros need not distinguish the two CRT components. General large
Delta fills a short cyclic ring. No random-coordinate probability follows.
Moreover, this newly explained family already admits a scalar comparison:

    N-1-Delta=(p-1)(q+1).

Searching a promised Delta interval of length H has a linear phase with
soft square-root cost; for close balanced factors the direct S interval in
section 2 is stronger. The folded implementation supplies no improved
complexity on the explained family.

## Consequence for the next computation

These attempts remove neither the generic factor-cover cost nor the
coefficient-acquisition cost. They rule out two specific tempting speed
claims and explain why tiny folded successes need input-family accounting.
The next construction changes the representation of root charts and of the
binomial coefficient recursion; see W023.md. None of these comparisons is
a lower bound for factoring.
