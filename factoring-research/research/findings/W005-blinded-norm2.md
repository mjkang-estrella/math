# W005 — blinded Norm2 from the outer square, with an explicit sampler

Date: 2026-10-08. **PROVISIONAL parent mechanism; independent review required.**
This changes the joint factoring wrapper, not the old standalone N,R-only
Norm2 contract. No assertion of a new best factoring bound or novelty.
It was developed while the other T3 reviews ran.

## Computation removed

The old reference finds u^2+v^2=5R mod N by two O(N)-length lists.
But the outer trial itself selected a unit x and R=x^2 mod N. It knows
the easy representation (x,2x). Passing this inward unchanged exposes the
root and invalidates the useful-root probability proof.

The proposal is to randomize that representation with an EXACTLY uniform
norm-one rotation, cheaply. The resulting auxiliary representation should be
independent of which root x in the R fiber was used. This supplies a new
joint sampler for factoring, not a free root or an N,R-only Norm2 algorithm.

## Actual algorithm

Assume gcd(N,30)=1, x a unit, R=x^2 mod N, and n=bitlength(N).

1. Sample a,b independently uniformly from {0,...,N-1}, using separately
   rejected n-bit words. Set h=a^2+b^2 mod N and d=gcd(h,N).
2. If 1<d<N, return the verified factor. If d=N, retry within the cap.
3. If d=1, compute h^(-1) mod N and

       c=(a^2-b^2)/h,  e=2ab/h,
       u=x*(c-2e),     v=x*(e+2c)     mod N.

   Return canonical u,v only, along with N,R, to the inner field/packet
   procedure. Do not pass x,a,b,c,e or their sampler tape to that procedure.

Then c^2+e^2=1 and u^2+v^2=5R mod N. This uses a constant number
of O(n)-bit modular operations per pair. Rejecting a or b outside range is
charged. For a fixed worst-case cap, use B=2*(n+1)^3 pair attempts and
finite caps on each raw-word rejection as specified below. A cap stop is a
failure, not a successful norm certificate.

For a simpler expected-cost variant, uniform sampling may use unbounded
rejection; the expected number of n-bit words per coordinate is <2.
The finite-raw-bit variant can allocate 2*(n+1) raw draws per coordinate
per pair, abandoning that pair if either coordinate never enters [0,N).
Conditional on entry, the coordinates remain exactly uniform. These
abandonments belong in the failure probability and cost.

The inner routine may depend on N,R,u,v and independent randomness, including
arbitrary adaptive filters of those values. The outer routine uses x only
to compare against a returned root. This interface restriction is substantive.

## Proposed exact independence proof

Work in S=(Z/NZ)[i], i^2=-1, with conjugation and norm. The accepted pair
xi=a+ib is uniform among units of S. Its rotation is xi/conjugate(xi).

The kernel of xi -> xi/conjugate(xi) is exactly the scalar units: if a
unit equals its conjugate, 2 invertible forces its i coefficient to zero.
Thus each image fiber has phi(N) members.

Surjectivity onto every c+ie with c^2+e^2=1 follows locally modulo p^k.
If 1+c is a unit, choose xi=(1+c)+ie, with norm 2(1+c).
Otherwise 1-c is a unit, and xi=e+i(1-c), with norm 2(1-c).
Both give the desired rotation. CRT proves existence globally; factors
are used only in this proof, never by the sampler. Hence the rotation is
uniform in the norm-one group, including repeated prime powers.

The element z_0=x(1+2i) has unit norm 5R. Multiplication by norm-one
elements acts freely and transitively on all z=u+iv of norm 5R:
the unique multiplier is z/z_0. Consequently the returned certificate is
uniform on that set for every fixed x in the root fiber. Its distribution
is exactly independent of x conditional on N,R.

Earlier rejected pairs, their count, and the factor/accepted/failure branch
depend on N and sampler randomness, not x. Even a bounded stopping rule
of the stated kind preserves the conditional uniform certificate law.
The final rotation tape must remain unavailable to the inner routine:
it would allow inversion back to x. No secrecy from the mathematical
algorithm or the outer verifier is assumed; this is a data-dependence
condition for the root returned by the inner subroutine.

## Paid sampling bound

For an odd p, the fraction of pairs with a^2+b^2 nonzero mod p is
(1-1/p)^2 if -1 is a square, and 1-1/p^2 otherwise. Prime-power lifts
have the same fraction. Therefore the unit-pair probability is at least

    product_(p|N) (1-1/p)^2 = (phi(N)/N)^2 >= 1/(n+1)^2.

For the last bound, order the r distinct primes increasingly and use
p_j>=j+1, giving product(1-1/p_j)>=1/(r+1), with r<=n.
No analytic prime theorem, factoring routine, smoothness or unproved
sampler theorem is used.

Expected pair count until a factor or a certificate is therefore polynomial
in n. With finite raw-word caps, the chance both coordinates are sampled
is at least (1-2^(-2(n+1)))^2, a constant near one; price this factor explicitly
rather than silently retaining the untruncated bound. The stated pair and
raw-word caps give worst-case polynomial work, while any exhaustion stays
in the failure denominator. Exact tail constants are for the independent
review; a near-one certificate probability is not necessary for the
old-gcd complete upper bound below.

## What changes in the factoring wrapper

Conditional on N,R and the complete INNER transcript (which excludes the
blinding tape), x should remain uniform on its 2^r roots, even with
repeated odd prime powers. Hence any inner root y splits with conditional
probability 1-2/2^r, as in the old reduction. Auxiliary norm certificates
are permitted because they are independent of that hidden root choice.

W004's algebra accepts any verified norm representation. Its two-field
selector and M=n^2 scans otherwise have polynomial per-trial bit work.
Replacing the Norm2 lists by the capped sampler therefore proposes a
polynomial-cost trial, under a CHANGED certificate distribution. It does
not inherit any unproved target-supply law from the old deterministic
representation. Field/packet failures, sampler exhaustion, raw words x>=N,
and x=0 remain failures; all proper gcds remain checked successes.

Even using only the original nonunit-x success mass >=1/(4sqrt(N)),
a polynomial-cost trial gives a conservative complete expected
O(sqrt(N_0)*poly(log N_0)) wrapper, after paid preprocessing and recursion.
This would improve the OLD W004 reference upper bound
O(N_0^(3/2)*poly(log N_0)), but does not improve trial division or the
established general factoring state of the art.

The actual new computational claim to validate is the cheap, root-choice-
independent auxiliary sampler. It removes a concrete setup cost and permits
cheap sampling/filtering of field constructions; it does not prove useful
packet supply. A finite distribution check can falsify implementation
mistakes, while the uniformity and full cost need the symbolic argument.
