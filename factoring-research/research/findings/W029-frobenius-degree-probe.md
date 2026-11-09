# W029: a sparse Frobenius polynomial and the black-box information it loses

Subsequent status: [independent audit and parent disposition](W029-parent-disposition.md)
accept the semiprime identities and give an exact zero-count formula.
The normalized derivative is already the companion circuit's scalar data:
H_N=(F_N-G_N)/(2x) at unit x. Its proposed information gain and any new
factoring improvement are rejected. Original derivation retained below.

Parent derivation, 2026-10-08 local. No experiment or independent review.
Verified complete factoring improvement: **NONE**. This tests a different
consumer from W028's requested central coefficient.

## 1. A short circuit whose component degrees encode the factors

Define integer polynomials F_r(X),G_r(X) by

    (1+a)^r = F_r(X)+a*G_r(X),   a^2=1-4X.

Binary exponentiation of the pair (1,1), with multiplication
(F,G)*(U,V)=(FU+(1-4X)GV,FV+GU), gives a straight-line circuit of O(log r)
gates. This extends W028's power-of-two Newton circuit to arbitrary r.
Over the integers, F_r=sum_j binom(r,2j)*(1-4X)^j.

Take N=pq with distinct odd primes p<q. In characteristic p, conjugating
the two branches and using Frobenius gives

    F_N(X) = F_q(X)^p = F_q(X^p) modulo p.

Similarly, F_N=F_p(X^q) modulo q. Since the highest coefficient of F_q
is q*(-4)^((q-1)/2), nonzero modulo p, the exact component degrees are

    deg_(mod p) F_N = (N-p)/2,
    deg_(mod q) F_N = (N-q)/2.

The largest nonzero coefficient index r over Z/NZ is therefore (N-p)/2,
and its coefficient is zero modulo q and nonzero modulo p. Its gcd with N
is q; alternatively, N-2r=p. Thus an acquired leading nonzero coefficient
would split N immediately. Degree over Z is known without doing this job,
and substituting that integer degree would be an error.

There are at most (q+1)/2 nonzero monomials modulo p and at most (p+1)/2
modulo q. Their union bounds the composite-ring support by O(p+q), much
less than the degree when the factors are balanced. This suggested sparse
interpolation from cheap evaluations of the O(log N)-gate circuit.

## 2. Why ordinary modular evaluations do not recover that support

For every x in F_p, x^p=x, so the evaluation functions of F_q(X^p) and
F_q(X) are identical. Their formal degrees and exponent supports are
different. Thus the high-degree Frobenius support cannot be inferred from
evaluations in F_p alone. Over Z/NZ, all base-ring evaluations inherit this
component aliasing. Derivatives provide no rescue: F_N' is identically zero
modulo N, and the first useful Hasse derivatives again require paid access
to high-index coefficients.

This is an exact information loss for that observation model, not a lower
bound for the circuit representation or for factoring. The circuit still
contains symbolic structure that evaluations discard.

Even assuming an extension ring and interpolation operations where all
relevant exponent collisions are avoided, a conventional full sparse
reconstruction would acquire on the order of p+q terms in the worst bound
above. That is order sqrt(N) for balanced factors before interpolation,
ring construction, exponent recovery and nonunit failures are priced.
Some coefficients can vanish or coincide, so this is an envelope for the
proposed reconstruction, not an unconditional support-size lower bound.
Discrete logarithms or suitably high-order evaluation points must not be
silently assumed in a composite-ring interpolation call.

## 3. What different computation would be required

The worthwhile target would be symbolic leading-degree extraction directly
from this particular short circuit, rather than full interpolation of its
value function. Binary powering alone does not solve it: reductions modulo
N create cancellations and different component degrees. Assigning formal
degrees to circuit gates by max/sum only gives an upper bound and misses
precisely those cancellations. A valuation oracle or a free high-order Hasse
derivative would simply restate the missing operation.

The generic sparse-interpolation mechanism is therefore rejected as a
factoring improvement. This finding gives both a concrete factor-bearing
invariant and the exact reason the cheap observation method loses it.
No success probability or complete time bound is asserted. Pursue a symbolic
consumer only if its state and cancellation operations can actually be given
and costed; otherwise return to a materially different computation.

## 4. A concrete symbolic operation: divide the derivative before reduction

The vanishing derivative suggests retaining one layer of integer divisibility
instead of observing only base-ring values. Differentiating the defining
integer identity gives the exact identity

    F_r'(X) = -2*r*G_(r-1)(X).

Thus H_N=F_N'/N is an integer polynomial whose value modulo N is computable
by the same pair-powering circuit in O(log N) ring operations:

    H_N(x) = -2*G_(N-1)(x) modulo N.

No modular division by N is being performed. This is an actual symbolic
normalization; it avoids both coefficient expansion and the need to represent
the derivative modulo N^2. It does not itself provide a splitting probability.

There is a precise comparator for its gcd test. Work modulo an odd prime
p dividing N, exclude x=0 and 1-4x=0, and in a splitting field put
a^2=1-4x, u=1+a, v=1-a, t=u/v. Both u and v are units. Let
chi be the quadratic character of 1-4x. Frobenius either fixes u,v or
exchanges them, so t belongs respectively to the split group of order p-1
or the norm-one group of order p+1. Since a and 2 are units,

    H_N(x)=0  iff  t^(N-1)=1.

For N=pq, reducing N-1 modulo p-chi gives chi*q-1; equivalently the
condition is t^(q-chi)=1. The normalized derivative therefore supplies
exactly a public-exponent order test in this parametrization. Its potential
zero set is the subgroup of size gcd(N-1,p-chi). This is a subgroup count,
not the probability under x sampling; x maps to unordered reciprocal t
pairs and the exceptional values have been excluded. No bound on the
subgroup fraction is supplied for arbitrary factors.

This normalization genuinely recovers information killed by ordinary
differentiation, but its first scalar consumer returns to a known order
condition. It does not acquire the formal leading degree or the hidden
Frobenius exponent. A different normalized symbolic invariant would need
an equally explicit computation and a new argument for useful component
separation; the existence of this normalization is not such an argument.

Deduplication: the elementary square-weight quadratic parameterization was
reconsidered in this turn and matched W021 section B exactly. Its existing
coverage-cost objection remains; no repeat experiment or new candidate is
counted for that idea. The earlier W021 Frobenius-support proposal is also
an antecedent of sections 1–2 here. W029's additional content is the exact
component degree and this explicitly computed normalized-derivative test,
not a new claim to the Frobenius support identity itself.
