# W032: a paid canonical finite-difference filter and its exact residual

Parent construction, 2026-10-08. **Independent review pending.** No numerical
experiment. Verified complete factoring improvement: **NONE**.

The proposed computation tries to simplify many scalar digits together:
sample a canonical arithmetic progression, then cancel their polynomial
trend with a finite-difference stencil. This actually changes the gcd
argument. The calculation below identifies what survives, rather than
assuming that cancellation isolates a hidden-factor signal.

## Exact canonical filter

Assume leastprime(N)>2R+1, R>=1. Set D=4^R(2R+1)! and m=2R+1. Choose
an integer a0 such that all inputs

    a_i=a0+iD,   0<=i<=m,

lie in [0,N) and are units. Initial nonunit inputs are ordinary gcd exits,
separate from this filter. Evaluate the already specified scalar digits
d_R(a_i) and form

    Z=sum_(i=0..m) (-1)^(m-i)*binom(m,i)*d_R(a_i) mod N.

One may instead use the reviewed exact floor-polynomial evaluator. Charge
m+1 point evaluations, all coefficient/precision work, binomial weights,
gcd checks, and the final gcd(Z,N). No hidden factor chooses a0 or D.

Use the accepted common-denominator representation. Since every a_i is
congruent to a0 modulo D, the two residues

    e=C_R(a_i^2) mod D,
    h=(-F(N,a_i)*N^(-(2R+1))) mod D

are constant across the stencil. Here C_k(x)=D G_k(x); the inverse in h
is modulo D, where N is a unit, never an inverse of N modulo N. Define
the rational polynomials in the integer variable i

    J(i)=(C_R(a_i^2)-e)/D,
    Q(i)=e/D+hN/D+sum_(k<R) N^(2k-2R)*G_k(a_i^2).

J(i) is an integer at every integer i in this residue class and has degree
at most 2R. Q(i) has degree at most 2R-2 (constant for R=1). The accepted
formula is

    d_R(a_i)=J(i)+floor(Q(i)) mod N.

Both degree-m finite differences vanish over Q. Thus Z is congruent modulo
N to the actual integer

    c=Delta^m floor(Q)(0)=-Delta^m {Q}(0),

where {x}=x-floor(x) lies in [0,1), also for negative x. The positive
binomial weights and the negative binomial weights each sum to 2^(m-1).
Consequently

    |c| < 2^(m-1) = 4^R.                              (1)

This bound does not need independence or equidistribution of the rounding
errors. Canonicalizing each d_R changes its integer lift by a multiple of
N, so gcd(Z,N)=gcd(c,N) exactly.

If every prime divisor of N is greater than 4^R, a nonzero c has gcd 1;
c=0 has gcd N. The filter therefore cannot give a proper factor on that
branch. For other inputs any prime it exposes is smaller than 4^R.
This statement is about the filtered gcd, not the original individual
digits, their own gcds, or an arbitrary different use of the observed data.

## Canonical width makes the residual small asymptotically

The full D-spaced stencil inside [0,N) requires mD<N. Since

    log D = R log4 + log((2R+1)!) = Theta(R log(R+1)),

this implies R=O(log N/log log N) when R grows; bounded R is easier.
It follows that 4^R=N^o(1) uniformly along such large admissible inputs.
For every fixed epsilon>0, sufficiently large inputs with leastprime(N)
at least N^epsilon therefore have no proper factor from this filter.
In particular it supplies no large balanced-semiprime splitting guarantee.
This conclusion does not say such stencils always exist or consist of units.
If the width guard fails, this proposed canonical-stencil experiment cannot
be invoked; replacing a_i by its residue modulo N breaks the fixed-D-class
argument in general. Higher lifts are a different distribution already
treated separately.

## Cost and constructive consequence

The scalar route supplies each point in soft O((R+1)*poly(log N)) bit work.
The whole displayed filter conservatively costs soft O((R+1)^2*poly(log N)),
including O(R) weights of O(R) bits and their modular combination. Computing
D has O(R log(R+1)) output bits, which is O(log N) on the width-legal branch.
The alternative fixed-R floor evaluator can remove powering stages but
does not change the exact bound (1).

The hoped-for saved work was to turn the complicated carry sequence into
a simpler factor-selective statistic. This filter does simplify it, but
it removes the polynomial component and leaves only bounded rounding noise.
No factor-selective law has been produced. Reject this particular high-order
filter as a route to large-factor amplification once the displayed size
condition holds.

A materially different follow-up would keep a lower-order difference, or
use residue classes with a proved much smaller period than D while paying
for their acquisition. Then the polynomial part or variable carry labels
remain and need their own separating-count analysis. Neither alteration is
implicitly covered by this negative result. The decisive next validation
is symbolic: unit/canonical hypotheses, the exact floor decomposition,
strict binomial bound, asymptotic width implication, and all scope limits.
No overlapping numerical assay is authorized by this note.
