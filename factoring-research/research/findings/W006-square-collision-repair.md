# W006 square-first collision selection: constructive recovery repair

2026-10-08. NEW parent derivation, separate from the already-launched original
batch review. PROVISIONAL until independently reviewed. Do not silently replace
the original brief or claim that its current reviewer has checked this repair.
No code or experiment ran. No improvement over established factoring bounds.

## The gap being removed

The original batch detector could stop at a full gcd caused by a globally equal
pair, even when another pair would split N. Its second-moment existence argument
therefore did not by itself establish recovery. Instead of bounding away global
duplicates, change what is selected and how it is decoded.

Assume N=pq for distinct odd primes. Let x_i,y_j be independent samples in H_N
from the same sign-equivariant map applied to uniform H_N, conditioned only on
sign-invariant survival. Do NOT filter survivors according to whether a trial
gcd(u-1,N) succeeded: that depends on the signs needed below. The fixed
denominator-failure rule is invariant and is permitted. Early proper factors
may terminate the entire computation successfully.

Set X_i=x_i^2 and Y_j=y_j^2. Construct P(T)=product_i(T-X_i), use monic remainder
trees to evaluate P(Y_j), and select the first j with nonunit norm by scalar gcd.
If that gcd is proper, return it. If full N, scan the K leaves in fixed order,
using gcd(N,Norm(Y_j-X_i)). A proper gcd returns a factor. Select the first full
leaf if encountered, or remember it while checking the other leaves; either
fixed policy is allowed if it uses squares only. If a full product had neither
a proper nor a full leaf, every leaf would be a unit, a contradiction.
Only one such O(K) scan is required.

For a selected full leaf, form z=x_i*bar(y_j). No inversion oracle is used:
Norm(y_j)=1. The local norm-difference lemma proves x_i^2=y_j^2 in S_p and S_q.
Thus z^2=1 in S_N. In H_p the only elements whose square is 1 are the scalar
+/-1, both in the split and nonsplit cases. Therefore z=u+iv has v=0 mod N
and u^2=1 mod N. Compute gcd(u-1,N); a proper value is the factor.

## Why full collisions are useful after selection

The kernel of squaring H_N->H_N is precisely the four scalar roots of unity
with local signs (+,+),(+,-),(-,+),(-,-). A sign-invariant sample law is constant
on each such four-element fiber. Conditional on its square, each original
sample therefore has four equally likely signs. For independent samples,
these signs remain independent conditional on the entire arrays of squares.

All polynomial operations, the selected query and the selected leaf depend
only on those square arrays. For any selected pair from the two independently
sampled lists, the ratio signs are consequently uniform over those four
patterns, even if its squares are equal globally or duplicate many other
entries. Exactly two patterns give a proper gcd(u-1,N). Conditional on a
full selected collision, extraction succeeds with probability **1/2**.

The failed extraction is retained as a failed trial; it is not erased or
resampled for free. For more than two distinct primes the sign count changes,
and for repeated prime powers a full norm gcd need not imply full coordinate
equality: norm valuations can double. No general-input extension is asserted.

## Paid collision probability

Let nu_p be the local distribution of X=x^2 and
d_p=sum_t nu_p(t)^2. For K independent samples in each list, let Z be the
number of p-colliding cross pairs. Then

    E Z=K^2*d_p,
    E Z^2 <= K^2*d_p + 2*K^3*d_p^(3/2) + K^4*d_p^2.

The terms are respectively identical pairs, pairs sharing one endpoint, and
disjoint pairs. The cubic moment is at most d_p^(3/2). For
K=ceil(d_p^(-1/2)), E Z is bounded below by 1 and the ratio
(E Z)^2/E Z^2 is bounded below by a positive universal constant.
Cauchy-Schwarz on Z*1[Z>0] gives a constant lower bound on P[Z>0].

Whenever there is any p-collision, the ordered evaluation finds some nonunit
query (possibly caused by q first). Its proper case succeeds outright; its
full case has conditional extraction probability 1/2 by square-only selection.
Hence collision existence now feeds an actual paid recovery algorithm with
constant loss. No local independence between p and q is needed for this
decoding argument beyond the full root-sign invariance and independent samples.
A fixed algebraic map of a uniform CRT input supplies those conditions.

For the original sign-invariant local law mu_p of x, squaring merges precisely
the pairs {x,-x}; therefore d_p=2*c_p, where c_p=sum mu_p(x)^2.
Uniform H_p has d_p=2/m_p. This only changes birthday constants, not exponents.
The previous concentration-versus-cost threshold remains the same up to
constants after charging survival and every map evaluation.

Unknown d_p does not grant an oracle for K. A doubling schedule is a possible
control, and its work/success bound must include fresh paid batches, survival,
caps, and failure probability. The uniform comparator reaches K=Theta(sqrt(p))
with N^(1/4)*polylog N cost for balanced semiprimes if the fast ring polynomial
arithmetic audit succeeds. This is already a known scale, not the research goal.

## Next independent obligation

The original batch task is still useful and remains live. Its monic-arithmetic
cost and probability audits apply as inputs, but this new square-selection
proof needs its own explicit review before being accepted. Do not duplicate
the running task merely to obtain a second report.

The main constructive target is now sharper: design an explicitly cheap map
whose local second moment grows faster than the square of its full cost, with
adequate survival. The detector and square decoder specify the computation
that would consume such a map; they do not supply that map's useful mass.

