# W030: the unbalanced acquisition frontier and a public rescaling

Parent derivation, 2026-10-08 local. Symbolic work only; no experiment.
**Verified complete factoring improvement: NONE.** The aggregate kernel
algorithm in this calculation is hypothetical. Even granting its stated
cost does not give a complete one-sixth factoring bound with these inputs.

## 1. Include the long input table

Let the smaller prime factor p lie in a public dyadic range [P,2P], with
q=N/p. Suppress constants and polynomial logarithmic factors in this
section. The short-weight cover has the balanced-width parameters

    U ~ sqrt(M*N)/P,   V ~ P*sqrt(M/N),   U*V ~ M,
    W ~ sqrt(N*M),     T ~ 1+sqrt(N)/M^(3/2).

These refer to the top stratum; geometric valuation sums preserve the
displayed powers. Assume, provisionally, a complete supplied-table
consumer of cost O~(U+V+sqrt(U*V*T)), including extraction and success
overhead. W030 DOES NOT implement that consumer. Its cost for p<=sqrt(N)
contains

    sqrt(M)*sqrt(N)/P + sqrt(M) + N^(1/4)*M^(-1/4).

Balancing the first and last terms gives

    M = P^(4/3)*N^(-1/3),
    cost = (N/P)^(1/3),
    V = P^(5/3)*N^(-2/3).

The interior range V>=1 begins at P=N^(2/5). At P=sqrt(N) this reproduces
the conditional balanced exponent 1/6. At P=N^(2/5), however, the table
and consumer terms reach N^(1/5). A standard small-factor block-product
comparison costs O~(sqrt(P)). Its crossing with (N/P)^(1/3) occurs at
exactly P=N^(2/5). Taking the better of these two displayed branches
therefore has a worst exponent 1/5.

This is a cost envelope of a proposed composition, not a lower bound for
factoring or for all uses of the root representation. In particular no
uniform prime distribution assertion is needed to locate its formal
maximum. Constants, integer ceilings and neighboring allowed prime
powers are suppressed only in this exponent calculation. The limiting
V=1 expression has U=M and is NOT literally an admissible W022 rectangle.
At the boundary choose, for example, U=floor(M/2), V=ceil(M/U), for
sufficiently large M: both are <M and the width and cost change only by
constant factors. Small targets use the imported finite fallback. Allowed
prime-power rounding costs at most the public polylogarithmic base.

## 2. A real coordinate change that balances the tables

The long table can be shortened without knowing p, but the corresponding
root width must also be recomputed. Choose a positive integer

    s ~ N/P^2

from the public range. For each public base ell choose s=ceil(N/P^2), or
s+1 if needed to ensure ell does not divide s. This is a constant-factor
change when P<=sqrt(N). It does not assume the prime schedule happens to
avoid all divisors of one fixed s. Any proper gcd(s,N) can be returned,
but that is not required by the root-table construction.

Take 2<=A<M and B=ceil(M/A)<M, both on the scale sqrt(M). Apply the
ordinary sorted-residue pigeonhole proof to the unit s*p/q modulo M.
Two residues supply positive a<=A and signed nonzero b with |b|<=B such
that

    M divides s*a*p-b*q.

Put u=s*a, v=b and S=s*a*p+b*q. Then

    S^2 = 4*N*s*a*b modulo M^2,
    E = s*a+N*b-S = (p-1)*(b*q-s*a).

Thus the two-table algebra applies with radicand N*s, row labels s*a,
and column labels N*b. It does not substitute N*s for the factoring
input in the exponent identity. Since ell does not divide s, the equal
valuation stripping argument for a,b is unchanged. The primitive true
leaf has

    E = s*a*(p-1)^2 modulo ell,

so the public W024 witness-retention condition is the same. Filter table
labels must encode the actual row weight s*a.

For p in [P,2P], q<=N/P and s*p=O(N/P). Hence a public magnitude bound is

    W_s = O((N/P)*sqrt(M)),
    T_s = O~(1+(N/P)/M^(3/2)).

The two coordinate tables now each have O(sqrt(M)) entries. Granting the
same hypothetical consumer, the full leading cost becomes

    sqrt(M)+(N/P)^(1/2)*M^(-1/4).

It balances at M=(N/P)^(2/3) and again costs (N/P)^(1/3). At P=N^(2/5)
this uses M=N^(2/5), table length N^(1/5), and width W_s on the scale
M^2=N^(4/5). The previous unscaled optimum used M=N^(1/5) and a long
table of that size. The two constructions arrive at the same exponent
by different inputs and widths.

All integers remain polynomially bounded in N. Base and range schedules,
valuation strata, root acquisition, filtering, labels and localization
must still be included in a complete algorithm; none is advice from p.
The new scaled construction is independently reviewable and is not
claimed to have been checked by the earlier root-table audit.

## 3. What failed and what would change the conclusion

The failed assumption was that balanced root-table input size could be
used uniformly over every factor range. Public rescaling is an actual
repair of that size assumption, but its increased geometric width
removes the hoped-for complete exponent saving in this model.

A useful next computation must do at least one of the following with a
paid construction: consume the long root table implicitly, cover the
transition range with a smaller width than this rescaling supplies, or
improve the small-factor branch. Merely supplying the balanced digit
kernel target is insufficient. None of these conditions is a global
necessity for factoring; a different starting mechanism can bypass them.

The cheap decisive validation is symbolic: check the sorted-residue
cover and nonzero-filter identity for scaled weights; then optimize the
complete U+V+sqrt(UVT) expressions with integer-domain repairs. No
timing run can establish the unimplemented aggregate cost.
