# A distinct extension tested: local density after thinning the primes

This is a pre-nomination diagnostic, not a replacement for DEG or any prior frozen target. No novelty or substantial-contribution claim is made. It tests whether the normalized pair argument could yield a robust theorem for an arbitrary subset S of the primes from positive density in every fixed reduced progression alone. That direction is false, even for h(x)=(x-1)^2.

Let alpha=sqrt(2) and ||.|| denote distance to the nearest integer. Define

    S={p prime : ||alpha(p-1)^2|| >= 1/4},
    A_N={n in [N] : ||alpha n|| < 1/16}.

Irrational rotation equidistribution gives |A_N|/N -> 1/8. If a,b belong to A_N then ||alpha(a-b)||<1/8 by the triangle inequality on R/Z. Thus a-b cannot equal (p-1)^2 for any p in S, since the latter has phase distance at least 1/4. This is exact avoidance, not an asymptotic error estimate.

Nevertheless S has relative density 1/2 in every fixed reduced prime progression. Here is a derivation from an actual operative input already read, P `prop:prime-minor-arcs`, without treating congruence density as equidistribution by definition. Fix q,a with gcd(a,q)=1. For every fixed integer j!=0 expand the condition p=a mod q using its q additive characters. The resulting phases are

    j alpha(p-1)^2 + b p/q,

each of degree two with leading coefficient j alpha. In the source notation theta=(2!)^2 j alpha=4j sqrt(2). It is badly approximable with a constant depending on j: for a rational u/v near theta,

    |theta-u/v|=|32j^2 v^2-u^2|/[v^2 |theta+u/v|] >= c_j/v^2,

because the numerator is a nonzero integer. Fractions not near theta satisfy the same type of lower bound after decreasing c_j. Dirichlet approximation with maximum denominator floor(Y) therefore gives a denominator v between c'_j Y and Y, with error at most v^-2. For sufficiently large Y this lies in [Y^(1/4),Y^(2-1/4)]. The source prime-minor-sum estimate yields an O_j(Y^(1-c_m(2,1/4))) bound for every character twist, hence o(Y) for the logarithmically weighted sum in our fixed progression.

The zero Fourier mode is Y/phi(q)+o(Y), by the source prime-progression estimate. Trigonometric upper and lower approximations to intervals and the preceding vanishing of every fixed nonzero Fourier mode imply uniform distribution of alpha(p-1)^2 mod 1 among primes in the fixed progression, with logarithmic prime weights. Partial summation removes those weights. The region ||t||>=1/4 has measure 1/2 and a finite boundary of measure zero, so

    #{p<=Y : p=a mod q, p in S}
       ~ (1/2) #{p<=Y : p=a mod q}.

In particular S has infinitely many primes p=1 mod q for every q; at those primes h(p) is divisible by q. The original polynomial is prime-intersective and all its local root congruences still meet S abundantly. Yet the avoidance density remains 1/8.

Implication for research: positive density in all fixed reduced classes, even with the same limiting relative density 1/2, cannot substitute for the polynomial-phase information in the prime kernel. To extend the proof to a prescribed prime subset one would need an additional quantitative analytic hypothesis or a genuinely new mechanism that rules out this phase mask. We do not assert a counterexample to any theorem with growing-modulus or polynomial-phase uniformity hypotheses, and we do not nominate a conditional transference lemma as a substantial result.
