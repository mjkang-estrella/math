# Squarefree denominators: prefreeze working question

This is a question, not a frozen theorem or nominee. No full proof is claimed.

(QSF) Do absolute B>0 and b0 exist such that every squarefree integer b>=b0 and every integer 1<=a<b admit

    a/b = sum_{i=1}^k 1/n_i,  k <= B log log b,

with distinct squarefree integers 2<=n_1<...<n_k, without a denominator-height bound?

Unreduced a/b is allowed. This differs from immutable I205 (arbitrary b, polynomial heights) and T025O54 (odd denominators). The necessary squarefree reduced-denominator condition is built in, not offered as a contribution. Initial selection of odd denominators was abandoned on actually reading r54, before any freeze. Family024 was only navigational.

## First integrated reductions (prefreeze)

Source025 provides short unrestricted lists, residue selection through deterministic and random prime products, a common-denominator descent, shifted divisor moments, dense-to-all addition, and duplicate cleanup. r54 supplies a stronger composition than a naive parity conversion: constrained multipliers, terminal digit templates, valuation separation and a sparse-dilation merge. These operations are paid historical inputs for comparison, not a new result here.

Squarefreeness has a distinct global issue. If n has a squared prime factor then 1/n cannot be a finite sum of reciprocals of squarefree integers: their lcm is squarefree, so every reduced sum denominator is squarefree. Thus individual-term squarefree cleanup is impossible. This does not obstruct a global replacement of a short list whose total a/b has squarefree reduced denominator.

For such a list let p^e, e>=2, be its maximal p-power denominator factor, and write the terms at that level as 1/(p^e m_i), p∤m_i. Let L=lcm_i m_i. Clearing the p-primary part in the full sum gives

    sum_i L/m_i = 0 (mod p).

Consequently the WHOLE top-level block can be replaced by the positive rational

    [sum_i L/m_i / p] / (p^(e-1) L).

This lowers its p-exponent by at least one. It is a rational-block identity, not a short Egyptian representation. Applying Source025 afresh to the block can reintroduce other squared primes (or p), so no monotone complexity descent has been proved. Grouping the entire sum merely returns the original question.

In the raw source identity u/(MQ)=1/((M/t)z)+(1/z)h/(MQ), squarefree M,Q alone do not suffice: z can be nonsquarefree or share primes with M/t, Q, previous z's, or the later terminal denominator. Constraining z modulo a fixed finite modulus (as in r54) cannot exclude square divisibility by all primes or guarantee coprimality to a path-dependent accumulated product. Reusing the binary/base5 terminal reservoir also creates prime powers. The required operation is a short exact positive completion preserving squarefree lcms through all rescalings, or an entirely global replacement with the same double-logarithmic length.

No assertion is made that failure of these literal steps proves QSF false or that all possible classical compositions have been excluded.

## Correction: reduced lcm states remove a false obstruction

The previous paragraph about old path primes concerns the literal, unreduced source recursion only. Requiring every new multiplier to avoid every old prime would be unnecessarily strong. Here is the compatible cancellation operation.

Let B be squarefree, 0<u<B, t|B, z>=1, and h=uz-t>=0. Suppose n=(B/t)z is squarefree. Equivalently z is squarefree and gcd(z,B/t)=1. Set g=gcd(z,t). Then g|h and

    u/B = 1/n + (h/g)/(Bz/g).

Bz/g is squarefree, because g=gcd(z,B). Further reduction only removes primes. Thus a small h contracts the integer numerator (h/g<=h), while the reduced denominator remains squarefree. This is the ordinary lcm subtraction operation; it handles shared primes exactly. It means that failure of the original product denominator is not itself an unpaid operation. The unresolved matter is finding enough successful t with squarefree n and propagating a short descent when the normalized base changes with the path.

## The terminal reservoir is also available classically

A primorial E has consecutive positive divisors in ratio at most two. Inductively, if the old divisors cover [1,E] with multiplicative gaps <=2 and the next prime p<=2E, the old divisors and their p multiples cover [1,pE] with the same property: if their ranges overlap, each range already has that property; if separated, the gap from E to p is <=2. Bertrand's bound gives p_next<2p_previous<=2E; start at E=2.

For every integer 1<=u<=E, greedy subtraction of the largest divisor d<=u leaves u-d<u/2 (or zero). Indeed the next divisor exceeds u and is <=2d, unless d=E and u=E. The remainder is smaller than d, so all chosen divisors are distinct. At most 1+log_2 u terms suffice.

Take E to be the least primorial >=S^D0. At the crossing E<=2(S^D0)^2, since the next prime is <=2 times the preceding primorial. Therefore log E=O(log S). If squarefree B is divisible by E, this gives a distinct squarefree expansion of u/B for every u<=S^D0 in O(log S) terms: divide those distinct divisors by B. No repeated prime-power digit base is necessary. An auxiliary squarefree base may contain lcm(E,b), so shared primes with the input do not obstruct this terminal construction. This is a classical dense-divisor composition, not a finding claimed here.

## A short squarefree prefix is feasible; it does not settle the tail

For all sufficiently large real x, an interval [x,x+6 sqrt(x)] contains a squarefree integer. For H=6 sqrt(x), eventually x+H<=2x. The number of nonsquarefree integers is at most

    sum_{p<=sqrt(2x)} (H/p^2+1)
      <= H sum_{n>=2} n^-2 + sqrt(2x) + O(1) < H.

For the final strict inequality one can bound sum_{n>=2}n^-2 <=1/4+1/9+integral_3^infinity t^-2 dt=25/36<0.7. Thus .7*6+sqrt(2)<6. Endpoint rounding is absorbed for large x.

Consequently, for small positive r, selecting such an n>=1/r gives

    0<=r-1/n <= 7 r^(3/2),

with n squarefree. Once r is below a fixed absolute threshold the positive remainder is less than 1/n and the next denominator is larger. A bounded initial prefix reaches that threshold: scan the squarefree integers in increasing order, subtracting 1/n whenever it does not exceed the current remainder, until the remainder is below the fixed threshold. If it never drops below that threshold, every denominator beyond its reciprocal would be selected, contradicting divergence of the squarefree reciprocal sum. A fixed finite initial segment with reciprocal mass greater than one beyond that cutoff gives a bound independent of a,b. The divergence follows from the same positive lower counting density. The input fraction stays below one. All prefix denominators are distinct, and reduced denominators stay squarefree by the lcm observation above.

Write r_j=A_j/C_j reduced. Each update gives C_{j+1}<=C_j n_j<=2C_j^2 once r is small, while shifted L_j=log(1/r_j)-2log7 grows by at least factor3/2. Stop at zero or at first C_j>=T. Because r_j>=1/C_j, stopping occurs in O(log log T) steps. The first crossing has C_j<=2T^2. Moreover

    log C_j <= log b + sum_{i<j} log n_i + O(1)
            <= log b + 2 log(1/r_j) + O(j),

so log A_j <= (log C_j+log b)/2+O(j). This is weaker than the ordinary source's nonincreasing numerator, but it is a useful paid prefix. It does not produce the exact high-stage source interface A<exp(S), C~exp(DC S). Classical reciprocal-phase estimates could be adjusted to a smaller separation: the second derivative test already gives power saving for Z between U^(1+epsilon) and U^(3-epsilon); higher derivative steps cover larger fixed powers. That modification would need full joint parameter checks before use in a theorem. It is not asserted as a finished replacement interface here.

## What the strongest primary compositions actually supply

Butler--Erdos--Graham (published 2015), all nine pages read, construct central blocks of subset sums of primorial divisors and hence integer representations by distinct three-prime denominators. Their proof's point is exact subset coverage, not short cardinality. Li arXiv:2606.15159v2, actually acquired and §§2,7,8 read, claims a stronger rational three-prime theorem using a semiprime block, a prime-deleted reservoir, and multiplication of the target by a fresh prime before dividing the denominators. The lifted denominators remain squarefree because the prime is omitted from the reservoir. This is a compatible classical-style operation; naive failure of an undeleted reservoir does not make this operation unpaid. The numerical base/finite certificates of Li were not replayed or independently certified here, and no mathematical conclusion here needs their correctness.

Even granting that full rational existence theorem, the fixed-three-prime output cannot itself have the QSF length uniformly. For a/b reduced, b divides the lcm of every representing denominator list. Hence

    omega(b) <= sum_i omega(n_i).

If each n_i has <=r prime factors, k>=omega(b)/r. For b the product of the first m primes and a=b-1, this gives k>=m/r, whereas log log b=O(log m) by the PNT (even a Bertrand bound suffices for O(log m)). Thus no fixed-r constructor, however efficient its implementation, supplies QSF directly on all b. QSF allows unbounded omega(n_i), so this is NOT a counterexample to QSF or a restricted replacement nominee.

One can choose r growing with b, but a fixed-r existence theorem has no uniform length guarantee in that regime. The fresh-prime lift raises r while preserving the number of terms; it does not compress that number. Choosing the lift prime before increasing the reservoir level is essential in Li's actual argument and has been accounted for, rather than tying the two parameters artificially.

Martin--Shi's finite-denominator search (published 2025) uses maximal-prime-power cancellation and returns all representations from a supplied multiset. It makes the earlier p-primary grouping operation explicit but supplies no small-cardinality representation or uniform finite reservoir with the QSF length. No exhaustive search or large finite base computation is being run.

## Exact local examples and remaining obligation

For B=30,u=7,t=15,z=3, the source identity is 7/30=1/6+6/90. The reduced-lcm step gives 7/30=1/6+2/30=1/6+1/15, all squarefree. The shared prime3 is harmless after cancellation. Conversely B=30,u=4,t=15,z=4 emits 1/8+1/120. Individual squarefree replacement of 1/8 is impossible, but the total equals 1/10+1/30. Thus neither example is an obstruction to a global construction.

The random prime-product reservoir itself can be chosen squarefree and disjoint from a fixed input prime set: in the source sampling range the probability of any repeated sample or any sample dividing a fixed C with log C=O(S) is O(S^2/P)=o(1). There is enough slack to intersect this with the source's probability1-o(1) events. This pays for the reservoir; it does not prove squarefree emitted multipliers.

An exact sufficient new step for the normalized divisor descent would control short paths whose emitted n=(B/t)z are squarefree, whose residues contract, and whose terminal state contains the required divisor reservoir. Normalization changes B to Bz/gcd(z,t); the next family of admissible divisors and its exceptional set consequently depend on the entire path. The source's moment estimate controls predecessors for fixed shifts and a fixed reservoir. No compatible path-dependent exceptional-set recurrence with the required short length has been established here.

The fixed-grid dense-to-all merge should also be tested before declaring a fresh obstruction: source selection failure is exponentially small in S/log S, so imposing it on O(S) dyadic top cutoffs is an affordable union bound. This could avoid the source's arbitrary final integer g, which would otherwise threaten squarefreeness. r54's marker separation can use the allowed squarefree valuations0 and1. These are plausible paid compositions, not a proved completion, because the squarefree path construction and its common good sets remain missing.

Alternative exact sufficient formulation: for each squarefree b and numerator a, find a squarefree Q divisible by b such that aQ/b is a sum of O(loglog b) DISTINCT divisors of Q. The Q may depend on a,b and has no height cap. This is equivalent to QSF: any squarefree expansion yields such Q by taking its lcm, and any such divisor sum yields the expansion by division by Q. Ordinary subset-sum coverage is insufficient; the cardinality bound is the unresolved part. This equivalence is algebraic, not a new contribution.

Status after all these comparisons: PREFREEZE / NO NOMINEE. QSF is retained with all numerators and squarefree b; no finite-prime-count subclass, odd restriction, weak length, or supporting obstruction replaces it. No extended theorem proof was drafted or frozen.

## Stronger classical baseline and absorption compatibility (late prefreeze)

There is already an elementary polynomial-size squarefree construction with logarithmic, rather than double-logarithmic, length. Let E be the least primorial >=b; then E<=2b^2. Put Q=lcm(E,b), so Q is squarefree and Q<=2b^3. Every prime of b missing from E is <=b<=E, hence adjoining these primes preserves the divisor-ratio-at-most-two property proved above. Greedy subtraction therefore writes the integer aQ/b (<Q) as at most 1+log_2 Q distinct divisors of Q. Dividing by Q produces distinct squarefree unit denominators <=2b^3 in O(log b) terms. This is a classical divisor composition. It is neither the earlier I205 double-logarithmic target nor a replacement nominee for it. Thus even polynomial heights and ordinary squarefree existence are already paid; QSF is specifically a sparse exact representation problem.

Conlon et al., Theorem5 and §4, also permit a squarefree-compatible local cancellation. Fix 0<epsilon<1. For a large prime p, choose I to be the squarefree integers in [p^epsilon,2p^epsilon]; it has fixed positive density by the elementary squarefree count and is automatically p-free eventually. Their Theorem5 supplies DISTINCT m in I, at most p^(epsilon/2), with any required sum of m^(-1) modulo p. Subtracting the corresponding 1/(pm) cancels p, emits squarefree denominators, and leaves a squarefree reduced denominator by the lcm rule. Every newly introduced prime is <=2p^epsilon. The reciprocal mass cost is at most p^(-1-epsilon/2). Different processed primes give distinct emitted denominators because p is their largest prime. This is a compatible positive-mass absorption primitive, not a missing squarefree sieve. Positivity requires a reserved mass budget as in the actual primary proof; it does not follow merely from a congruence.

Neither the local term count p^(epsilon/2) nor the bound on the largest new prime gives an amortized O(loglog b) term count for all branches. Sending epsilon to zero with p is not licensed by the fixed-epsilon theorem. The actual transitive Conlon--Fox--Pham Theorem1.5 requires s>=m^eta with fixed eta>0; its proof uses that range in its growth iteration. It does not directly justify a logarithmic-size absorber by parameter substitution. Bourgain--Garaev v1 Theorems1--6 give energy/sumset estimates for reciprocal intervals (and a prime-input version), but the read statements do not supply the required sparse, squarefree, positive all-input completion. Only their statements were read here; no exclusion of a stronger composition from the rest of that paper or later literature is asserted.

The strongest integrated reduction is therefore broader than the literal normalized divisor path: it includes squarefree primorial reservoirs, exact lcm cancellation, dense-subset modular inverse absorption with correct positivity, prime-deleted scaling, and source short unrestricted expansions. What is actually unpaid in this round is a compatible GLOBAL double-logarithmic cardinality bound, with exact completion for every numerator. No operation has been proved to supply that bound.
