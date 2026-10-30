# Counterexample family for Keith's multicolor linear-cut conjecture

Working result, October 26, 2026. **Credit 0:** complete Lean, independent review, full bounded novelty gate, paper and extracted packet are pending. This is one proposed source-question resolution, not a credit for each box or cut.

## Exact target and scope

William J. Keith, *Restricted k-color partitions, II*, arXiv:2001.08351v1, Conjecture 1 on printed p.2 and its explicit slant-cut discussion on p.8. Theorem 3 counts partitions in an M by N box, at most N parts each of size at most M, with one of k colors chosen for each distinct part size. A color variable records how many distinct part sizes receive that color. Set the third variable to 1, take the coefficient of a fixed q power, and retain the coefficient array in x,y. The conjecture says every linear cut is unimodal. Its p.8 example explicitly includes cuts with step (1,-2), so the present step is within the intended scope.

MathDB 345259 refers to this multicolor extension. Its title attributes the underlying two-color conjecture to Dousse and Kim; **the present result refutes Keith's three-color extension only**. Dousse–Kim arXiv:1701.07915 Conjecture 7.1(ii), the original one-variable claim, is not refuted. The source's apparent n-versus-k dimensional typo is irrelevant and supplies no credit.

## The family

Let N>=25 and set M=N and n=N(N+1)/2. Write a_r for the number of ordinary partitions of n in the N by N box with exactly r distinct part sizes. The coefficient polynomial after setting the third color to 1 is, by the literal counting rule (also Keith Theorem 3),

F_N(x,y) = sum_(r=0)^N a_r (1+x+y)^r.

Its coefficient C_N(i,j) is

C_N(i,j) = sum_(r>=i+j) a_r r! / (i! j! (r-i-j)!).

The three consecutive points

(N-5,5), (N-4,3), (N-3,1)

lie on a line with step (1,-2). They give a strict valley, so no full cut containing them is unimodal.

## Top distinct-size counts, directly from partitions

All part sizes lie in {1,...,N}.

1. a_N=1. Using every size already contributes n, so each size must occur once.
2. a_(N-1)=0. Such a partition omits a size a. Its distinct sizes contribute n-a, and at most one extra part is allowed. That extra part would have to be a, which is omitted.
3. To count a_(N-2), omit two sizes a<b. The other sizes contribute n-a-b. There are at most two extra parts, whose sum must be a+b. One extra part is possible precisely when a+b<=N. Two extra parts are an unordered pair c<=d from {1,...,N} with c+d=a+b, other than the forbidden pair (a,b). If either c or d is an omitted size, the other is the other omitted size, so this exclusion is exact.

For a sum s put m_s=#{1<=a<b<=N:a+b=s}. There are m_s+1_(s even) unordered pairs c<=d with that sum. Consequently

a_(N-2) = sum_s m_s (m_s-1 + 1_(s even) + 1_(s<=N)).

This is a classification, not merely an injection or a numerical count. Every admissible partition has a unique missing pair and multiset of extra parts, and every counted datum produces an admissible partition.

For N=2m+1, the positive values of m_s consist of four copies of each integer 1,...,m-1 and three copies of m. Moreover sum_(s even)m_s=sum_(s<=N)m_s=m^2. Hence

a_(N-2) = 4 sum_(r=1)^(m-1) r(r-1) + 3m(m-1) + 2m^2
          = m(m+1)(4m-1)/3
          = (N^2-1)(2N-3)/12.

For N=2m, there are four copies of each 1,...,m-1 and one copy of m. Both remaining sums equal m(m-1). Hence

a_(N-2) = 4 sum_(r=1)^(m-1) r(r-1) + m(m-1) + 2m(m-1)
          = m(m-1)(4m+1)/3
          = N(N-2)(2N+1)/12.

The direct missing/repeated-size enumerator in independent-counts.json verifies the N=25 count a_23=2444 independently of the q-Gaussian search.

## The strict valley

Writing A=a_(N-2), the top counts give

L = C_N(N-5,5) = binomial(N,5),
B = C_N(N-4,3) = N binomial(N-1,3),
R = C_N(N-3,1) = (N-2)A + N(N-1)(N-2)/2.

Their first difference is

L-B = N(N-1)(N-2)(N-3)(N-24)/120 > 0.

If N is odd,

R-B = (N-2)(N-1)(11N-3)/12 > 0.

If N is even,

R-B = (N-2)N(11N-14)/12 > 0.

Thus L>B<R for every N>=25, giving infinitely many literal-source counterexamples. No smallest box, smallest size, or complete classification of failing cuts is claimed.

For N=25, n=325, the coefficients at (20,5),(21,3),(22,1) are exactly

53130, 50600, 63112.

These are positive coefficients at consecutive lattice points, with a strict internal valley. This is not a support-boundary or zero-padding issue. The full nonnegative-lattice line has earlier zero entries, which do not remove the valley.

## Shorter proof using an injective family

The exact a_(N-2) formula is stronger than needed. In fact a_(N-2)>=binomial(N,3) alone gives

R >= (N-2) binomial(N,3) > N binomial(N-1,3)=B,

since the difference in the latter strict inequality is binomial(N,3)>0. The extra contribution of the unique staircase partition can simply be retained or ignored.

Here is an explicit injection proving that lower bound. For each 1<=u<v<w<=N put d=u+w-v, so u<d<w. Start from the staircase containing each size 1,...,N once. If v<=d, remove u,w and add v,d. If d<v, remove d,v and add u,w. The resulting partition has N parts, sum n and exactly N-2 distinct sizes. Its missing pair and extra multiset are disjoint. These uniquely recover u,w as the outermost of the four sizes; in the first case v is the smaller extra size, and in the second case v is the larger missing size. The cases are distinguished by whether the smaller missing size is below or above the smaller extra size. Thus different triples give different partitions. Equality v=d is allowed in the first case and means that one part size occurs three times.

For N=25 this supplies 2300 distinct actual partitions with 23 distinct sizes. Their colorings alone contribute 23*2300=52900 to C_25(22,1), already greater than 50600. This direct injection is a promising route for a formal source/count bridge without formalizing the Gaussian-binomial identities or assuming precomputed coefficient values.

## Independent q-Gaussian verification

Keith's Theorem 4 and the displayed identity on p.7 give

b_k(n) = [q^(n-k(k+1)/2)] Gaussian(M,k) Gaussian(M+N-k,N-k),

and C(i,j)=binomial(i+j,i)b_(i+j). This is the formula used by screen.py, using exact FLINT integer polynomials and the standard Gaussian recurrence.

At M=N=25,n=325 the only needed values are b_25=1, b_24=25, b_23=2744. In particular b_23=a_23+binomial(25,23)=2444+300. The independent direct-partition count agrees with all three cut values. Neither computation uses floating-point arithmetic.

## Remaining gates

Formalize a source-faithful endpoint, including the coefficient/count bridge rather than treating the three displayed integers as an assumed array. Obtain an independent actual-source, mathematical, formal and bounded-prior-art review; examine the final publication and closest follow-ups where accessible; write and visually verify a paper; build a manifest packet and replay after extraction. No acceptance until these gates pass. No posting, publication, external contact or upload occurred.

Initial Lean progress: formal/PartitionTopCounts.lean compiles with warnings as errors under pinned Lean 4.34.1/mathlib and checks 9 declarations with only the standard three axioms. It proves the finite missing-pair sum is 2444, the derived model's three exact values, and nonunimodality from a strict valley. It explicitly does **not** yet identify that model with the source's literal coefficient array. This is a helper certificate, not a completed formal refutation or discovery credit.
