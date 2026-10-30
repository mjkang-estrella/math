# Full ordinary proof candidate: no prime square is sparsely Schemmel totient

Status: complete ordinary argument, depending on the published prime-gap Lemma 2 below and Bertrand's postulate. Not independently reviewed. Novelty and substantive eligibility HOLD; credit 0. No Lean claim.

## Literal source question

Colin Defant, *On Sparsely Schemmel Totient Numbers*, INTEGERS 15 (2015), #A18, published 8 May 2015, printed p8, Conjecture 1:
For every prime p and positive integer r, p² does not belong to F_r.
The preprint arXiv:1412.3080v1 has the same question as Conjecture 3.1, p9.

The source defines the multiplicative function S_r by S_r(l^e)=0 if the prime l≤r and S_r(l^e)=l^(e−1)(l−r) otherwise; S_r(1)=1. Set B_r={n≥1:S_r(n)>0}. The set F_r consists of n∈B_r such that S_r(n)<S_r(m) for EVERY m∈B_r with m>n. A single m>p² in B_r with S_r(m)≤S_r(p²) therefore suffices. This is the entire Conjecture 1, not the different Conjecture 2 on a largest prime's cube dividing arbitrary n.

## Published dependencies

1. Bertrand's postulate: for integer r≥1 the least prime a>r satisfies a≤2r. The r=1 equality is allowed.
2. Defant's published Lemma 2, printed p6: consecutive primes p_j,p_(j+1) satisfy p_(j+1)≤(7/5)p_j for j outside {1,2,4}. In particular, if x≥11 and q is the smallest prime strictly greater than x, then q≤(7/5)x<(3/2)x. Indeed the preceding prime u obeys 11≤u≤x and its index is not exceptional, so q≤7u/5≤7x/5. This also covers x itself prime.

Lemma 2's actual proof invokes Dusart's prime-in-(x,x+x/(25log²x)] estimate for x≥396738, and a finite small-prime check. Its statement and proof were read in the actual journal body. check.py independently reproduces its complete finite base using an integer sieve; the infinite range is the cited published lemma, not numerical extrapolation. Dusart arXiv:1002.0442, Proposition 6.8 and its actual proof on p8 were also fetched and read. That proof uses a Chebyshev-function estimate and published finite prime-gap data; those antecedent computations are not independently re-audited here.

## Uniform argument

If p≤r then S_r(p²)=0, so p²∉B_r and the conclusion is immediate. Assume p>r. Let a be the least prime >r. Thus r<a≤p and a≤2r. Put x=p²/a, let q be the least prime strictly greater than x, and set m=aq. Since x≥p≥a and q>x, the primes a and q are distinct, m>p², and m∈B_r. Multiplicativity gives

S_r(m)=(a−r)(q−r),    S_r(p²)=p(p−r).

Suppose first x≥11. By dependency 2, q<(3/2)p²/a. Because a−r>0,

S_r(m)<(a−r)((3/2)p²/a−r).

The following exact identity proves the right side is at most p(p−r):

p(p−r)−(a−r)((3/2)p²/a−r)
 = ((3r−a)/(2a))(p−a)²
   +(2r−a)(p−a)
   +(a−r)(r−a/2).

Every summand is nonnegative: p≥a>r>0 and a≤2r. Hence S_r(m)<S_r(p²), as required. This argument holds for all such r,p, without upper limits.

## Complete finite exception list

If x<11, then p≤x<11, so p∈{2,3,5,7}. Enumerate integers 1≤r<p and retain p²/a<11. The following is the full list; q is still the least prime >p²/a. Primality here is elementary trial division.

|r|p|a|q|m|S_r(m)|S_r(p²)|
|--:|--:|--:|--:|--:|--:|--:|
|1|2|2|3|6|2|2|
|1|3|2|5|10|4|6|
|2|3|3|5|15|3|3|
|2|5|3|11|33|9|15|
|3|5|5|7|35|8|10|
|3|7|5|11|55|16|28|
|4|5|5|7|35|3|5|
|4|7|5|11|55|7|21|
|5|7|7|11|77|12|14|
|6|7|7|11|77|5|7|

Each row has m>p² and 0<S_r(m)≤S_r(p²). Together with the uniform argument and the p≤r case, this proves the literal full conjecture. QED.

## Eligibility objection and limits

This argument combines a two-prime replacement with an elementary quadratic identity and a prime-gap lemma already in the source. It is short enough that the campaign's exclusion of routine corollaries is a serious objection. The author's Theorem 3 already proves exclusion of the *least* admissible prime's square and of every prime cube; neither theorem states the arbitrary-prime-square conclusion. The present argument does not follow just by applying the source's downward-prime-power lemma to its prime-cube result (that implication goes in the wrong direction). Nonetheless its substantive status requires root adjudication; mathematical completeness alone does not meet the user's freshness requirement.

No full current Omega tree clearance exists, no exhaustive semantic registry screen was done, and no independent adversarial review or Lean certificate exists. The statement must not be counted on this packet alone.
