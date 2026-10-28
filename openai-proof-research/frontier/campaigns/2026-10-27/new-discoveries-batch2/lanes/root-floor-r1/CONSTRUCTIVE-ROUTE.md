**EXCLUDED: exact public prior resolution found. See EXCLUSION.md. Credit 0.**

# Elementary interval route, avoiding the torus formalization

**Unreviewed. Credit 0.** This is an alternative necessity proof for Conjecture
4.7, using exact floor computations and a Cassini-type invariant. It is more
concrete than the compact-group proof in PROOF.md and may shorten Lean work.

Write q=α² and F(n)=floor(nq)−floor(α floor(nα)). Assume α>0 irrational
and F(n)=1 for every positive integer n. The pointwise bound F(n)≥floor(α{nα})
and irrational rotation density force α<2 (if α>2 choose {nα}>2/α); α=2 is
rational. If α<1 then F(1)=0. Thus 1<α<2.

The first three constraints give, by direct interval arithmetic,

    5/2 ≤ q < 8/3.

Indeed F(1)=1 gives 2≤q<3. On that interval, F(2)=1 gives
5/2≤q<25/9. The third constraint lowers the upper endpoint to 8/3.
These are finite scalar floor claims, not numerical approximations.

## The interval induction

Let positive integers a,b satisfy a≥2, 3a/2≤b<2a, and

    b²−ab−a²=−1.

Set

    c=a+b, d=a+2b, e=2a+3b, f=3a+5b,
    L=2a+b, J=a+3b, K=3a+4b.

Suppose c/a≤q<d/b and F(c)=F(L)=F(d)=1. Then

    e/c ≤ q < f/d.

Here is the complete scalar mechanism. It uses only positive squaring,
the Cassini identity, and the integer bounds stated above.

1. Initial bounds give d−1<cα<d+1. Consequently floor(cα) is d−1 or d.
   The identities c³−ad²=−b and c²d−bd²=d verify the squared endpoints.

2. If floor(cα)=d−1 then q<d²/c². On [c/a,d²/c²),

       J ≤ Lα < J+1,
       K−1 ≤ Lq < K,
       K−1 ≤ Jα < K.

   Thus F(L)=0, contradiction. Exact endpoint certificates:

       L²c−aJ² = 3a−b > 0,
       Ld−Jc = 1,
       Lc−a(K−1) = a−1 > 0,
       Kc²−Ld² = a > 0,
       J²c−a(K−1)² = 6a²+8ab−9a−9b > 0,
       Kc−Jd = 2.

   All identities here and below hold modulo b²−ab−a²+1=0.

3. We therefore have floor(cα)=d. The initial interval gives

       e−1<cq<e+1,    e−1<dα<e+1.

   So F(c)=1 forces floor(cq)=e and floor(dα)=e−1. Hence
   e/c≤q<e²/d². The first pair of endpoints follows from
   c²−ae=−1 and cd−be=1. For the squared dα bounds use
   d²c−ae²=−K and d³−be²=c, together with
   2e−1>K/a and 2e+1>c/b (immediate from a≥2, 3a/2≤b<2a).

4. On [e/c,e²/d²),

       f−1<dq<f+1,    f−2≤(e−1)α<f−1.

   For the first, de−cf=−1 and e²−df=1. For the second, the lower
   squared certificate is

       (e−1)²e−c(f−2)² = 6a²+10ab−3a−3b−2 > 0,

   and the upper certificate is d(f−1)−(e−1)e=c−1>0.
   Since floor(dα)=e−1, F(d)=1 now forces floor(dq)=f−1,
   so q<f/d. This completes the interval step.

All displayed positive polynomials are positive for a≥2,b≥3; no asymptotic
estimate is hidden in the step. The map (a,b)↦(c,d) preserves the Cassini
identity and the bounds 3a/2≤b<2a. Start with (a,b)=(2,3).

## Shrinking to the golden ratio

Let (a_i,b_i) be successive pairs under that map, starting at (2,3).
The base constraints and interval step prove

    1+b_i/a_i ≤ q < 2+a_i/b_i

for every i. Also a_i≥i+2, so a_i→∞. Set r_i=b_i/a_i. Its invariant is
r_i²−r_i−1=−1/a_i², and 3/2≤r_i<2. With φ=(1+sqrt(5))/2,

    0 < φ−r_i = 1/[a_i²(φ+r_i−1)] ≤ 1/a_i².

Thus r_i→φ. The two endpoints tend to 1+φ=φ² and 2+1/φ=φ²,
respectively. Squeezing yields q=φ² and α=φ by positivity.

This proves necessity without the circle-endomorphism classification.
The already known sufficiency remains one line from α²=α+1, as in PROOF.md.

Formal and independent-review gates remain open. The initial three scalar
claims, every endpoint certificate, and the passage from irrational density to
α<2 must be checked in Lean; they are not permitted as extra axioms.
