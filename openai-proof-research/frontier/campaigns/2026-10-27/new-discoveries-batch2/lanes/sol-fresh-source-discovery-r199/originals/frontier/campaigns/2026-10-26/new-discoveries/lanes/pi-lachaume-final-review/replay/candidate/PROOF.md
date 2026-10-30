# Quartic refutation of Lachaume diagonal concavity; known companion converse failure

Proposed Conjecture1 outcome only, discovery credit **0** pending all gates. Parent discovery dated 2026-10-26. No external posting. Only Conjecture1 / MathDB338076 can form the candidate discovery basis. The companion Conjecture3 failure is known by translation of Zaimi2016 and uncredited; see the parent addendum.

## Literal source and versions

Xavier Lachaume, *On the concavity of a sum of elementary symmetric polynomials*, arXiv:1712.10327v1 (12 December 2017). Current arXiv submission history inspected: v1 only. Parent personally inspected rendered PDF p.3 (definitions, Conjecture1) and p.5 (Conjecture3). Actual PDF/text snapshots are in sources/.

On p.3: for nonnegative coefficients a=(a0,...,ap), f_a=sum a_k sigma_k in n variables; the conjecture asserts concavity of f_a^(1/p) throughout the strictly positive orthant iff its positive diagonal restriction has the same concavity. Here n=p=4 and **all coefficients are strictly positive**, a=(1,2,1,2,1).

On p.5: for a nonnegative-coefficient polynomial P of degree n, Conjecture3 asserts real-rootedness from PP''+(1/n-1)(P')²<=0 on ALL REAL arguments. Our construction meets that global condition literally; no positive-half-axis weakening.

MathDB338076 is the main source question. Snapshot reports open with empty solution/progress/comment fields; this is not novelty evidence by itself. The source Conjecture3 need not have a separate MathDB record. Adjacent 338077/338078/338079 concern different assertions and are not claimed newly resolved.

## Quartic and exact global inequality

Take P(x)=x^4+8x^3+6x²+8x+1. Direct polynomial expansion gives

    4 P P'' - 3(P')² = -144(x²-1)² <= 0  for every real x.

In particular P>0 on x>0, and the genuine real fourth root h=P^(1/4) obeys

    h'' = (4PP''-3(P')²)/(16 P^(7/4)) <= 0.

Hence h is concave on the entire open positive axis. This is a full universal diagonal-concavity statement, not a finite numerical check.

## Uncredited companion: nonreal root and Conjecture3 failure

Write s=sqrt(3), u=s-2 and v=sqrt(4s-6). Since s>3/2, v>0. The exact factorization is

    P(x)=(x²+(4-2s)x+1)(x²+(4+2s)x+1).

For z=u+i v, the first factor is zero: its imaginary part is v(2u+4-2s)=0, and its real part is u²-v²+(4-2s)u+1=0 using s²=3 and v²=4s-6. Thus P(z)=0 and Im(z)=v>0. Nonnegative coefficients, degree4, global differential condition and failure of real-rootedness are all genuine.

## Literal elementary-symmetric sum: Conjecture1 false

Let f=1+2 sigma1+sigma2+2 sigma3+sigma4 in four variables. Its diagonal is exactly P. With the first coordinate fixed to 2,

    g(t)=f(2,t,t,t)=5+12t+15t²+4t³.

Choose positive vectors a=(2,1/20,1/20,1/20), b=(2,3/20,3/20,3/20); their midpoint is c=(2,1/10,1/10,1/10). Exact values are

    f(a)=2819/500, f(c)=3177/500, f(b)=7151/1000.

Use the exact rational bounds

    (15409/10000)^4 < 2819/500,
    3177/500 < (15877/10000)^4,
    (16352/10000)^4 < 7151/1000.

All bases and values are strictly positive. Monotonicity of the positive fourth root yields

    f(c)^(1/4) < 15877/10000
      < (15409/10000 + 16352/10000)/2
      < (f(a)^(1/4)+f(b)^(1/4))/2.

The middle rational gap is exactly 7/20000. This contradicts midpoint concavity at strictly positive inputs, with no boundary/convention loophole. Since the diagonal fourth root is globally concave, the source's asserted implication is false.

For intuition only: 4g g''-3(g')² at t=0 is168>0. The actual proof uses the strictly positive finite Jensen witness above.

## Prior work and limits

Parent searched the source title, Lachaume/concavity/counterexample, Conjecture3 and the explicit quartic; no direct prior resolution found in this bounded initial screen. Serious independent novelty investigation remains mandatory.

A genuinely relevant public prior is Carptopus, *A Walsh-convolution proof of two conjectures of Lachaume*, public v0.1-beta 4 September2026, DOI10.5281/zenodo.22299983, github.com/Carptopus/MathExplore-Notes/research/lachaume-walsh-convolution. Parent read its actual README and entire relevant LaTeX scope section. It proves Conjectures4/5 and explicitly excludes1/3. Its section on Conjecture2 credits Lachaume's later2018 Lovelock paper for the real-rooted diagonal sufficient criterion. That later primary paper and the author's thesis must be read for duplication/source changes; parent has not yet done so. Do NOT count classical Walsh convolution or Conjecture2 here.

No claim of absolute priority. The quartic could be a known normalized-Laguerre counterexample, and this requires a serious nearest-prior search, not merely empty citation lists. Parent now completed three Lean modules,61declarations, actual source endpoints with C² regularity and strict replay PASS. A manuscript draft is built. Independent reviews and extracted packet still pending; credit0.

## Parent formal and companion check update

Fresh isolated strict replay of61declarations PASS with warningsAsError and exactly propext/Classical.choice/Quot.sound. Parent personally read all61types/axiom reports. Literal subset-sum elementary functions are bridged to MvPolynomial.esymm; actual fourth-root C² regularity proved on the strictly positive orthant. No residual proof hypotheses.

Parent downloaded/read latest1712.04528v2 (current submission history: v2July9,2018), especially Theorem2.7(d), Remark8/Conjecture1 and conclusion. It proves the distinct sufficient real-rooted-diagonal criterion by Walsh, and retains a more general diagonal-concavity conjecture for arbitrary C²outer F. The present construction takes F(t)=t^(1/4). This is still one combined construction, no extra credit. Published typeset copy/thesis and systematic citing/nearest-prior checks remain for review.

## Superseding prior-art/scope correction

The preliminary review found MO248816/answer248836 (Zaimi2016). Parent corrects its mistaken claim that the normalized differential condition is not translation invariant: (x+2)^4−1 has strictly positive coefficients and exactly the same known converse failure. Therefore Conjecture3 has NO discovery credit, even in the nonnegative-coefficient setting. Only the substantive Conjecture1 diagonal/global concavity failure remains a prospective discovery. Candidate/reviews/parent-addendum.md contains the exact correction and detailed actual Andrica2019Section5 comparison (full publisherPDF obtained, relevant18pages read). Earlier preliminary searches/limitations above are historical, not final novelty conclusions.
