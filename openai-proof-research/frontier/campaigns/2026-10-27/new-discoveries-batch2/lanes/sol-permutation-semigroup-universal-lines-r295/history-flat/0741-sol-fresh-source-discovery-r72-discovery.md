# r72: Zinn's full Rademacher doubling question — unresolved

Credit 0. No nomination, complete source proof, Lean or PROOF.md. Root alone decides acceptance.

## Selection and attribution

Selected source: https://mathoverflow.net/questions/208349/zinns-doubling-conjecture-on-weighted-sums-of-independent-rademacher-random-v . Iosif Pinelis posted the question 2015-06-03 17:12 and expressly attributes the conjecture to Joel Zinn. The currently read page includes the 2020 comment that Pinelis had not seen it in a publication. Thus this is a genuine expert-stated primary question, not a claim of a published Zinn conjecture. The named Pinelis profile, https://mathoverflow.net/users/36721/iosif-pinelis , identifies Michigan Technological University and probability/inequalities expertise; the author name and subject are corroborated by his actual mathematical manuscript math/0701806v1. Identity was checked before mathematical experiments.

For every finite real vector a with sum a_i²=1, independent equiprobable signs eta_i, S=sum a_i eta_i and independent copy T, is E|S|^p <= E|(S+T)/sqrt2|^p for every real p>=2? The source states that p=2 and p>=3 are known; the substantive remaining range is ALL 2<p<3 and ALL finite vectors. No restriction to equal weights, bounded dimension, integer weights or asymptotics is made here.

Source status: actual current public question and its sole answer read via web text on 2026-10-29, independently of direct HTTP403. It still contains failed g_t and two/four-moment routes, not a full resolution. No later published source version was located in the bounded exact-title/Zinn/doubling searches. Search absence is not certification.

Freshness/duplication: capped scan.py searched older frontier SUMMARY.md files (excluding frozen/extracted copies); Zinn/208349 and the other fresh Pinelis lead 451831 had no hits. Additional rg covered discovery.md and FINDINGS.md. Jekl was immediately retired on the r47 hit, and DeTemple was retired for credited-family overlap; neither was reinvestigated as a candidate. A five-circle lead was abandoned on finding its original non-expert question attribution and existing Pinelis answer. Mao's paper was only a retrieval lead and could not be read (timeout), so no conjecture selected from it. Only TWO fresh expert-attributed questions were screened: 208349 selected; 451831 excluded by its actual full public River Li answer (2023, edited 2024). No credit for rechecking it.

## Closest bodies and limits before sustained work

Pinelis's primary arXiv:math/0701806v1 is an expanded preprint of his Annals of Statistics 22(1994),357–368 paper. Theorem4.1, Corollary4.4 and the appendix proof were actually read. The class is even f with convex second derivative. The proof conditions on the other coordinates and uses convexity of g(u)=f(a+b sqrt(u))+f(a-b sqrt(u)), then Jensen and successive replacements. For f(x)=|x|^p, 2<p<3, f''''(x)=p(p-1)(p-2)(p-3)|x|^(p-4)<0 off zero: this hypothesis fails. That theorem therefore explains the known p>=3 case but supplies no full source bridge. Its Taylor-necessity argument already identifies the obstruction to universal single-coordinate replacement; our explicit certificates below are NOT a new theorem claim.

Published Annals body returned a service-notice HTML object under a .pdf name; conversion failed and bytes are preserved. The exact printed Corollary2.5 was not read. Figiel et al.1997 Lemma2.2 body was blocked403; its description in MO is not promoted to an independently read theorem. These are material access gaps, not cleared by abstracts. The expansion-preprint theorem/proof is sufficient for the limited class comparison above.

Before the full-scope routes, dated registry trees were screened (scan.json). No lexical Zinn/Rademacher match was found. Actual pinned Metya–Mukherjee Problems body and IndependentConvolutionL1Minimum.lean definitions, theorem and proof were read: it minimizes full L1 error of arbitrary finite convolutions against a uniform vector, with no normalized p-moment comparison. Its sector-crossing proof supplies no demonstrated bridge. This is only a lexical neighbor, not a claim that it is the mathematically closest theorem. No matching registry body was located; a filename search cannot certify absence.

Shared GitHubAPI403 persists: inherited r58/r69 evidence has no reset clearance. Zero API calls in this lane, no retry/bypass. Latest observed Omega6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3 at15:49UTC is NOT current HEAD. r57 omega-D5.json is Blueprint markdown, while r58 omega-D5.json contains actual .lean paths. Neither is a current complete delta. root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json was read; its bounded acceptance judgment is not transferred to r72. Freshness HOLD remains.

## Route 1: a full-scope Mellin criterion, with local positivity

For 2<p<4 define I_p=int_0^infty (cos t-1+t²/2)t^(-p-1)dt. This is finite and positive: the numerator is nonnegative, O(t^4) near zero, O(t²) at infinity, and positive on an interval. Scaling gives |x|^p=I_p^-1 int_0^infty [cos(tx)-1+t²x²/2]t^(-p-1)dt. Tonelli applies to each finite sign law. Equal variances cancel, so the desired moment difference equals

I_p^-1 int_0^infty D_a(t)t^(-p-1)dt,
D_a(t)=prod_i cos(a_i t/sqrt2)^2 - prod_i cos(a_i t).

This is an exact all-vector criterion. Integrability also follows directly: D_a(t)=A4*t^4/24+O(t^6) at0, A4=sum a_i^4>0, and |D_a|<=2 at infinity. The coefficient follows independently from E S^4=3A2²-2A4, E U^4=3A2²-A4.

For 0<t<pi/(2max|a_i|), every cosine is positive and cos(x/sqrt2)^2>=cos x. To prove this, differentiate 2log cos(x/sqrt2)-log cos x: the derivative is tan x-sqrt2 tan(x/sqrt2)>0, because tan x/x increases on(0,pi/2). This last assertion follows by differentiating x sec²x-tan x, whose derivative is2x sec²x tan x>0. Thus D_a(t)>0 on this initial interval.

However n1,a1=1 gives D_a(2pi)=cos(sqrt2*pi)^2-1<0, since sqrt2 is not an integer. Positive local curvature cannot replace the weighted integral. The crude absolute tail estimate 2T^-p/p gives no established uniform domination by the initial positive integral. A genuine all-vector oscillatory-tail estimate, or a different mechanism, is still missing.

## Route 2: Laplace order of squares fails in the genuine source family

Put q=p/2 in(1,3/2). The same positive-remainder scaling argument using e^-u-1+u expresses the moment difference as a positive constant times int_0^infty [L_U(t)-L_S(t)]t^(-q-1)dt, L_X=E exp(-tX²). No Gaussian mixing/limit exchange is assumed.

For unnormalized a=(1,1), let y=e^-2t. Exact enumeration gives
L_U-L_S=3/8+y/2+y^4/8 -1/2-y²/2
=(y-1)²(y²+2y-1)/8.

It changes sign at y=sqrt2-1. Hence pointwise Laplace order cannot prove the source claim. Nevertheless the actual source moment difference is positive for ALL p>2 in this example: set z=2^(p/2-1)>1; it is z+z³-2z²=z(z-1)²>0. This contrast makes the missing integration step concrete.

## Route 3: synchronized splitting cannot be replaced by a monotone path

Replace each eta_i independently, with probability s, by (eta_i+eta_i')/sqrt2, otherwise retain eta_i. At s0 one has S and at s1 one has U. For n2,a=(1,1),p5/2, the derivative at s0 is twice the single-coordinate replacement difference. That difference is

1/2 + [(1+sqrt2)^(5/2)+(sqrt2-1)^(5/2)]/4 -2sqrt2 <0.

The sum in brackets equals A=(7-2sqrt2)sqrt(2+2sqrt2). All compared quantities are positive; (8sqrt2-2)²-A²=130-90sqrt2>0 because 2<169/81. Thus the interpolation initially DECREASES even for a genuine Rademacher vector, while its endpoint difference is positive by Route2. Scaling the vector to unit variance preserves this strict sign. This invalidates a monotonicity-in-s proof, not the source conjecture.

Off the singular support there is another transparent obstruction: for y>sqrt2*r>0, single-coordinate splitting has difference sum_{k>=2} binom(p,2k)y^(p-2k)r^(2k)(2^(k-1)-1)<0, since every indicated binomial coefficient is negative when2<p<3. Absolute convergence follows from sqrt2*r/y<1. This is consistent with the actual Pinelis necessity proof.

## Route 4: subgaussianity and low moments are insufficient

Let X take ±1 each with probability eps/2 and0 otherwise. Its doubled p-moment/old p-moment ratio is (1-eps)/z+eps*z, z=2^(p/2-1). Choose eps2/5,z9/8, so2<p<3 and this ratio=59/60<1.

Yet X is subgaussian with its exact variance eps: termwise E X^(2k)=eps <=(2k-1)!! eps^k for k>=2. At k2 this follows from3eps>1; subsequent right/left ratios increase by(2k+1)eps>1. Summing nonnegative cosh/exponential series proves E e^(tX)<=exp(eps*t²/2) for all real t. Its kurtosis is5/2<3 as well. Thus these broad properties cannot establish doubling. This is NOT an admissible-source witness: if a finite Rademacher sum has only three support points, it has exactly two equal nonzero coefficients, giving nonzero mass1/2. To see this, order positive coefficients; distinct subset sums contain0,b1,b1+b2,...,sum b_i, at least m+1 distinct sums for m nonzero coefficients. Three support points force m<=2, and m2 forces equality of the coefficients. Hence X is outside the source family.

## Reproducibility, objection, falsifier and remaining gap

sh run.sh: 800 exact assertions, including160 independent sign-enumeration/DP vector comparisons, fourth moments, rational Laplace factorization and exact obstruction certificates. 4800 integer-weight vectors at six p values and8000 interpolation derivative diagnostics are floating evidence ONLY, with repeated equal-weight samples acknowledged. No rigorous negative full-source witness was found; no finite positive census is called a proof. All Python helpers were run through the copied monitor: AS512MiB,groupRSS512MiB,CPU210s,wall230s,40ms samples,BLAS1. No caps raised. Failures listed in progress.md; no Lean.

Strongest objection: every established statement here is a reduction, known classical comparison explanation or obstruction to a stronger method. None proves the full all-vector p-moment comparison. The hard cancellation is between the initial positive characteristic-function interval and the oscillatory tail; even genuine source laws defeat the strongest simple pointwise and interpolation orders.

Falsifier: a finite real (preferably exact rational up to common normalization) vector and p in(2,3) with a certified strict NEGATIVE actual doubled-minus-original p-moment, including rigorous evaluation error bounds. Method-law failures do not qualify.

Precise gap: prove int_0^infty D_a(t)t^(-p-1)dt>=0 uniformly for every finite a and2<p<3, or construct such an admissible strict negative witness. Current registry freshness and blocked original theorem bodies remain separate eligibility gaps. No discovery credit or acceptance requested.
