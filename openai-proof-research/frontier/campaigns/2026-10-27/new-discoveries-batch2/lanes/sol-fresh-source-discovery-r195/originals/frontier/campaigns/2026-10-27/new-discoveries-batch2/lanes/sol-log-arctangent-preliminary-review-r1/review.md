# Independent preliminary adversarial review

Review date: 2026-10-29 UTC. Assigned candidate: `root-log-arctangent-candidate-r1`, supplied root freeze commit `88eb1b426c` (identifier supplied by root, no git command run). Counts remain 3/30 additional, 33/60 total. Candidate credit remains 0. This is a review, not acceptance. No children, git operations, external mutations, browser tabs or other-lane edits occurred. Root preliminary review notes were not used as authority.

**Ordinary mathematics PASS for the literal arXiv v2 Conjecture 4.7, both p=±sqrt(17), every distinct positive pair. Substantive eligibility and bounded novelty HOLD. Journal comparison HOLD. Formalization HOLD: no literal Lean endpoint exists.** Exact arithmetic is part of the ordinary proof; no floating-point diagnostic is used as evidence.

## Gate decisions and exact scope

| Gate | Verdict | Exact scope |
|---|---|---|
| Freeze integrity | PASS | All 19 frozen file SHA256 values checked before copying and again after review; own frozen copy only used for working materials. Freeze manifest itself also recorded. |
| Primary source | PASS | Actual arXiv:2405.13618v2 body, Definition 1.1, equation (1.5), Example 4.6 and Conjecture 4.7 read. Literal strict displayed inequality, with a!=b as source equation (1.7) conventions require. |
| Journal-source equality | HOLD | Journal body not independently obtained/read; no identity with v2 asserted. Search snippets are not body clearance. Inherited timeout/TLS limits respected. |
| Stable comparison and transfer | PASS | Both branches, arbitrary distinct positive inputs, no reliance on monotonicity in the exponent p. |
| A positivity and analytic reduction | PASS | All t>0; positive denominators; removable zero limit used only at t=0. |
| Finite exact arithmetic | PASS | Independently reconstructed all derivatives n=0..299, matched every supplied even derivative n=0..298; zeros below 10 and odd derivatives, positive even derivatives from 10 through 298. |
| All-order tail | PASS | Every even n>=300, with largest exponents ±(7+sqrt17), all others strictly below 41/4 in absolute value. Entire convergence closes every t>0. |
| Stronger terminology | HOLD | “(Bp,Bq)-super-stabilizable” additionally requires M between Bp and Bq. This proof establishes the displayed conjecture; it does not prove that separate sandwich. Do not promote terminology without an additional proof. |
| Full substantive mathematical scope | PASS | Full displayed conjecture, not a helper, local expansion, domain repair, or one-branch instance. Both branches form one result, never separate credits. |
| Substantive eligibility / nonroutine subsumption | HOLD | No complete classical subsumer identified in bodies read; this is not universal nonexistence evidence. Strong ratio comparison is the outstanding nonclassical content. Final eligibility requires broader closest-body comparison and source-access follow-up. |
| Current public registry / bounded novelty | HOLD | Live indexed registry searches performed, no exact matching proof located. Complete cached trees screened with hashes and original dates; these are dated, not current-head receipts. GitHub API limit and MathDB403 inherited restrictions not retried or bypassed. Current full registry bodies/head equality remain uncertified. |
| Formal certificate | HOLD | No full Lean source/endpoint, axiom audit or strict replay supplied. Arithmetic checker PASS is expressly not formal PASS. |
| Paper / extracted replay | HOLD | No finished reviewed paper or fresh extracted formal packet in this candidate. |

No mathematical FAIL was found. HOLD gates are not waived by the mathematical PASS.

## Independent derivation

Put d=sqrt17, alpha=(5+d)/2, beta=(5-d)/2. Then alpha beta=2, alpha+beta=5 and alpha-beta=d. Let

S(a,b)=[(beta/alpha)(b^alpha-a^alpha)/(b^beta-a^beta)]^(1/d).

For either (p,q)=(d,beta) or (-d,alpha), r=p+q is the other member of {alpha,beta}, and directly

S(a,b)^p=(q/r)(b^r-a^r)/(b^q-a^q).

The negative branch follows by reciprocation, not by an inequality operation. If a<b and c=Bq(a,b), then a<c<b and c^q-a^q=b^q-c^q=(b^q-a^q)/2. Thus the average of S(a,c)^p and S(c,b)^p equals S(a,b)^p. Applying the injective positive p-th-power map backwards yields Bp(S(a,c),S(c,b))=S(a,b) for either sign. This is the classical Stolarsky identity, uncredited independently of the source's Theorem 3.1.

Set t=log(b/a)/2, x=log(c/a)/2, y=log(b/c)/2. These are positive and x+y=t. Homogeneity makes the logarithm of S/M depend only on the half-log-ratio. If k(t)=log S(e^-t,e^t)-log M(e^-t,e^t) is strictly increasing, then

M(a,c)>exp(-k(t))S(a,c),   M(c,b)>exp(-k(t))S(c,b).

For all real nonzero p, partial differentiation gives ∂Bp(u,v)/∂u=(1/2)u^(p-1)Bp(u,v)^(1-p)>0, and similarly for v. Consequently the resultant is strictly greater than exp(-k(t))S(a,b)=M(a,b). This explicitly resolves the possible negative-p sign objection. Symmetry handles a>b; diagonal equality is never claimed strict.

The centered formulas derived directly from (1.5) are

g=log(sqrt2 sinh(t)/atan(sqrt2 t)),
f=(1/d)log[beta sinh(alpha t)/(alpha sinh(beta t))].

Define B=sinh(t)sinh(alpha t)sinh(beta t)>0 and

A=cosh(t)sinh(alpha t)sinh(beta t)
  -(sinh(t)/d)[alpha cosh(alpha t)sinh(beta t)-beta sinh(alpha t)cosh(beta t)].

This construction, independently used in the checker, gives A/B=coth(t)-f'(t). Hyperbolic products reduce A and B exactly to the displayed candidate formulas. The independent sparse-ring equality checks these identities literally, not at sampled t.

For every even n>=2,

2 A^(n)(0)=4^n+[(5/d-1)/2](d+1)^n-[(5/d+1)/2](d-1)^n>0.

Indeed 4<d<17/4, (5/d+1)/2<9/8, d-1<13/4 and (16/13)^2>9/8. Thus the first term alone dominates the negative term, and the middle term is positive. A(0)=0 and A is even entire, so A(t)>0 for every t>0. Direct leading orders give A=2t²+O(t⁴), B=2t³+O(t⁵).

Let T=1+2t², D=TA, J=sqrt2 B/D. Direct quotient differentiation gives

J'-sqrt2/T=sqrt2 [B'D-BD'-TA²]/D².

The square-bracket numerator is exactly E=T(B'A-BA'-A²)-4tBA. This independent route avoids assuming the supplied U,V decomposition. J tends to zero at zero. The all-order certificate below makes E>0 for every t>0, so J-atan(sqrt2 t) is strictly increasing with zero limit at zero and is positive. Since all quantities in the reciprocal comparison are positive,

k'=sqrt2/[T atan(sqrt2 t)]-A/B>0.

The transfer then proves the full source inequality. No finite interval is left untreated.

## Independent exact checker and the all-order argument

`independent_exact.py` was written for this review without reading/importing any candidate checker. It constructs A from the coth numerator above and B from three sinh factors. A dictionary in Q(sqrt17) represents polynomial-in-t exponential terms with rational half-integer exponent coordinates. It constructs E directly by the quotient-rule numerator, differentiates its exponential terms via exact moments, and includes falling-factorial contributions from t and t². It does not read the supplied certificate to generate its values. A separate subsequent comparison matched all 150 supplied even values.

Hard address-space cap is 536870912 bytes; hard CPU cap 40 seconds; external timeout 50 seconds; BLAS/OMP/MKL/NumExpr threads one. One bounded run passed in under a second; final reproduction passed under the same limits. No limits were raised. The only tooling failure was an initial local registry JSON reader assuming an object where a list occurred, retained in `failures.log` and corrected locally. No diagnostic or mathematical run failed.

For E(t)=sum e_n t^n/n!, independent exact output establishes e_n=0 for n<10 and odd n<=299; all even 10<=n<=298 are positive. The first four are 37847040, 19891322880, 5550283554816, 1162696473968640. Full values and every E term are retained in `independent-evidence.json`.

Write E=U+tV+2t²U. Sparse-ring output establishes this identity and even/odd parity, not just the finite Taylor parity. With L=7+d and R=41/4, the coefficients at +L are

u=(-85+21d)/544>1/1000,
v=(17-5d)/272>-1/50;

at -L they are u and -v. Every other exponent has absolute value strictly below R. Exact total l1 norms, including the dominant terms, are

sum |u_lambda|=(53+13d)/17<10,
sum |v_lambda|=7/4+25d/68<10.

These equalities and strict inequalities use exact field signs by rational squared comparisons. There is no floating-point radical approximation. Also 11<L<12. For even n>=300, the two extreme terms contribute

2L^(n-2)[uL²+nvL+2n(n-1)u].

Its bracket exceeds .002n(n-1)-.24n = .002n²-.242n >= .001n² (already valid for n>=242). All other terms together have absolute contribution at most

R^(n-2)[10R²+10nR+20n(n-1)] <22n²R^(n-2).

For the latter uniform inequality, divide by n²: 20+(10R-20)/n+10R²/n² decreases on n>0 and its exact rational value at 300 is below 22. Thus

e_n>n²[(1/500)L^(n-2)-22R^(n-2)]>0,

because L/R>44/41>1 and 44^298>11000*41^298, independently checked as an integer inequality. This is a proof for ALL even n>=300, not a finite numerical extrapolation. Entire convergence of the finite exponential polynomial with polynomial prefactors allows its Taylor series at every real t. Hence E(t)>0 for every t>0.

## Primary bodies and independent substantive objection

The hashed arXiv body literally gives the M2 formula in (1.5) and conjectures M2-R(Bp,M2,Bq)<0 with p=5-2q and q=(5±sqrt17)/2. Its preceding Example 4.6 already gives the sixth-order local sign; that observation is known and uncredited. Definition 1.1(3) separately says “and M is between K and N.” The displayed conjecture alone is the scope reviewed here.

I read the actual pinned Raissouli 2011 Theorem 3.1 and telescoping proof: E_(p,q) is (B_(q-p),Bp)-stabilizable. This fully subsumes the stable identity and gives it zero independent eligibility. I also read actual 2012 Theorems 3.1–3.3 and proofs. Theorem 3.3 would give R(Bp,M,Bq)<S from M<S, whereas the desired claim is M<R(Bp,M,Bq). It does not compare the two quantities on the same side of S. The paragraph immediately after (3.16) explicitly asks when an iteration improves bounds as in (3.17); no sufficient criterion answering that question is given there. Thus using this theorem as an automatic resolution would be an invalid implication.

The 2016 actual Theorems 4.1, 4.2 and 4.4 and proofs were read. The latter two impose arithmetic outer mean, curvature, and a particular arithmetic-power sandwich. Neither outer power here is 1. A power-coordinate conjugation changes the inner function and its curvature/sandwich hypotheses; those hypotheses do not follow simply from the classical Stolarsky identity or the conjecture's local coefficient. I do not assert that no such conjugation theorem exists elsewhere. The reciprocal-arctan PDF is frozen but none of its theorems is needed or claimed independently cleared in this review.

**Strongest objection:** a published ratio-monotonicity or general stabilizable-mean theorem could already imply this exact k'(t)>0, or the nested inequality directly, with routine verification. The stable S identity and transfer mechanism are classical; only the full specialized ratio comparison can potentially carry substance. The exact proof is valid without settling priority or routine subsumption. Complexity or the 145 positive coefficients does not itself establish novelty. No known complete subsumer was found in the bodies actually read, but I retain substantive HOLD rather than treating an incomplete search as clearance.

**Falsifiers:** (i) an exact nonpositive even derivative at n>=10 in the asserted E certificate, or an omitted exponent of absolute value >=41/4 other than ±L, would invalidate this proof path; these were independently checked/controlled as above. (ii) A pair a!=b>0 with resultant<=M in either branch would refute the theorem; the proved analytic chain rules it out subject to the exact certificate. (iii) An earlier primary theorem with the literal same centered M2 and S ratio monotonicity, or a fully verified generic theorem substitution producing both full-domain branches, falsifies substantive eligibility even if the proof remains mathematically correct. A title, abstract, open registry status or mere M<S does not suffice for (iii).

## Provenance and remaining limits

See `provenance.json`, `hash-before.json`, `hash-after.json`, and `dated-registry-screen.json`. Five source files are copied unchanged with their frozen hashes; the body comparisons above rely only on the first, second, fourth and fifth relevant sources (not the unused reciprocal-arctan paper). Original retrieval dates are preserved. Dated registry files are independently hash-verified and screened; fresh live web/index searches are explicitly distinguished from authoritative current-head checks. API/403/challenge restrictions were not bypassed. No worldwide priority claim, current full-text registry clearance, journal equality, formal PASS or acceptance is made.
