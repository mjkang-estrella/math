# r49 research record: Wright-density criterion, unresolved

Credit **0**. No nomination, eligibility PASS, full proof, Lean or paper. Counts observed: six additional, 36 total. Root owns all gates. Only one actual source conjecture was screened and pursued. This is a continuation of r47's abandoned lead, with a new explicit positive-kernel variance route; it is not presented as an unseen lead.

## Source and literal scope

Ferreira–Simon, *On the Log-Concavity of the Wright Function*, Constructive Approximation 60 (2024), 309–338, DOI 10.1007/s00365-023-09666-w; published online 24 August 2023. Actual publisher full HTML Section 6.4 and Theorems A–D/Sections 3–5 were read, not just metadata. ArXiv2212.07974 latest is v2, 28 August 2023, after v1 of 15 December 2022. Its actual Section6.4 matches the publisher statement. Exact bytes and UTC are in http.jsonl.

For admissible a in [0,1], b>=0, define M_(a,b) by moments
E M^s = Gamma(a+b) Gamma(1+s)/Gamma(a+b+a*s), s>-1,
with the source's limiting interpretation at a=b=0. For 0<a<1 its density is
f_(a,b)(x)=Gamma(a+b) W_(-a,b)(-x), x>0,
W_(rho,b)(z)=sum_(n>=0) z^n/(n! Gamma(b+rho*n)).
For b in(0,1), a_*(b) is the unique a in(0,1) solving
rgamma(b-a)^2=rgamma(b)rgamma(b-2a).
Set a_*(0)=1 and a_*(b)=1 for b>=1. The conjecture is the equivalence, for **all** admissible pairs, of
(1) a<=a_*(b),
(2) log-concavity of the density of M_(a,b),
(3) convexity of t -> 1/E_(a,a+b)(-t) on t>0.
Here E_(a,c)(z)=sum z^n/Gamma(c+a*n). At a=0 the distribution is exponential; at a=1,b>0 it is Beta(1,b). The degenerate point (1,0) is recorded by the source as a point mass. No claim is made from the literal density wording at that point: any intended endpoint convention is to be preserved, never exploited for credit.

The substantive missing density-sufficiency statement is: for every 0<a<1,b>=0 with a<=a_*(b), f_(a,b) is log-concave on all x>0. Source TheoremD(a) gives the converse. Section4 gives the log-concavity-to-reciprocal-convexity transfer, and Section6.4 gives its necessary condition. Thus the full density sufficiency would close the nondegenerate substantive conjecture, not merely a parameter instance.

## Distinctness and early eligibility screen

This is not the credited Mills-ratio complete-monotonicity refutation (first-batch18), nor the accepted Gamma level-curve convexity, nor the held complex Mittag-Leffler modulus question. It concerns a two-parameter family of probability densities and their ordinary spatial log-concavity, with genuine unproved ranges b<a and a>4/5,b=0. The known a=1/2 Mills/Sampford specialization is not pursued or counted. That distinction permits research, not a novelty/substantive PASS. The elementary full-kernel reductions below are helpers and never credits.

Primary antecedents read: source TheoremB proves exactly b=1-a, TheoremD(b)(i) exactly b=0,a<=4/5, and D(b)(ii) exactly b>=a. Their proofs and Remark4 were read: fractional integrals of order<1 explicitly fail to preserve log-concavity, and finite beta grouping stops at the stated parameter bounds. No reuse of those theorems closes the missing ranges.

The second primary body is Hasebe–Simon–Wang, *Some properties of the free stable distributions*, arXiv1805.01133, Section2.1 Eqs(4),(6), and selected Section3.8. Its classical positive-stable/Kanter identity is a dependency, not a second screened problem. Results about free stable whale-shape or Gamma2 mixtures concern other densities and do not supply the variance bound below. No unrelated open problem from this paper is selected.

Current registry refresh preceded investment: Omega dev e1d4e12fbc1f1f82e5f88362e931a52c778b4374. Compare from r47's 9fabd81524aa5bc037d66794c239ac6b9d2b4e86 shows seven commits, two Blueprint documentation/scribe files on compact root coherence. Actual patches are in sources/delta.json and were read. They are not probability claims. The complete named D5 (12552 entries) and Problems (1551 entries) caches are unchanged in this delta; those scopes are reused byte-for-byte with original r47 hashes. This does not establish absence throughout dev. Four other heads remain unchanged (registry-screen.json). Complete named cached OpenAI preprints/AIM/Count/main scopes reused, no whole-repository semantic completeness claim.

Actual lexical-match bodies were read: AIM322 is a delay equation with negative Schwarzian derivative; Omega FerreiraOddPowerResidueRadical is an odd-modulus residue/radical identity; Omega KilbasSaigo is a different three-parameter entire-function sandwich. Their actual definitions and theorem bodies establish mismatch, not labels. Bounded current search and Simon's public publications page did not locate a full matching settlement; this is not priority clearance. No known theorem is nominated, no absence-of-hit proof of novelty.

## Positive representation, derived with all constants

Write p=1/(1-a)>1 and
U_a(theta)= sin((1-a)theta) sin(a theta)^(a/(1-a)) / sin(theta)^p,
0<theta<pi.
Kanter's source identities give Z_a=L^(1-1/a) K_a and
K_a=sin(a theta) sin((1-a)theta)^((1-a)/a)/sin(theta)^(1/a),
where L is unit exponential, theta uniform(0,pi), independent. Hence
M_(a,1-a)=Z_a^(-a)=(L/U_a(theta))^(1/p).
Equality follows also from the exact Mellin transform; the densities are determined, for example by the moment generating function supplied by the source. Conditioning on theta gives its density p*x^(p-1)/pi times integral U_a exp(-U_a*x^p) dtheta.

The entire-series identity W_(-a,0)(-x)=a*x*W_(-a,1-a)(-x) follows coefficientwise from rgamma(z)=z*rgamma(z+1). Consequently
f_(a,0)(x)=Gamma(1+a)*p/pi * x^p * integral_0^pi U_a(theta)exp(-U_a(theta)*x^p)dtheta.       (A)
The Gamma(1+a) factor is essential; omitting it would give the wrong normalized density.

For b>0 let gamma=b/a. The source fractional-integration identity gives
f_(a,b)(x) = Gamma(a+b)/(Gamma(a)Gamma(gamma))
 * integral_0^infty s^(gamma-1) f_(a,0)(x+s) ds.                 (B)
Substituting (A) is a positive double integral with coefficient a*p*Gamma(a+b)/(pi*Gamma(gamma)) and kernel
s^(gamma-1) U_a(theta) (x+s)^p exp(-U_a(theta)(x+s)^p).          (C)
These are exact identities, not an approximate density model. Tonelli applies to the positive kernels. For differentiation at any x>0, restrict x to a compact subinterval of(0,infinity); the lower bound U_a>=c_a>0 and exponential decay dominate all fixed derivative factors, including theta->pi and s->infinity; gamma>0 handles s=0. Thus differentiating twice is justified without an asymptotic interchange assumption.

## All-parameter variance target

Let P_(a,b,x) be the probability on(s,theta) obtained by normalizing (C), and t=x+s. Define
S=p/t-p*U_a(theta)*t^(p-1),
D=p/t^2+p*(p-1)*U_a(theta)*t^(p-2).
Differentiation of the normalized positive integral proves
(log f_(a,b))''(x) = Var_P(S)-E_P(D).                         (V)
For b=0, let y=x^p and let E_y denote the law proportional to U_a(theta) exp(-y U_a(theta))dtheta. Then (V) simplifies to
x^2(log f_(a,0))'' = -p-p*(p-1)*y*E_y U_a+p^2*y^2*Var_y U_a. (V0)

A concrete full-scope route is therefore to prove Var_P(S)<=E_P(D) whenever a<=a_*(b), for all x>0 (using V0 for b=0). This is an explicit inequality for elementary positive kernels and their first two moments, with no Wright zeros or cancellation in its statement. It is NOT proved here. In particular, deriving it does not resolve the source or qualify as an additional outcome.

## Rigorous analysis of the Kanter-specific obstacle

The beta0 slice is necessary for the full conjecture, so understanding it is not a substitute partial-family nomination. U_a is strictly increasing from c=(1-a)*a^(a/(1-a)) to infinity. Indeed, with h(z)=z*cot(z), h'(z)<0 on(0,pi); multiplying (log U)' by (1-a) gives
[(1-a)h((1-a)theta)+a*h(a theta)-h(theta)]/theta>0.

Change variable u=U_a(theta), and put w(u)=u/U_a'(theta(u)). The tilt in V0 has density proportional to w(u)e^(-yu) on(c,infinity). Taylor expansion and the other endpoint give, with A=sin(pi*a)^p,
U_a(theta)=c*(1+a*theta^2/2+O(theta^4)),
U_a(theta)=A*(pi-theta)^(-p)*(1+O(pi-theta)),
w(u)~sqrt(c/(2a))*(u-c)^(-1/2) as u downarrow c,
w(u)~A^(1/p)/p*u^(-1/p) as u->infinity.
These expansions can be differentiated since the underlying sine expressions are analytic locally in theta or pi-theta. For H(u)=(u-c)*(log w)'(u) they imply
H(c+)=-1/2, H(infinity)=-1/p.
Thus for every a>1/2, H cannot be nonincreasing. This includes the entire difficult a>4/5 beta0 range.

Integration by parts, whose boundary terms vanish by these expansions, yields exact Stein identities
y*E_y(U-c)=1+E_y H,
y*Var_y(U)=E_y(U-c)+Cov_y(U,H).                           (S)
A tempting sufficient condition H<=0 with H nonincreasing would give y*E(U-c)<=1 and y*Var(U)<=E(U-c). Writing r=y*E(U-c), these imply
p*y^2 Var(U)<=p*r<=1+(p-1)*(r+y*c),
which proves V0. But the required monotonicity is rigorously impossible at a>1/2. One must control the positive covariance in (S), not silently discard it. This is a route obstruction only: its hypotheses are stronger than the source's hypotheses.

The endpoint expansions nevertheless localize the problem. At y downarrow0, regular-variation Laplace scaling gives y*E U->a and y^2 Var U->a. Thus the right side of V0 tends to -1, agreeing with f_(a,0)(x)~constant*x near0. At y->infinity, Watson scaling at c gives E U=c+1/(2y)+O(y^-2), Var U=1/(2y^2)+O(y^-3), and the right side of V0 equals -p*(p-1)*c*y-p/2+O(y^-1). These follow by substituting v=y*(u-c) into the stated w expansion, respectively v=yu at infinity; the exponential permits domination after splitting off a fixed endpoint neighborhood. Hence for each fixed a the beta0 curvature is negative near both ends. The remaining interval is parameter-dependent and cannot be covered uniformly by a finite numerical grid, particularly as a->1.

## Strongest exact falsifier of a generic shortcut

Positivity and log-concavity of each conditional kernel cannot by themselves prove (V0). At p=6 take the unrelated two-atom mixing measure U=1,5 with original weights 1,e^4/5 in the integral U*exp(-yU). At x=1, the tilted masses are equal. Mean=3, variance=4 and
x^2(log[x^6*(exp(-x^6)+exp(4)*exp(-5*x^6))]))'' at x=1
= -6-6*5*3+36*4 =48>0.
Each individual x^6 exp(-u*x^6) has strictly negative log curvature on x>0. Thus positive mixing destroys the required property even for this highly tractable kernel. The mixing law is NOT the Kanter law: this is explicitly NOT a source counterexample.

## Validation, remaining gaps, decision

run.sh/capped_run.py impose per-process AS512MiB and CPU210 seconds, wall230 seconds, sampled process-group RSS512MiB/CPU210 seconds, BLAS1. Sampling can miss transients; reaped children are not included in later CPU samples. No broad enumeration. check.py compares (A), its score and its log curvature against independent literal entire-series derivatives at eight fixed identity probes, including a=.9; three small-angle probes corroborate the expansion, and exact integer arithmetic checks the generic mixture obstruction48. These are diagnostics, not proof of the conjecture or of the asymptotic remainder estimates. 45-digit arithmetic; all eight errors <1e-30. Guard exit0, about3.44s wall, sampled19.24MB groupRSS.

Precise mathematical gap: a uniform, Kanter-specific variance/covariance estimate proving (V) on the entire permitted gamma-threshold set. Even beta0 requires a nonmonotone-score covariance estimate that the source beta-product/bell-shape theorems do not give. For b>0, no reduction has removed the coupled s/theta variance. Critical-threshold equality cases are not certified by a positive origin value. No actual source counterexample was found.

Precise eligibility gap: no full ordinary result, no independent adjudication, bounded nonexhaustive citing/registry investigation, no worldwide novelty guarantee. Actual published source is available, so its text is not an access gap. Kanter1975 original article itself was not fetched; Hasebe–Simon–Wang's explicit source identities (and their attribution) are the read primary antecedent. Source bibliography's full Yamazato/other books were not exhaustively audited. All lane fetches200; no403/429/challenge or bypass. No git, other-lane writes, browser/account/contact/post/upload actions, children, or paper/Lean investment.
