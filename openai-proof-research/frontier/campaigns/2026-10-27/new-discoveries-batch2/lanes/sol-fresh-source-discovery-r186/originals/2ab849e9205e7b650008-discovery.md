# r69: squared-radius log-convex convolution — unresolved

Decision: no full source resolution, no nomination, credit 0. No PROOF.md or Lean. Root alone decides acceptance; campaign stays 7 additional / 37 total.

## Context and selection

Read ancestor research AGENTS.md, batch AGENTS.md, ledger.json, prior-campaign-context.json, current NEXT.md, r64/r65/r66 SUMMARY.md, and root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json. The 37 accepted families were screened before selection. The user-supplied excluded/exhausted families were not revisited. No arithmetic/algebra or combinatorics target was selected. Only two attributed primary questions were screened:

1. **Interior versus boundary mean distance**: MO509554 (AspiringMat, 26 March 2026; expert partial reduction by Iosif Pinelis). For every planar convex body K, independent uniform area points X,Y and independent uniform arclength boundary points X',Y', is E||X-Y|| <= E||X'-Y'||? EXCLUDE: Eric Shen, arXiv2608.06470v3, 3 September 2026, Theorem1.2 and Corollary3.10 explicitly prove the whole planar statement. Actual theorem and proof paragraphs read, including angular projection and the Gini comparison. No special-case or new-credit claim. This question's original poster's research credentials were not established; Pinelis's mathematical contribution is attributed separately.
2. **Squared-radius log-convex convolution**: MO476529, japalmer, asked 7 August2024 14:58, edited27August2024 16:57. For EVERY pair of probability densities p,q on R satisfying p(x)=p(|x|) and convexity of t -> log p(sqrt(t)) on [0,infinity), is p*q in the same class? Selected. No restriction to identical inputs, smooth inputs, Gaussian scale mixtures, finite variance, or a finite breakpoint family is part of the source. Real-valued logarithms mean positive values; no exploitation of density modifications on null sets or endpoint wording is intended. Current web-readable body has no posted answer. That is not evidence of novelty.

japalmer's terminology and class match Jason A. Palmer's author-hosted research paper *Strong Sub- and Super-Gaussianity* (with Kreutz-Delgado and Makeig, 2010), but a verified identity link from the username to the named author was not obtained. Expert-authorship attribution is therefore **HOLD**, rather than an invented identity. This eligibility uncertainty independently prevents nomination.

## Primary theorem and registry comparison BEFORE sustained work

Author-hosted Palmer et al. PDF read: Definition1, Sections2.2–2.3, Theorems3–6, and conclusion. The exact class is SS+. Section2.3 explicitly states strict inclusions GSM < SS+ < M²(2). Theorem4 states M²(m)*M²(n) lies in M²(min(m,n)); Theorem5 concerns convolution of a star-shaped function with an M²(2) density. Neither theorem is the target SS+ closure. Theorem6 concerns ICA separating local optima. It does not assert closure of SS+. Its use of the larger M²(2) class cannot be reversed.

Brascamp–Lieb, *Some Inequalities for Gaussian Measures*, actual Theorems1.2 and1.3 read: integration preserves pointwise log-convexity in the retained variable; ordinary convolution preserves log-concavity. The squared-radius transformed convolution is not a direct instance of either statement. The pointwise obstruction below shows why.

Inspected saved actual Lean D5 tree and Problems tree from sol-polyomino57-source-prior-refresh-r3/live, with paths/hashes recorded in context-screen.json. This is NOT r57's Blueprint tree. Relevant lexical paths included IndependentConvolutionL1Minimum, KarpZhangReciprocal/IntervalConvolution, and Fourier convolution modules, but no named SS+/Palmer closure endpoint. Read actual immutable Problems/metya-mukherjee-independent-convolution-l1.md and D5/S3/TotalVariation/IndependentConvolutionL1Minimum.lean at 6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3. The latter's definitions and result quantify finite real simplex vectors and minimize their discrete output's full L1 distance from uniform. Different target; no subsumption bridge. Reading external Lean is not compilation or truth certification.

The inherited API403 remains respected. No new GitHub API request, blind retry, alternate-identity request, or bypass was made. No reset information was found in inspected inherited records. 6c27b0a... was last observed at15:49; it is NOT asserted to be current HEAD. Saved-tree lexical screening does not clear the current delta or all semantically related bodies. Broad current-registry freshness **HOLD** remains. Targeted live public search found primary class/mixture results but no full closure solution; absence of search hits is not clearance. MO direct HTTP returned403; readable public web-tool bodies were used and manually recorded in sources/source-read.md, without browser or account action.

## Route A: exact conditional score criterion

For positive C² inputs with enough domination for differentiating twice, let

r(x)=integral p(x-y)q(y)dy, L=log r, H(t)=L(sqrt t).

Direct chain rule gives, for x>0,

4x³ H''(x²) = xL''(x)-L'(x)
 = [x(rr''-r'²)-rr']/r².                                      (1)

Writing psi=p'/p and E_x for density p(x-y)q(y)/r(x), differentiation of the quotient gives

L'=E_x psi(x-Y),
L''=E_x psi'(x-Y) + Var_x(psi(x-Y)).                            (2)

The source hypothesis supplies z psi'(z)-psi(z)>=0 for z>0, extended evenly for the ratio psi(z)/z. It does NOT directly give

x E_x psi'(x-Y) - E_x psi(x-Y)
 + x Var_x(psi(x-Y)) >=0.                                    (3)

In particular x-Y can have either sign, and multiplying the source inequality by x/(x-Y) is unjustified. Even unimodality of the conditional measure is not available for arbitrary SS+ factors. Equation(3) is an exact smooth-case target, not a proved inequality. A full route must establish this sign for all legal inputs, and justify approximation for nonsmooth inputs. No moment assumption may be added to the source.

## Route B: folded-integrand curvature and an exact obstruction

For t>0 fold y onto [0,infinity):

K(t,y)=q(y)[p(sqrt t-y)+p(sqrt t+y)], R(t)=integral_0^infinity K(t,y)dy.

Whenever derivatives are integrable, set A=partial_t log K and B=partial_t² log K. Under normalized weight K/R,

(log R)'' = E B + Var A.                                    (4)

Proof: R'/R=E A; R''/R=E(B+A²), then subtract (R'/R)². This addresses the entire smooth class, with no truncation to examples. To prove closure it is sufficient, and in this regular setting necessary, to establish E B+Var A>=0. The integrand need not be log-convex.

Indeed take p(z)=exp(-a z²), q(z)=exp(-b z²), with a,b>0; normalizing constants are immaterial. Then

K(t,y)=2 exp(-at-(a+b)y²) cosh(2ay sqrt t).

At t=0 the analytic extension gives

A(0,y)=-a+2a²y²,
B(0,y)=-(8/3)a⁴y⁴.

Thus B is strictly NEGATIVE at every y>0. This also persists for positive t close to zero. Brascamp–Lieb Theorem1.2 cannot apply pointwise even for Gaussian factors. This is an obstruction to a proof method, NOT a source counterexample.

Put c=a+b. The half-Gaussian weight at t=0 has E y²=1/(2c), E y⁴=3/(4c²), hence

E B=-2a⁴/c², Var A=+2a⁴/c², and their sum is exactly0.

The cancellation is all-parameter exact. A proposed argument discarding Var A or assuming B>=0 would already mishandle the source's Gaussian equality case. The missing general mechanism is a lower bound Var A >= -E B for arbitrary SS+ p,q. No such bound was proved here. A density outside SS+ is not a falsifier of this missing statement.

## Route C: heat-flow specialization and its boundary gap

Gaussian convolution may be approachable through a scalar PDE, but does not settle convolution by an arbitrary SS+ density. If u_tau=u_xx, write g(tau,s)=log u(tau,sqrt s). Calculation yields

g_tau=2g_s+4s(g_ss+g_s²).

For v=g_ss,

v_tau=4s v_ss+(10+8sg_s)v_s+16g_s v+8s v².                  (5)

At an interior first zero of v, this formally has the sign required by a maximum principle. This is NOT a completed positivity proof: the degenerate boundary s=0, infinity, growth, regularization, and first-contact attainment require actual analysis. Even a full Gaussian-kernel statement would be an uncredited specialization; it cannot extend to all SS+ by claiming that all SS+ densities are Gaussian mixtures. The published strict inclusion explicitly prevents that transfer.

## Adversarial finite checks, with no inference of a theorem

A test family genuinely outside the Gaussian-mixture subclass is

p(z)= exp(-az²) if |z|<=u;
      exp(-(a-b)u²-bz²) if |z|>u,

where a>b>0,u>0. Its log in z² is the maximum of two affine functions, so is convex. It is positive, even and integrable. The derivative jump at u² shows p(sqrt t) is not completely monotone, so the Gaussian-mixture proof does not cover it. This is a mathematical non-mixture witness, not an unresolved-source resolution.

Convolutions of two such densities have explicit finite Gaussian-integral formulas: split the y-axis at +/-u,x+/-v; on each interval the integrand is exp(C+D-A B x²/(A+B)) exp(-(A+B)(y-Bx/(A+B))²). scan.py implements the erf antiderivative. 600 deterministic random parameter pairs and30 abscissae per pair gave18000 floating diagnostics. No certified negative source sign was found. Minimum finite-difference score was -8.1583e-10, in a nearly pure-Gaussian tail. audit.py recomputes that particular case using65 decimal digits and analytic differentiation of the exact interval formula: actual numerical xL''-L' is +5.16221665e-25. Independent scaled quadrature agrees to relative1.65e-64. No numerical sign here is offered as a proof certificate.

The initial unscaled tail quadrature failed an excessively stringent relative-accuracy check; raw failure and original script retained. Scaling the integrand to order-one size fixed the diagnostic without changing resource limits or the mathematical formula. exact.py checks chain-rule, folded Gaussian coefficients, heat differentiation,64 rational Gaussian cancellation identities and three independent polynomial chain-rule instances. These are exact reproducible checks of the displayed reductions, not checks of the full source assertion.

## Strongest objection, falsifier, and precise remaining gap

**Strongest objection:** no uniform sign theorem has been established for either equivalent curvature criterion, and known closure results concern a strict subclass or a strict superclass. Finite positive samples provide no bridge. Moreover verified expert identity and current registry freshness remain HOLD.

**Falsifier:** any legal positive even p,q with convex log p(sqrt t), log q(sqrt t), and three nonnegative t0<t1<t2 violating the convex secant inequality for log(p*q)(sqrt t), or a rigorously certified negative (1) at an interior x in a smooth case, refutes closure. It must concern genuine SS+ inputs; an M²(2)-only or generic symmetric input does not suffice.

**Precise proof gap:** establish Var A >= -E B uniformly in (4), or prove (3) by a valid two-input structural inequality, then close nonsmooth/no-finite-moment approximation and source endpoint continuity. Alternatively supply a rigorous source-admissible negative witness. Neither route is complete. No novelty or acceptance claim is made.

Reproduce `sh run.sh` in this lane (Python, scipy, sympy, mpmath). All Python mathematical helpers run through copied capped_run.py: AS512MiB, sampled process-group RSS512MiB, CPU210s, wall230s,40ms sampling, BLAS1. Shard/reduce rather than raising caps. No git/shared/other-lane edits, children, browser, posting/contact/account/upload operations.
