# Proposed resolution of Simon's threshold-convexity question

Status: complete proposed mathematical proof; independent source/novelty/eligibility
review, full literal Lean endpoint and manuscript NOT YET obtained. Credit0.
This is the separate last paragraph of Section3, p5, of Simon2012.11018v2.
It does NOT settle MathDB349140's main complete-monotonicity conjecture.

Fix gamma>1. For 0<alpha<1/gamma, define exactly as in the source
 beta_gamma(alpha)=inf{beta>0: z+gamma(z^(beta-alpha)-z^beta)<=1 for every 0<z<1}.

Proposed theorem: beta_gamma is C-infinity and strictly convex on (0,1/gamma).
In particular it is convex as explicitly conjectured in the source. The slope
and curvature below give one combined characterization, not extra outcomes.

1. Exact variational reduction

Put z=exp(-t), t>0. The literal criterion is equivalent to
 beta >= G(alpha,t):=alpha+[log gamma+log(1-exp(-alpha*t))-log(1-exp(-t))]/t
for every t>0. No complete-monotonicity conjecture is used in this equivalence.

Define
 h(x)=log(1-exp(-x))-x/(exp(x)-1), x>0.
Then
 h'(x)=x*exp(x)/(exp(x)-1)^2>0,
 q(x):=x*h'(x)=[x/(2*sinh(x/2))]^2
is strictly decreasing. To verify the last assertion, sinh(y)/y is strictly
increasing for y>0: y*cosh(y)-sinh(y) has derivative y*sinh(y)>0 and value0 at0.
Equivalently, differentiate q using exponentials. This is classical calculus,
credited as a tool, not a new claim.

For fixed alpha in(0,1/gamma), alpha<1. Let
 K_alpha(t)=h(t)-h(alpha*t).
Its derivative is [q(t)-q(alpha*t)]/t<0. Moreover
 K_alpha(0+)=log(1/alpha)>log gamma,
 K_alpha(infinity)=0<log gamma.
The limits follow from h(x)=log x-1+O(x^2) near0 and h(x)->0 at infinity.
Thus there is a UNIQUE tau=tau_gamma(alpha)>0 with
 h(tau)-h(alpha*tau)=log gamma.                         (E)

Direct differentiation gives
 partial_t G(alpha,t)=[K_alpha(t)-log gamma]/t^2.
It is positive before tau and negative after tau, so G has a unique global
maximum there. Put B(alpha)=G(alpha,tau).
This maximum is greater than alpha>0: for sufficiently large t,
log gamma+log(1-exp(-alpha*t))-log(1-exp(-t))>0.
Consequently the literal feasible beta-set is exactly [B(alpha),infinity).
Its infimum over beta>0 is B(alpha). In particular the infimum is attained;
this rigorously identifies B with the source beta_gamma.

2. Smoothness and convexity

K_alpha'(tau)=h'(tau)-alpha*h'(alpha*tau)<0. The ordinary smooth implicit
function theorem applied to(E) shows tau_gamma is smooth locally at every
alpha in(0,1/gamma). Uniqueness identifies the local branches globally.

Write s=alpha*tau and H=h'(tau)-alpha*h'(s)<0. Implicit differentiation yields
 tau'=tau*h'(s)/H,
 s'=tau+alpha*tau'=tau*h'(tau)/H<0.                    (D)

Because partial_t G(alpha,tau)=0, differentiating the attained value gives
 beta_gamma'(alpha)=partial_alpha G(alpha,tau)
                  =1+1/(exp(s)-1)=1/(1-exp(-s)).       (S)
The last function is strictly decreasing in s>0, while(D) says s is strictly
decreasing in alpha. More explicitly,
 beta_gamma''(alpha)
   =- exp(-s)/(1-exp(-s))^2 * tau*h'(tau)/H >0.         (C)
This proves strict convexity on the entire literal source interval. It uses
no finite computation, no unproved CM necessity, and no residual optimizer
existence/regularity assumption: all are established above.

3. Scope and obligations

The main conjecture (CM iff criterion) remains open here. We prove only the
separate explicit all-gamma threshold-convexity question in the SAME source.
Known sufficient CM cases, monotonic beta/alpha, calculus tools and numerical
checks are uncounted. Need full Lean source infimum and convexity endpoint;
conditional curvature for an assumed stationary branch is not sufficient.
Prior-art/eligibility screening remains bounded and not yet independently
reviewed. Actual published T&F body returned403; source v2 and author list read.
No worldwide priority claim, no credit or external posting.

4. Simpler self-contained convexity proof (primary formalization route)

There is a shorter proof of exactly the source conjecture, requiring neither
stationarity nor implicit differentiation. Let f(t)=-log(1-exp(-t)), t>0.
Its derivative is -1/(exp(t)-1), strictly increasing, so f is strictly convex.
Changing optimization variable to s=alpha*t gives
 beta_gamma(alpha)=sup_{s>0} J_s(alpha),
 J_s(alpha)=alpha + (alpha/s)(log gamma-f(s)+f(s/alpha)).
For fixed s>0, the nonlinear term alpha*f(s/alpha) is the classical positive
perspective of f and is convex in alpha>0. The other terms are linear. Hence
J_s is convex, and its pointwise supremum is convex wherever finite.

All literal-infimum bridges can be proved without assuming source results:
(i) beta=alpha+1 satisfies the exponential criterion whenever gamma*alpha<=1:
  1-exp(-alpha*t)<=alpha*t,
  t*exp(-t)<=1-exp(-t),
so gamma*exp(-t)*(1-exp(-alpha*t))<=1-exp(-t).
Thus the supremum is bounded by alpha+1.
(ii) f(s)->0 as s->infinity. Choose s>0 with f(s)<log gamma.
Since f(s/alpha)>0, J_s(alpha)>alpha>0. Thus the supremum is positive.
(iii) The exact logarithmic criterion is beta>=J_s(alpha) for every s>0.
The feasible positive-beta set is therefore [sup J_s,infinity), proving its
literal infimum equals sup J_s, with no attainment premise left unproved.

This route should be presented candidly as a resolution by standard perspective
convexity after reparameterization. It could be judged too immediate for the
campaign's strict novelty/eligibility standard; an INDEPENDENT judgment is
required before count or heavy investment. The stronger unique maximizer/smooth
strict-curvature route in Sections1-2 is mathematically separate evidence, not
additional discovery credit. Formalizing only a conditional branch is forbidden.

Numerical check note: an initial70-digit relative finite-difference test at
gamma1.01, alpha=.01/gamma could not resolve curvature about2e-285; it failed
from inadequate precision in the difference, not negative curvature. The saved
30-case check uses alpha fractions.1,.3,.5,.9,.99,.999 and passes. No rigorous
sign conclusion is inferred from those finite differences.
