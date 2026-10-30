# r53: beta-median source screen and incomplete uniform comparison

Credit requested: **0**. No complete source resolution, eligibility clearance, PROOF.md, Lean, or paper.

## Literal source and early screen (two candidate claims only)

1. Selected: Jouni Kerman, *A closed-form approximation for the median of the beta distribution*, arXiv:1111.0433v1 (only version in current submission history), November 2011. Actual six-page PDF read, particularly definition p1, formula (1) p3, relative-error paragraph p3 and sign/uniformity discussion p4. For a,b>1 the abstract asserts relative error less than 4% for Q(a,b)=(a-1/3)/(a+b-2/3). The body also includes a,b>=1 in the numerical discussion. The precise selected target is

   for every real a,b>1, with m uniquely defined by I_m(a,b)=1/2,
   |Q(a,b)/m(a,b)-1|<1/25.

   Endpoint extension a,b>=1 would be stronger, not a separate result. The sign observation for a<b, Q<m, is an intermediate objective, not separate credit. This is a published numerical assertion rather than a numbered open conjecture. No novelty follows from that distinction.

2. Richard F. Lyon, *A simple improvement on Kerman's approximation to the median of the beta distribution*, arXiv:2610.33859v1, posted 24 October 2026 19:05:32 UTC (only version in current history). Screened global pointwise improvement/error-ratio assertion in abstract and Section4: replacing g(x)=x-1/3 with g(x)=x-1/3+1/(36x), the error is smaller, with ratio at most 13/32 wherever Kerman's is defined. Actual Section3 Theorems1–2 and AppendixA read. They prove fixed-ray eventual comparisons and asymptotic relative errors, **not** the global numerical bound. Section4 explicitly describes a grid; Section8 gives its finite coverage. Not pursued as a second target: same beta-median mechanism, more difficult cancellations, substantial contemporary-source risk.

Theorem1 fixes r>1 and g(x)=x-1/3+c1/x+O(x^-2); its threshold is c*_r=8/405+4r/[405(1+r)^2]. Strict comparisons c1<c*_r and c1>c*_r give eventual lower/upper bounds along b=ra. Theorem2 gives error=-(1-1/r)(c*_r-c1)/a^2+O(a^-3). These are public proofs predating this lane and off limits as discoveries. Neither controls all finite a,b>1, nor the noncompact regime with one parameter fixed. The paper mentions a longer beta-bound manuscript; that body was not obtained or cleared. This is a concrete priority/coverage gap.

## Closest actual bodies checked early

- Arab–Oliveira–Wiklund, arXiv:2005.08204v4 (latest): Theorems1–3 classify stochastic/star/convex transform ordering of Beta(a,b) by opposite parameter directions. Corollary13 gives mode–median–mean ordering. These give no immediate control of Q/m; scaling changes the support and both shape effects. No claim that an abstract or a theorem title clears subsumption.
- Helton–Klep–McCullough–Schweighofer, arXiv:1412.1481v4 (latest): actual Section11, pp57–61. Eq11.3 recalls the mean/mode interval; Corollary11.7 gives, for s>=t>=1 and s+t>=3, s/(s+t)<=m(s,t)<=s/(s+t)+(s-t)/(s+t)^2. By reflection, for b>=a>=1 this gives a/(a+b)-(b-a)/(a+b)^2<=m(a,b)<=a/(a+b). This does not give 4% near a=1,b large: its lower bound is only of order b^-2 when a=1. Thus it is not a complete bridge. The exact journal revision was not compared separately.
- Two Monotonicity Results for Beta Distribution Functions (Entropy26(2024)938) identified as relevant. Actual public publisher request returned403 and was stopped. Its theorem bodies remain an explicit access gap; not excluded as irrelevant from a search snippet.

No worldwide priority or complete novelty claim. No MathDB open label used.

## Route 1: scaled median, exact derivative, and the failed first shortcut

Assume 1<=a<=b. Let n=a+b-2/3 and Z_b=n X_b for X_b~Beta(a,b). The tempting plan is to prove that its median z(a,b)=n m(a,b) increases from z(a,a)=a-1/3 toward the Gamma(a,1) median M(a) as b tends to infinity. This would give

  a-1/3 <= z(a,b) <= M(a).

An additional uniform gamma estimate M(a)<(25/24)(a-1/3) would imply 24/25<Q/m<=1 on this half-domain. Reflection gives the full-domain absolute relative-error bound: when a>b, the absolute approximation error is unchanged and the true median is larger than its reflected counterpart. The gamma estimate is **not proved here**; familiar gamma-median results are dependencies requiring exact body checking, not a premise silently accepted. Most importantly, scaled-median monotonicity itself is unproved.

The density of Z_b on (0,n) is proportional to z^(a-1)(1-z/n)^(b-1)/n^a. For b2>b1, differentiation of its log-density ratio with respect to z gives

  (a+1/3-z) [1/(n2-z)-1/(n1-z)]

on the common support. It changes sign. Thus monotone likelihood ratio does not apply. Stochastic ordering of the entire scaled laws also fails: set a=b=1 and define H_b(C)=I_{C/(a+b-2/3)}(a,b). For u=C/(4/3), differentiation at b=1 gives exactly

  dH_b(C)/db = -(1-u) log(1-u) - 3u/4.

This is positive at u=1/100 and negative at u=1/2. The signs follow directly from the log series and log2<3/4; they are not merely numerical signs. Consequently there is no all-threshold stochastic-order shortcut. This is a **method obstruction, not a counterexample to Kerman**.

Going past that shortcut, let f=f_{a,b} be the normalized beta density, u=m(a,b), and L=psi(b)-psi(a+b). Differentiation under the beta integral is justified locally in a,b>0 by integrable logarithmic endpoint bounds. At fixed C=n u,

  dH_b(C)/db = integral_0^u f(x)[log(1-x)-L]dx - u f(u)/n.

The integral is also

  integral_0^u integral_u^1 f(x) f(y) log((1-x)/(1-y)) dy dx,

using normalization and F(u)=1/2 (indeed the covariance identity holds for any u). Implicit differentiation of H_b(z(a,b))=1/2 shows that z_b>=0 is equivalent to the first displayed derivative being <=0 **at the median**. Thus the precise outstanding inequality is

  integral_0^u integral_u^1 f(x)f(y)log((1-x)/(1-y))dy dx <= u f(u)/(a+b-2/3),
  for all 1<=a<=b and u=m(a,b).

The all-u version is false by the exact a=b=1 calculation. A bound using only positivity of the covariance has the wrong strength. Nine 40-digit derivative/independent finite-differentiation checks pass; they do not prove this median-restricted inequality.

## Route 2: nonroutine equal-deviance pairing for the sign subgoal

To attack the sign subgoal without generic ordering, set t=a+b-2/3, q=(a-1/3)/t, so a=tq+1/3, b=t(1-q)+1/3 and 0<q<1/2. Define

  V_q(x)=q log(q/x)+(1-q)log((1-q)/(1-x)).

For v>0 there are exactly two roots x_-(v)<q<x_+(v), since V'= (x-q)/[x(1-x)], V(q)=0 and V tends to infinity at each endpoint. The unnormalized beta density is a positive constant times

  exp(-t V_q(x)) [x(1-x)]^(-2/3).

Changing variables separately on each side of q yields the exact right-minus-left mass integral

  constant * integral_0^infinity exp(-t v) K_q(v) dv,

where

  K_q(v)=[x_+(1-x_+)]^(1/3)/(x_+-q)
         -[x_-(1-x_-)]^(1/3)/(q-x_-).

Each positive side integral is finite for the actual a,b>0; their difference and the change of variables are legitimate improper integrals. Proving K_q(v)>=0 uniformly would prove Q<=m on the selected half-domain, but would still leave the 4% magnitude. An exact equivalent kernel comparison is

  (x_+-q)^3/[x_+(1-x_+)] <= (q-x_-)^3/[x_-(1-x_-)]

for the equal-V pair. This is a specific one-variable analytic inequality, not an assumption that positive mixtures preserve log-concavity. Introducing signed z=(x-q)/[x(1-x)]^(1/3) reduces inversion to

  h^3+z^3 h^2-z^3(1-2q)h-z^3 q(1-q)=0, h=x-q.

The cubic alone does not compare V on its positive and negative inverse branches. No uniform branch comparison is proved here. Twelve 40-digit equal-level kernel probes are positive, with small level residuals, but are diagnostics only. In particular no claim is made for all v from a finite grid. This second reduction is preserved for possible genuinely new analytic work, not nominated as a helper discovery.

## Strongest objections / falsifiers

Mathematical: find any a>=1,b>=a whose scaled median decreases in b; this defeats Route1, even if the source 4% assertion remains true. A negative K_q(v) defeats the pointwise sufficient condition in Route2, though not necessarily its Laplace-integrated sign. Neither hypothetical event would by itself refute the literal source. Only an actual a,b>1 with |Q/m-1|>=1/25 would falsify the selected claim.

Eligibility: a public global beta-median bound in the inaccessible 2024 paper, Lyon's longer manuscript, or other unsearched specialist literature could subsume the target. This lane does not certify absence. The public 2026 ray theorems are already excluded, not rediscovered.

Conclusion: exact zero-credit gap consists of the median-specific covariance inequality (or an alternative full uniform bound), the magnitude estimate/bridge, and unresolved body/priority coverage. No partial result is offered for campaign credit.
