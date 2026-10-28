# Provisional complete ordinary route for Coiculescu's period conjecture

Credit 0. No Lean, independent review, manuscript or novelty clearance. This is
a research derivation to be independently checked, not an accepted discovery.

Source: Coiculescu, arXiv:2005.06430v2 (16 July 2021), Proposition 3.2 and
Conjecture 3.6; MathDB 346478. Actual latest PDF downloaded and text read.
The journal comparison remains open. Source integral, for alpha>0, 0<beta<1:

    P_alpha(beta)=2 integral_{t_-}^{t_+}
      [1-beta^2 V_alpha(t)]^(-1/2) dt,
    V_alpha(t)=(alpha exp(2t)+exp(-2alpha t))/(alpha+1).

The two endpoints solve V_alpha(t)=beta^(-2). The source geometrical family
uses 0<alpha<=1; the proposed integral argument applies to every alpha>0.
The entire family is ONE prospective outcome. The main cut-locus conjecture
does not follow from this derivative sign alone and is not claimed.

## Logarithmic energy and exact transform

Put h=-2 log beta>0, U=log V, and Q_alpha(h)=P_alpha(exp(-h/2)). Then

    Q(h)=2 integral_{U(t)<h} [1-exp(U(t)-h)]^(-1/2) dt.

U is strictly convex, has its unique minimum U(0)=0, tends to infinity at
both ends, and U''(0)=4alpha. Thus the ordinary turning-point substitution
u=sgn(t)sqrt(U(t)) removes the endpoint singularities and proves Q is
continuous for h>=0 and smooth for h>0, with

    Q(0)=C_alpha=pi sqrt(2/alpha).

For s>0 Tonelli and v=h-U(t) give

    LQ(s)=2 B(s,1/2) integral_R exp(-s U(t)) dt.

Write q=alpha/(alpha+1), r=1/(alpha+1), and
c=(alpha+1)/alpha^q. The substitution u=alpha exp(2(alpha+1)t) yields

    integral_R exp(-sU(t))dt=c^s B(qs,rs)/(2(alpha+1)),
    LQ(s)=sqrt(pi)/(alpha+1) c^s Gamma(qs)Gamma(rs)/Gamma(s+1/2).

These identities also prove finiteness of the transform for every s>0.
The Gamma duplication formula rewrites the second display as

    LQ(s)=2^(2s-1)/(alpha+1) c^s Gamma(qs)Gamma(rs)Gamma(s)/Gamma(2s).

## Positive inverse-transform representation

Use the exact Binet remainder formula, for z>0,

    log Gamma(z)=(z-1/2)log z-z+(1/2)log(2pi)+R(z),
    R(z)=integral_0^infinity exp(-zt) k(t) dt/t,
    k(t)=1/(exp(t)-1)-1/t+1/2.

Cancellation of all elementary Stirling terms (q+r=1 and c q^q r^r=1)
gives the EXACT identity, not an asymptotic approximation,

    s LQ(s)/C_alpha = exp(L nu_alpha(s)),
    nu_alpha(t)=[k(t/q)+k(t/r)+k(t)-k(t/2)]/t.

For t>0,

    k'(t)=1/t^2-exp(t)/(exp(t)-1)^2 > 0,

because 2sinh(t/2)>t. Also k(0+)=0, so k(t)>0. Consequently nu_alpha(t)>0.
At zero its removable limit is

    nu_alpha(0)=(1/q+1/r+1/2)/12 > 0.

It is continuous and bounded on the entire positive half-line (at infinity
nu(t)~1/t). Define convolution on [0,infinity), and

    H_alpha(t)=sum_{n>=1} nu_alpha^{*n}(t)/n!.

This series converges locally uniformly, since for a global bound M on nu,
nu^{*n}(t)<=M^n t^(n-1)/(n-1)!. It is continuous and strictly positive,
already because its n=1 term is nu. By nonnegative Tonelli and the convolution
transform identity,

    L H_alpha(s)=exp(L nu_alpha(s))-1,

for every s>0 (the right side is finite). Hence

    L [ C_alpha (1+integral_0^h H_alpha(t)dt) ](s)=LQ(s).

Uniqueness of the Laplace transform of continuous functions, with finite
Laplace integrals at every s>0, proves

    Q_alpha(h)=C_alpha (1+integral_0^h H_alpha(t)dt).

It follows that Q_alpha'(h)=C_alpha H_alpha(h)>0 for every h>0. The chain
rule then gives P_alpha'(beta)=-2 Q_alpha'(-2log beta)/beta<0, and continuity
at h=0 gives lim_{beta->1-}P_alpha(beta)=pi sqrt(2/alpha).

## Required scrutiny before promotion

Twelve independent real turning-point quadratures agree with numerical inverse
Laplace transforms to better than 1e-22, for alpha=.1,.37,1,2.5 and h=.3,1,3.
Twelve direct numerical Binet-kernel integrals agree with the logarithm of the
Gamma quotient, and 24 positive-kernel grid probes pass. These are diagnostics
only, not interval certificates or formal proofs; see check_route.py/checks.json.
Root visually read actual source PDF page15, including Proposition3.5 and the
literal Conjecture3.6. Latest arXiv remainsv2; journal body comparison is open.

The transform constants, Binet cancellation, uniqueness hypotheses, ordinary
turning-point regularity and convolution-series interchange all require an
independent review. No full Lean endpoint
exists. The exact general period statement was not found in an early bounded
registry/keyword screen, but that is not novelty clearance.

Closest prior-art warning: Rothe (1985) and Waldvogel (1986) prove monotonicity
for Lotka-Volterra periods using Gamma/Laplace methods. Their actual theorem
bodies and any time-preserving equivalence must be checked; the appearance of
Gamma functions alone neither proves nor disproves subsumption. General
logarithmically completely monotone Gamma-ratio theorems may render the new
argument a routine corollary. No claim is made until an explicit bridge is
adjudicated. Source alpha=1,1/2 known cases, Binet, Gamma identities, kernel
positivity and convolution tools are all classical and never separate credits.
