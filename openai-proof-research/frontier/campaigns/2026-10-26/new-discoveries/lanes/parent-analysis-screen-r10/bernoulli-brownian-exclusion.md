# MathDB332241: a direct Brownian-exit corollary, not discovery credit

The actual Chen–Paris1601.02192 source defines both remainders in Conjecture1.1.
The nu half is already proved in that same source (Remark2.4, via Theorem2.2).
The remaining mu half is a direct Taylor-remainder corollary of the classical
Brownian interval-exit Laplace transform. Thus no new-outcome credit is proposed.

## Exact reduction

For standard Brownian motion started at alpha in(0,1), let H be its first exit
time from(0,1), conditioned on exiting at1. The classical transform is

    E_alpha[exp(-s*H) | exit at1]
       =sinh(alpha*sqrt(2*s))/(alpha*sinh(sqrt(2*s))), s>=0.     (1)

An actual primary body recording the drifted version for every real drift is
Cérou–Guyader–Lelièvre–Malrieu, *On the length of one-dimensional reactive paths*,
ALEA10(1)(2013)359–389, Proposition5.1, p381. Setting drift0 in its continuous
limiting expression yields(1). The same result follows directly from the
boundary-value calculation in that paper Section2.1, solving u''/2=s*u with
u(0)=0,u(1)=1 and dividing by the exit probability alpha.

At alpha=1/3, put s=t^2/8. Elementary hyperbolic algebra gives the exact source
function

    (exp(t/3)-exp(2*t/3))/(exp(t)-1)
      =-sinh(t/6)/sinh(t/2)
      =-(1/3)*E[exp(-t^2*H/8) | exit at1].                   (2)

For every u>0 and m>=0, the ordinary integral Taylor remainder gives

    (-1)^(m+1)*(exp(-u)-sum_(j=0..m)(-u)^j/j!)>0.           (3)

All conditional moments of H are finite. One elementary justification: a
Brownian increment of at least1 over the next unit interval forces exit from
(0,1), regardless of the current position. The Markov property therefore bounds
P(H>k) geometrically; conditioning multiplies the bound by1/alpha. This also
gives a small exponential moment and justifies identification of Taylor
coefficients in(2).

The Bernoulli generating function in Chen–Paris identifies those coefficients
as 2*B_(2j+1)(1/3)/(2j+1)!. Substitute u=t^2*H/8 into(3), take the conditional
expectation, and multiply by-1/3. This proves (-1)^m*mu_m(t)>0 for ALL m>=0,
t>0, exactly the remaining source assertion. Strictness follows from H>0 almost
surely. The nu assertion follows similarly with alpha=1/2, but is already
explicitly proved by Chen–Paris and is uncredited in either reading.

## Scope and classification

This records a specific application of an older stronger transform, not an
older paper explicitly announcing a solution to Chen's conjecture. The only
additional reasoning is the standard exponential Taylor remainder and matching
the displayed generating function. Under the user's exclusion of immediate
known-result corollaries, do not count or invest in a discovery packet. No
novel Brownian transform, stochastic theorem, coefficient formula or CM theorem
is asserted. No worldwide-priority claim.

Primary actual raw body: https://alea.math.cnrs.fr/articles/v10/10-15.pdf ,
p381 and Section2.1; also arXiv1206.0949. Both raw PDFs were successfully
retrieved and extracted after the ordinary impa-host download failed. The
cnrs copy's p381 was rendered and personally inspected. The failed host
response was never used as a PDF. No HTML response is treated as a PDF.
