# I332 parent endpoint reduction — uniformly biased entropy production

2026-10-13. Conditional reduction and research hypothesis, not a proved production bound or accepted finding. The full S313 target remains open.

Use psi and I from S313, F(psi(a))=a atanh(a), and T_(exp(-t)) for the cube noise semigroup. For interior-valued u define

    D(u)=(1/4) sum_i E[(u-u^(i))(atanh(u)-atanh(u^(i)))].

Finite-sum differentiation gives d/dt I(T_(exp(-t))u)=-D(T_(exp(-t))u). Endpoint values are handled after positive time and then by continuity. The mean is unchanged. Sharp contraction from the stipulated source implies D(u)>=F(I(u)) by differentiating at t=0, but does not itself supply the strict quantitative term below.

## The unpaid hypothesis

It would suffice to prove constants c>0,I0>0, independent of dimension, such that

    D(u)-F(I(u)) >= c I(u)^2

whenever 0<I(u)<=I0 and |Eu|>=1/2. More generally any fixed positive bias threshold would suffice. The assertion is NOT justified by N131, which only covers a genuine one-coordinate kernel. The older source max-profile estimate cannot be substituted for this strict term.

A stronger possible hypothesis is D(u)-F(I(u)) >= c (Eu)^2 I(u)^2 uniformly at small I. It is compatible with the fixed-mean optimized quartic examples, but no global proof is supplied. Rare posteriors with relative fluctuations of order one must be included.

## Exact implication for the missing S313 regime

Fix 0<r0<=r1<1 and choose a_*<1 with psi(a_*)<=I0. Let I(u)=psi(a), a<=a_*, and m=Eu with |m|>=1/2. Set t=-log r, y(s)=I(T_(exp(-s))u) and w(s)=psi(a exp(-s)). Then w'=-F(w), while y'=-F(y)-R(s) with R=D-F(y). Hence

    Delta=w(t)-y(t)=integral_0^t exp(-integral_s^t A(v)dv) R(s) ds,

where A is the secant slope of F between y and w, with continuous extension at equality. On [0,psi(a_*)], 2<=A<=K for a finite K. This identity uses the sharp contraction y<=w and ordinary scalar variation of constants.

If Delta>=w(t)/2, then Delta>=r0² a²/4 >=r0² a4/4. Otherwise monotonicity gives y(s)>=y(t)>w(t)/2>=r0²a²/4, for 0<=s<=t. The mean is still m, and y(s)<=I0, so the unpaid production hypothesis would give

    Delta >= c r0^4 a4 (1-r1^K)/(16K).

The distance d_a(u)=E u²+a²-2a max_i |uhat(i)| is at most 2. Consequently this would prove d_a<=C a^(-4)Delta throughout the uniformly biased small-information regime. Together with a fully proved fixed-interior-mean version (e.g. |m|<=3/4) and R020 on amplitudes bounded away from zero, it would establish full S313. No conclusion is taken until the production bound and the fixed-mean theorem have each passed their required validation.

## Why relative fluctuation arguments are insufficient

Writing epsilon=(1-m)/2 and f=(1-u)/(2epsilon), one has Ef=1, 0<=f<=1/epsilon. The complementary density is (1-epsilon f)/(1-epsilon). Thus

    I(u)=epsilon Ent(f)+(1-epsilon) Ent((1-epsilon f)/(1-epsilon)).

As epsilon tends to zero, small I does not force f close to one in any strong norm. An argument based only on absolute oscillation of u, or on Taylor expansion with a fixed lower bound for 1-m², misses this regime. Any proposed uniform production proof must respect both conditional densities and their exact positivity constraint.
