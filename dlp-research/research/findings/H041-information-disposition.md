# H041 autocorrelation and signed recovery: scoped results

2026-10-09 UTC / 2026-10-08 local. Raw Factory Fable5.1 report is retained in
H041-information-fable-raw.md. Native Astra independently reviewed the algebra
and character hypotheses; native Sol independently reviewed recovery and cost.
Root checked the formulas and reopened [Kohel–Shparlinski, section3](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf).
Its subgroup character-sum bound is used only after checking nondegeneracy.
No new executable run, experiment, Lean claim or H034 cap reset.

## Changed query, incomplete peak decoder

For F(n)=f([n]G), the proposed paired public evaluations have expectation

    E_d f(Q+[d]G) conjugate(f([c]Q+[d]G)) = R_F((c-1)k),
    R_F(t)=q^(-1) sum_n F(n) conjugate(F(n+t)).

Here d is uniform modulo the odd prime subgroup order q. Computing [c]Q,
both sample points, features and any dependent sampling schedule is paid.
Dispatch k=0 by Q=O; c=1 gives the known zero lag and is not a recovery query.
A large uncentered mean can generate peaks at every lag without information.

The proposed decoder samples c to hit a public list T of t peak lags, then
tries k=tau/(c-1) for members tau of T and verifies them. Its displayed
q/(t epsilon^2) only prices a modeled peak-search stage. It omits constructing
and storing T, identifying the correct lag within T, all false-positive and
confidence costs, and up to t scalar verifications under its own enumeration
rule. A structured lag-recovery algorithm could change that invoice, but none
was supplied. A non-phase statistic still needs calibrated error control.
For fixed k!=0 and independent uniform c in F_q minus {0,1}, the lag is uniform
on F_q minus {0,-k}. Thus the usable peak count is t_k=t-1[-k in T]; the ideal
first-hit mean is (q-2)/t_k, and t_k=0 is a failure case. Peak height alone is
not a statistical separation gap. With a specified gap Delta, M comparisons
and total error budget delta, independent bounded samples give a sufficient
per-comparison estimate cost O(Delta^(-2) log(M/delta)), plus centering,
calibration and numerical error control. This is not a universal lower bound.

## Narrow additive-coordinate bound

Let f(P)=phi(x(P)), with |f|<=1 and explicit bounded conventions at infinity.
Write phi(z)=sum_u c_u psi(uz), and L1=sum_u |c_u|. The correct expansion for
T=[tau]G is

    R_F(tau)=sum_(u,v) c_u conjugate(c_v)
       * q^(-1) sum_P psi(u x(P)-v x(P+T)),

with the at-most-two exceptional points handled separately. For tau!=0 and
(u,v)!=(0,0), the rational function has distinct poles at O and -T, of order
two where present. In characteristic p>2 these orders also exclude an
Artin–Schreier form h^p-h+constant. The cited bound therefore yields

    R_F(tau)=|c_0|^2+O(L1^2 sqrt(p)/q + 1/q).

The group mean mu=q^(-1)sum_n F(n), rather than c_0 alone, is the appropriate
centering. Its corresponding one-point bound gives, conservatively,

    |R_F(tau)-|mu|^2|=O((L1+1)^2 sqrt(p)/q + 1/q).

Thus no centered peak exceeds this bound; this does NOT say there are no
peaks at smaller thresholds. For q comparable to p and L1 polylogarithmic,
if epsilon is a possible centered peak height, t<=q implies
t epsilon^2 is at most polylogarithmic. It cannot meet the raw decoder's
idealized improvement criterion t epsilon^2>sqrt(q). This excludes that
declared inverse-square sample-cost model on this feature class, even before
its missing recovery costs. It is not a sample-complexity lower bound on every
estimator, a bound on arbitrary nonlinear features, or a general adaptive-query
impossibility result. The Fourier norm must be justified for each feature;
Legendre-type features do not automatically have small Fourier L1.

## Quadratic characters: corrected nondegeneracy lemma

Let g be an F_p-rational function of degree d, and let Dodd be the geometric
support of its odd valuations. If g(P)g(P+T) is geometrically square, Dodd is
invariant under translation by T. This is about valuation parity, not the full
zero/pole set. The raw implication T in E[d] is not established.

For T of odd prime order q, every translation orbit has q elements. The number
of points in Dodd is even, because the principal divisor has degree zero.
Consequently, if invariant and nonempty it has at least2q elements. But
|Dodd|<=2d, so d<q forces Dodd empty in this degeneracy case.

Under the additional assumption that the FULL rational group E(F_p) has odd
order q, an F_p-rational even principal divisor is twice a rational principal
divisor: its half-divisor class would otherwise be rational two-torsion in
Pic^0(E), which is absent. Hence g=c h^2 and its quadratic feature is constant
away from zeros/poles. This supplies a narrow nondegeneracy test for nonconstant
features away from zeros/poles under that full-group hypothesis. A zero-extended
feature can still differ at exceptional points, whose corrections remain paid.
For a subgroup inside an ambient
group with rational two-torsion, unramified quadratic classes require separate
analysis. No numerical Kummer bound is asserted here without its character,
conductor, summation domain and exceptional-point conditions.

Higher moments are not closed by this two-translate argument: several parity
divisors can cancel without invariance under a single translation. The raw
learned-window, smoothness and general representation-method exclusions are
likewise not established. No universal negative result is accepted.

## Constructive signed-membership repair

The root proposed and Sol checked a simple complete invariant avoiding the
raw report's unspecified first orientation step. After Q=O is dispatched,
recover the least absolute residue

    r=min(k,q-k) in {1,...,(q-1)/2}.

For j in this positive half-range, x(Q)=x([j]G) holds exactly when j=r.
Binary search r using the product over j in the tested contiguous half of the
current integer interval. Retain inclusive endpoints. A zero product chooses
that half; otherwise choose its complement. At the final singleton verify
[r]G=Q or [-r]G=Q. This restores a valid recovery invariant; it does not assume
the unknown secret lies in a smaller range. Both signs are covered.

This assumes a correct evaluator for an arbitrary contiguous block, with its
whole construction and query cost charged afresh unless reuse is justified.
If its bound is uniformly C sqrt(length), first tested lengths are about
q/4,q/8,... and their square roots sum to at most
(1+1/sqrt(2))sqrt(q)+O(log q). Constants, ceilings, logarithmic factors,
representation, memory and final verification remain paid. This conditional
upper bound proves neither a gain nor inferiority to matched BSGS/rho. No
implementation or new evaluation primitive was supplied.

## Disposition

Retain the changed autocorrelation query, narrow feature-class screen and
constructive sign-aware recovery as paper findings. There is no demonstrated
complete-work survivor, and no experiment is admitted. Best supported exponent
remains1/2; verified improvement NONE. Next conclusion-changing evidence would
be a feature outside the scoped bound with paid peak construction and recovery,
or a genuinely cheaper complete interval-product evaluator. General proof
infrastructure is not the next step.
