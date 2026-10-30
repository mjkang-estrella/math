# Full ordinary counterexample to the MMPP stochastic-order conjecture

Candidate only: no independent eligibility review, formal certificate, acceptance,
or priority clearance. This is an ordinary finite-dimensional analytic proof,
including exact rational arithmetic and a uniform analytic remainder bound.

## Exact claim and witness

Asanjarani–Nazarathy, ANZIAM J.64 (2022), 54–68,
DOI 10.1017/S1446181122000013, Conjecture3.9, asserts that every irreducible
MMPP satisfies T1^pi >=st T1^alpha. The identical preprint target is
arXiv:1905.01736v1 Conjecture4.2. Here pi is the stationary row law of the
background generator Q; D is the diagonal matrix of arrival intensities;
C=Q-D; lambda*=pi D1; alpha=pi D/lambda*. Proposition2.2 identifies the
survivals as eta exp(tC)1. These definitions are literal, not alternative
notions of event or time stationarity.

Use states i=0,...,11, with subscripts modulo12. Set Q_(i,i)=-1,
Q_(i,i+1)=1, all other entries0, and D=diag(a_i/60), where

    a=(9,8,7,6,5,4,3,4,5,6,7,8).

This finite directed-cycle generator is irreducible: a path of successive
positive-rate jumps connects every ordered pair. Its stationary law is
pi_i=1/12 because every column sum is0. All arrival intensities are strictly
positive; their mean is lambda*=1/10, so alpha_i=a_i/72 and
w_i=pi_i-alpha_i=(6-a_i)/72. In particular alpha is positive with total1.
The embedded arrival chain has matrix (-C)^(-1)D, and
alpha(-C)^(-1)D=pi D/ lambda*=alpha, since pi(-C)=pi D.
Thus these are exactly the source stationary laws.

At t=48/5 we prove

    w exp(tC)1 < -1/25000 < 0.

The time-stationary survival is therefore strictly SMALLER at this threshold,
refuting the asserted universal stochastic order. No minimal order is asserted.

## Analytic estimate and reproducible finite certificate

Let r=23/20, P=I+C/r, s=rt=276/25. The only nonzero entries of P are
P_(i,i+1)=60/69 and P_(i,i)=(9-a_i)/69. Hence P is nonnegative and
P1<=1. Inductively 0<=P^k1<=1 for every k>=0. The matrix exponential power
series is absolutely convergent and C=r(P-I), giving

    exp(tC)=exp(-s) sum_(k>=0) s^k P^k/k!.

Put L=sum_i |w_i|, and S80=sum_(k=0)^80 (s^k/k!) wP^k1. Absolute values,
0<=P^k1<=1, and the geometric ratio bound for the scalar tail give

    |sum_(k>=81) (s^k/k!) wP^k1|
      <= L s^81/81! / (1-s/82) =: B80.

The denominator is positive. Exact rational arithmetic gives S80<-2 and
B80<1/100. It follows that the entire infinite series is negative. Multiplying
by exp(-s)>0 preserves its sign. This already proves the counterexample.

Here is a finite INTEGER specification of the nontrivial arithmetic inequality,
so no floating-point exponential or special-function evaluation enters the proof.
Let x0=(1,...,1), x_(k+1,i)=60 x_(k,i+1)+(9-a_i)x_(k,i), and

    D80=72*25^80*80!,
    N80=sum_(k=0)^80 4^k 25^(80-k) (80!/k!) sum_i (6-a_i)x_(k,i).

Then S80=N80/D80 exactly, by induction and s/69=4/25. The integers
N80,D80,N80+2D80 are saved in certificate.json. certificate.py computes them
using only integer addition, multiplication, powers and exact factorial quotients,
and verifies N80+2D80<0. check.py independently reconstructs S80 with Fraction
matrix-vector recurrence and verifies the tail bound above. These finite
arithmetic statements, together with the displayed analytic bound, are an ordinary
proof certificate; neither script is asserted to be a Lean/kernel certificate.

For a second independent arithmetic formulation within this SAME solo lane,
expand exp(tC) directly to order160. Let U160 be the resulting signed sum.
Since ||C||_infinity=max_i(2+a_i/60)=43/20, z=t||C||=516/25,

    |w exp(tC)1-U160| <= L z^161/161! /(1-z/162)=:E160.

check.py verifies U160+E160<-1/25000 by exact rational arithmetic. This proves
the quantitative bound stated above. The two evaluations use different matrices
and tail envelopes, but are not an independent reviewer.

## Scope and remaining gates

Nothing about variance, all time thresholds, all cycle sizes, reversibility,
minimal state dimension, or a universal family classification is needed.
The source's existing four-state nonmonotone EVENT-hazard example is a different
property and does not supply this survival crossing. Our witness is nonreversible
and therefore outside its two-state/symmetric-C positive results.

The remaining gaps are external to this ordinary argument: independent adversarial
source/math/substantive review; bounded-priority coverage beyond the inspected
sources and dated registry evidence; and, only if eligibility is approved, full
formalization. Any sign error in either exact certificate, stationary-law mismatch,
or hidden source restriction would defeat this nomination. No count is changed.
