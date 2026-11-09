# W028: a rational circuit for the single-coefficient branch

Parent derivation, 2026-10-08 local, not independently reviewed. No numerical
run. Verified complete factoring improvement: **NONE**. This is a different
computation from the weighted-root product family.

## An exact finite approximation with no coefficient truncation gates

Let N be odd, A(t)=1-4t, and start P0=Q0=1. Use ordinary polynomial circuits

    P_(k+1)=P_k^2+A*Q_k^2,
    Q_(k+1)=2*P_k*Q_k.

Their shared straight-line description has O(k) arithmetic gates. Direct
substitution proves

    P_k^2-A*Q_k^2 = (4t)^(2^k),
    P_k(0)=Q_k(0)=2^(2^k-1).

Thus P_k has unit constant coefficient over Z/NZ. The formal rational series
Q_k/P_k has constant 1 and agrees with (1-4t)^(-1/2) through degree 2^k-1.
The proof uses the displayed residual and the unit constant coefficient 2 of
the sum of the two square-root branches. It works over an odd composite ring;
no factorial or unknown nonunit is inverted.

For m>=1 choose n=2^k>m. Then binom(2m,m) modulo N is exactly the coefficient
[t^m]Q_k/P_k. For k>=1 the degrees are n/2 and n/2-1. This improves the
degree growth of W023's untruncated inverse-square-root Newton polynomial
(whose degree is (3^k-1)/2), while keeping a short circuit and eliminating
explicit intermediate prefix truncation from its DESCRIPTION. It does not
make coefficient extraction a circuit gate or establish a runtime saving.

Expanded rational-series algorithms still pay for degree d=n/2=Theta(m).
For example the standard even/odd coefficient-halving method multiplies the
denominator by its value at -t and retains parity coefficients. It needs
access to those polynomial data; the short generating circuit alone does
not supply them at unit cost. Primary algorithm reference:
[Bostan--Mori, 2021](https://mathexp.eu/bostan/publications/BoMo21.pdf).
The parent retrieved the paper's statement and algorithm context, not a full
audit of all its algorithms over every coefficient ring. No new asymptotic
claim here depends on importing a field theorem without its hypotheses.

## A tempting trace shortcut reduces back to the same coefficient

The following characteristic-zero identity explains a concrete failed
consumer; after clearing powers of 2 it transfers to odd composite moduli.
Writing a^2=A and n=2^k gives

    P_k=((1+a)^n+(1-a)^n)/2,
    Q_k=((1+a)^n-(1-a)^n)/(2a).

Differentiation and (1+a)(1-a)=4t give

    Q_k/P_k = 1 - (2t/n)*P_k'/P_k.

If the reciprocal roots of P_k are lambda_i, its coefficient of degree m>=1
is therefore (2/n)*sum_i lambda_i^m. The root equation can be parametrized
by eta^n=-1; inverse pairs give the same reciprocal root

    lambda=eta+2+eta^(-1).

Consequently the power sum is half the trace over all n roots of z^n+1.
But for 0<m<n the Laurent expansion of (z+2+z^(-1))^m has exponents only
from -m to m. Root-of-unity summation kills all nonzero exponents in that
range, leaving exactly n*binom(2m,m). The proposed trace shortcut has merely
restated the requested central coefficient. The explicit quotient algebra
has dimension n, and its trace cannot be treated as a free operation.

This calculation distinguishes a smaller finite rational representation from
an actual coefficient consumer. W023's exact infinite-series section degree
does not by itself rule out exploiting this finite circuit. Conversely, this
short circuit does not defeat that theorem or yield a factoring algorithm.

The precise next constructive question is whether parity multiplication and
section extraction on this particular finite rational circuit have an
executable compressed recurrence with total cost below the dense degree.
The direct trace/roots-of-unity substitution above is already eliminated as
a shortcut. Any survivor must specify the resulting state, its acquisition,
its ring operations over unknown odd factors, and its growth at every step.
No additional root-chart review is needed to pursue that separate question.
