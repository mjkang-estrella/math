# W010 — a quantitative envelope from the acquired norm law

2026-10-08. Parent derivation, PROVISIONAL pending independent review.
No candidate experiment, Lean change or complete factoring improvement.
The positive-drift theorem is accepted separately. The question here is
whether its rate is large enough to help a short sequential circuit.

## Smooth leading form and the actual norm distribution

Fix any current monic odd P in F_p[X], of formal degree D=3^j, p>3.
Its coefficients may have been chosen adaptively; freeze the whole map
before taking fresh uniform X,Y. Define

    eta(b)=Pr[Q(P(X),P(Y))=b],   Q(z,u)=z^2+zu+u^2.

This includes all pairs, not only the legal ones defining K. Thus
K(b)<=eta(b) pointwise. Their total masses differ: sum eta=1,
sum K=ell. Let psi be a nontrivial additive character and t!=0.
The top degree form of t Q(P(X),P(Y)) is

    t (X^(2D)+X^D Y^D+Y^(2D)).

It is squarefree over the algebraic closure: in the ratio X/Y its roots
are the D-th roots of the two distinct roots of Z^2+Z+1; they are nonzero
and simple because p does not divide 3D. The point at infinity is not a
root. It therefore defines a smooth zero-dimensional hypersurface in P^1.
Also p does not divide 2D. These facts hold for every lower coefficient
of P, not just random coefficients.

Deligne, La conjecture de Weil I, Theorem 8.4, printed pp.302–303, gives
for an n-variable polynomial with smooth top projective hypersurface and
degree d prime to p, the bound (d-1)^n p^(n/2) for its complete additive
sum. The parent read the original theorem at
https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf . This application,
normalizations and scope still need independent audit.
For n=2, d=2D it proposes

    |eta_hat(t)| = |E psi(t Q(P(X),P(Y)))| <= (2D-1)^2/p.

Parseval therefore gives

    sum_b (eta(b)-1/p)^2 <= (2D-1)^4/p^2,
    sum_b K(b)^2 <= sum_b eta(b)^2
                  <= 1/p+(2D-1)^4/p^2.                         (1)

The omitted factor (p-1)/p only weakens the bound. We use formal degree;
no replacement modulo X^p-X is made. A theorem with a large right-hand
side is valid but uninformative. This does not bound all later depths.

## Statewise drift and root supply

The accepted exact laws are D_v=sum K^2-sum K A and D_m=sum K B.
Here sum B=s and sum B^2=2v, using the odd symmetry. Nonnegativity of B
and K<=eta, followed by Cauchy–Schwarz, gives

    0<=D_v<=1/p+(2D-1)^4/p^2,
    0<=D_m<=s/p + (2D-1)^2 sqrt(2v)/p.                         (2)

The lower bound for D_v is the separately proved orbit/graph result.
The root bound uses the actual beta distribution; it does not assume
uniform beta or take square roots of beta as computational inputs.
An auxiliary three-variable character sum is unnecessary.

Use the original W010 raw-attempt protocol modulo distinct p,q>3:
update only on the joint clean chart, paid no-op otherwise; record a
proper factor and freeze the map afterwards. At a fixed active state,
local raw drifts are multiplied by the other component's ell<=1.
Since D_v,D_m>=0, (2) bounds the stopped-and-frozen increments too.
After t raw attempts, the number of accepted updates is at most t and
D<=3^t. Fresh input means remain those of a fixed polynomial at that
realized state. No independence between survived prime histories is used.

Starting with v_0=(p-1)/p^2<=1/p, write

    V_t=(t+1)/p + (81^t-1)/(5p^2).

The inequality (2*3^j-1)^4<=16*81^j and a geometric sum propose

    E[v_t]<=V_t,                                               (3)
    E[m_k]<=(k+1)/p + (4/p) sum_(j=0)^(k-1) 9^j sqrt(2 V_j).    (4)

Equation (4) uses Jensen on sqrt(v_j), not survival-conditioned means.
The inactive contribution is zero. The expectation is over the entire
protocol, including failures and early factors, with their states frozen.
For k>=1 and 81^k<=p these imply the convenient bounds

    E[v_k]<=(k+6/5)/p,
    E[m_k]<=(k+1+0.5 sqrt(2k+2/5))/p.                          (5)

Indeed V_j<=(j+6/5)/p, and sum_(j<k)9^j=(9^k-1)/8<=sqrt(p)/8.
At k=0 use the original masses; no empty-sum ambiguity is needed.
These are O(k/p) bounds through D<=p^(1/4). Formal degree 3^k has not
produced exponential mean concentration in this regime.

## How this relates to success, and what it does not prove

At a fixed active state, a proper factor in the four anchor gcds requires
one of z,u,z-u,z+u to vanish at at least one component. A union bound at
p is at most

    2m + 2(m^2+v) <= 4m+2v,

and analogously at q. Sum these statewise probabilities over the actual
raw-attempt schedule, applying (3)-(4) to its stopped states. This gives
an O(k^2*(1/p+1/q)) training-success upper bound under 81^k<=min(p,q).
This is an upper bound with all full gcds included in the union; it is
not an exact success law. Earlier full-gcd stopping can only reduce the
set of tested events, provided the same update/no-op protocol is used.

A subsequent fresh sampled pin a=P(r), with proper gcd(a,N) recorded,
and one absorption update P(P-a), has local mean endpoint root mass
m+v when a is unrestricted. If the pin is clean-conditioned, do not use
this equality without its rejection factors. One can instead upper-bound
the unconditioned event for the attempted pin and its T fresh probes;
mark rejected/terminated paths inactive. The proposal is an
O((k^2+(T+1)(k+1))*(1/p+1/q)) full success bound for this SPECIFIED
training/one-pin/probe protocol in the same degree range. Its constants
and precise pin chart must be audited before acceptance.

This is a raw-budget envelope, not an expected-actual-work lower bound.
Training can stop early; k accepted layers can require more than k raw
attempts; an algorithm could try greater degrees or different probes.
Even acceptance of (1)-(5) would leave deeper cubic circuits open.
No application to the Jacobi-filtered training rule is assumed: it uses
a different beta distribution and can lose the sign of the drift.

## Constructive response

The smooth leading form is the exact obstruction being tested: it keeps
the sampled norm parameter almost flat at low degree, despite favorable
sampling bias. A possible escape must either enter greater circuit depth
with paid acquisition, change the leading form to acquire persistent
correlations, or lower detection work through a batch primitive. Existing
reciprocal and group-coherent maps have their own scoped failures and
cannot simply be relabeled as such an escape. The parent is developing
batch extraction alongside this calculation, without assuming a positive
review or an unexplained energy oracle.
