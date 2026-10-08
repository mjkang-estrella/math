# H030 odd-selector extension to order-six automorphisms

2026-10-08. Root derivation independently checked by native Astra. Paper proof
using accepted H027 normalization; no Lean theorem, experiment or solver gain.
This is an applicability lemma for C1/C2, not an extra automorphism speedup.
The comparator already receives the known order-six quotient where applicable.

Let E:y²=x³+b over Fp, p>3, with primitive cube root beta in Fp, full prime
group order q>3, q!=p, and phi(x,y)=(beta*x,y). Put z=-x/y, so z o phi=beta*z.
For nonidentity P, normalize the accepted torsion Miller function by

    div(f_P)=q[P]-q[O],  f_P=z^-q*(1+a_P*z+O(z²)).

The pullback f_(phi P) o phi has the same divisor as f_P and leading coefficient
beta^-q. Two functions with the same divisor differ by a constant, hence

    f_(phi P) o phi=beta^-q*f_P.

Comparing the next coefficients gives beta*a_(phi P)=a_P, therefore

    h(phi P)=beta^-1*h(P),  h(P)=a_P/q.

q is invertible in Fp. For O use its separately defined h(O)=0, not the
nonidentity Laurent expansion. Oddness supplies the other three unit actions.
For h!=0 the six values{+/-h,+/-beta*h,+/-beta²*h} are distinct, so minimizing
their integer representatives selects one point from the order-six orbit.
h=0 requires paid x/y canonicalization. No frequency assumption is supplied.

Field beta is NOT a scalar modulo q. If phi acts on the q-subgroup by eigenvalue
lambda, the point action epsilon*phi^i uses scalar epsilon*lambda^i in labels,
while h scales by epsilon*beta^-i. Track the chosen action explicitly.

For cumulative tag tracing the invariant generalizes to S=U(P0+K), with U a
unit action. The correct update is K'=K+U^-1 J, NOT K+U J in general. Then
S+J=U(P0+K'), so full-unit canonicalization of P0+K' gives the same logical
successor. Sign-only tracing hid this distinction because epsilon^-1=epsilon.

## Table and cost scope

Each jump coefficient now lives in the Eisenstein lattice with six unit steps.
Its sphere at positive distance n contains6n formal vectors, giving

    g(z)=1+6z/(1-z)^2,
    N(r,tau)=sum_(n=0)^tau [z^n]g(z)^r.

For one jump N(1,tau)=1+3tau(tau+1). These are formal vectors, before any paid
identification of equal subgroup points. The larger table, scalar unit actions,
field beta multiplication, canonical comparisons and exact reported orbit keys
all cost work. Neither h-values nor orbit size are free collision keys.
This extends applicability to rational order-six families; it does not establish
useful-collision behavior, complete cost advantage or a new exponent.
