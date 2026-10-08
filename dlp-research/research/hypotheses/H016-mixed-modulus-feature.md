# H016 mixed-modulus feature: exploratory, no cost-qualified solver

2026-10-08. Native Astra /root/h007_additive_relations independent proposer;
root checked the algebra and requested explicit growing-order cost qualifications.
No test, training, hidden log advice or new Lean claim. Novelty unestablished.

For E:y^2=x^3+a*x+b over Fp with distinct prime subgroup order q, take centered
integer representatives X,Y,a,b and define

    kappa(P)=(Y^2-X^3-aX-b)/p,
    f_m(P)=chi_m(Y*kappa(P) modq), f_m(O)=0, chi_m(0)=0.

The quotient is an integer because P lies on E. It supplies no hidden carry
information: modulo q it equals p^(-1)*(Y^2-X^3-aX-b), so exact division can
be replaced by a paid precomputed inverse. This is an explicit scalar-field
polynomial in centered coordinate-field representatives. Under negation the
quotient is unchanged and Y changes sign, giving f_m(-P)=chi_m(-1)*f_m(P).
That avoids forced parity mismatch but proves no useful scalar correlation.

The motivation is arithmetic interaction between p and q using the curve
equation; the proposer candidly supplies no positive correlation mechanism.
The feature is executable for any certified m dividing q-1. Phase conversion
requires a paid order-m table or other explicit method, not free complex roots.

Conditional recovery uses the already-reviewed MCL identity, with calibrated
phase/error control and a fully paid coset-search backend. If rho_m is its
correlation magnitude, polylogarithmic paid feature evaluation would leave
principal terms roughly m^2/rho_m^2+sqrt(q/m), plus setup, tables, precision,
verification and failures. The prior beta<1/4 condition for rho=q^(-beta) and
m=q^delta is only a conditional balance. No growing-order divisor family,
correlation theorem, favorable full-work bound or practical speed is provided.

Proposed finite diagnostic only: earlier H002 fixture p127,a78,b87,q139,m6,
with full recertification, exact correlation/zero mass, planted control and
symmetry-preserving permutations, all globally charged. NOT implemented or run.
It would detect gross structure on one tiny frozen instance, not test every
asymptotic claim. Fixed m6 also retains H014's backend-cost limitation. Prior
labelled data may support a declared diagnostic but never become solver advice.

Disposition: retain as a concrete high-risk information probe, low priority;
no new feature sweep justified by the present weak mechanism. Reopen with an
analytic correlation reason or a more direct paid recovery advantage, rather
than arbitrary unbounded feature search. This does not reject other coordinate
information methods, nor require a complete proof before evaluating an idea.
