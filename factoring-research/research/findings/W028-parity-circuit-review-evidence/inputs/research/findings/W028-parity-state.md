# W028: exact parity state and a failed compression

Parent derivation, 2026-10-08 local. Not independently reviewed yet.
Verified complete factoring improvement: **NONE**. No numerical run.

Use W028-rational-newton-coefficient.md's notation n=2^k, d=n/2, and
R_k=Q_k/P_k. The Newton description is short, but its finite rational
coefficient extraction still needs an actual computation.

## 1. Parity extraction over the composite ring is legitimate

For any numerator A and denominator B with B(0) a unit, multiply both by
B(-t). Set U=A(t)B(-t), and write B(t)B(-t)=V(t^2). Retain the parity
of U matching the requested coefficient m, replace the denominator by V,
and replace m by floor(m/2). The denominator's constant is squared and
stays a unit. This is Bostan--Mori Algorithm1, whose proof and hypotheses
were read at PDF text lines454-548, including the effective-ring setup:
https://mathexp.eu/bostan/publications/BoMo21.pdf . It does not require
unknown field inverses. Expanded arrays of degree d remain paid.

## 2. Exact rational degree does not fall on these sections over Q

The d reciprocal poles of P_k are

    lambda_i = 2+eta_i+eta_i^(-1),   eta_i^n=-1,

with inverse pairs counted once. Over the complex numbers these lambda_i
are DISTINCT positive real numbers strictly between 0 and 4. The rational
Newton series has the exact partial-fraction representation

    R_k(t) = (2/n) * sum_(i=1)^d 1/(1-lambda_i*t).

This holds for the full rational function, not only its first n coefficients.
For a>=1 and 0<=c<a, its arithmetic section is therefore

    Section_(a,c)(R_k)(t)
      = (2/n)*sum_i lambda_i^c/(1-lambda_i^a*t).

The lambda_i^a remain distinct and every numerator weight is nonzero.
Each pole is genuine: at its pole all other summands are regular, so no
numerator cancellation removes it. The reduced rational denominator has
degree exactly d for EVERY section, including every binary digit path.
The denominator has rational coefficients by Galois invariance; the complex
pole count proves the same reduced degree over Q.

This is a statement about an exact rational representation. It is not a
lower bound on a short circuit, a truncated state, a modular algorithm, or
factoring. In finite characteristic powers can make poles coincide, so the
positive-real proof must NOT be exported to every odd prime. A later modular
collapse could be useful, but its acquisition and component dependence would
need a separate algorithm and proof.

## 3. A concrete short circuit survives ONE parity split

Write P_k(t)=E_k(z)+t*O_k(z) and Q_k(t)=G_k(z)+t*H_k(z), where z=t^2.
Direct expansion of the Newton update yields

    E_next=E^2+z*O^2+G^2+z*H^2-8*z*G*H,
    O_next=2*E*O+2*G*H-4*G^2-4*z*H^2,
    G_next=2*(E*G+z*O*H),
    H_next=2*(E*H+O*G).

Start E0=G0=1, O0=H0=0. This four-component recurrence computes the first
parity split with O(k) ordinary circuit gates. Its transformed denominator
is E_k(z)^2-z*O_k(z)^2. The even numerator is G_k*E_k-z*H_k*O_k;
the odd numerator is H_k*E_k-G_k*O_k. Thus the first split is executable
without a dense degree-d coefficient prefix.

Applying the same generic trick repeatedly is not yet a speedup. Computing
sections modulo t^a-z carries a components for a=2^j. Naive circuit pairing
can multiply the state size at each section, while explicit multiplication
of these components needs convolution. Keeping the remaining coefficient
precision m/a in every component stores on the order of m coefficients.
This describes two concrete implementations and their cost; it does not
prove that every representation has that size.

## 4. Chebyshev structure and the next computation

Let C_d(X) be the monic polynomial 2*T_d(X/2). The reciprocal-pole polynomial
is C_d(X-2), since eta^n=-1 and n=2d give T_d((eta+eta^(-1))/2)=0.
Its doubling rule C_(2d)(X)=C_d(X)^2-2 gives another logarithmic circuit.
After a section, the pole polynomial is the resultant of C_d(X-2) and
Y-X^a. Writing that resultant is not computing it.

The original Chebyshev symmetry is centered at 2: lambda pairs are
lambda and 4-lambda. Parity extraction instead squares lambda about 0.
These are different operations. Treating the transformed polynomial as the
same Chebyshev family with d halved would contradict the pole count above.
An actual compressed recurrence must account for the shifted center or use
a different coefficient functional. The first split's four-state circuit
is a concrete place to work on that issue; the trace shortcut in the prior
finding is already known to return the original binomial coefficient.

Independent audit should check the full rational identity, characteristic
scope, four-state recurrence, source hypotheses and actual generic state
cost. No toy timing can establish a fast coefficient algorithm here. The
main thread continues independent mechanisms instead of waiting on that audit.
