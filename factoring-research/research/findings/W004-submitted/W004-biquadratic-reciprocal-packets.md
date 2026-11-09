# W004 supporting derivation — reciprocal packets

2026-10-08. **UNACCEPTED pending a new independent review.**
This is the separately retained reciprocal-packet deduction from the constructive
work, complementary to the accepted W003 companion packet used in the main
[report](W004-biquadratic-construction.md). All notation and field hypotheses
are those independently checked there: t=2R, f_i=T^2-s_i*T+t^2,
Delta_i=s_i^2-4t^2, d_i^+/-=s_i+/-2t, with alpha_i nonsquare in K_i.
No numerical execution or point search was performed.

For rational c, c is square in K_i iff c or c/Delta_i is a rational square;
c*alpha_i is square iff c/d_i^+ or c/d_i^- is a rational square. These follow
from expanding a square in 1,sqrt(Delta_i) and (alpha_i+/-t)^2=d_i^+/-*alpha_i.

Use the reciprocal quartic to pair two rows. For coprime positive
integers p,q define the common integer pairs (p,q) and (tq,p), and

    Q_{p,q}(T)=(p^2-q^2 T)(t^2 q^2-p^2 T),
    Lambda_i=s_i p^2 q^2-p^4-t^2 q^4.

The constant term cancels on using alpha_i^2=s_i alpha_i-t^2:

    Q_{p,q}(alpha_i)=alpha_i Lambda_i,                 (1)
    Norm(Q_{p,q}(alpha_i))=t^2 Lambda_i^2,
    Lambda_1-Lambda_2=(s_1-s_2)p^2q^2=0 mod N.       (2)

Thus the absolute-norm requirement is solved identically in both fields.
This is a nonempty two-row construction, not a subset-kernel search.
Neither Lambda_i vanishes over Q: otherwise (p/q)^2 would be a rational
root of f_i. Its sign need not be positive. Clearing the reciprocal pair
to these integer rows is essential: no inverse of p or q modulo N is needed.

## Exact target criterion and explicit, valid extraction

For the orientation Q(alpha_1)=alpha_1 z_1^2, Q(alpha_2)=z_2^2,
(1) meets the target **if and only if** some rational h,k satisfy

    Lambda_1=epsilon_1 h^2, epsilon_1 in {1,Delta_1},
    Lambda_2=epsilon_2 k^2, epsilon_2 in {d_2^+,d_2^-}.               (3)

The equivalence follows from the rational-class tests above. In particular
h,k are nonzero. The actual roots are explicit:

    z_1=h                    if epsilon_1=1,
    z_1=h(2alpha_1-s_1)       if epsilon_1=Delta_1;
    z_2=k(alpha_2+t)          if epsilon_2=d_2^+,
    z_2=k(alpha_2-t)          if epsilon_2=d_2^-.

Use the same conditions with 1 and 2 interchanged for the opposite orientation.
No factorization of Lambda_i, discriminant, field order or norm is needed.
An exact rational square test reduces a fraction and tests its numerator and
positive denominator by integer square roots, rejecting a negative numerator.

All four epsilon choices are units modulo N. If h=A/B in lowest terms and
epsilon h^2 is an integer, then B^2 divides epsilon. Therefore the rational
denominators of h,k are units; this conclusion does not require p,q to be
units. The displayed z_i belong to explicitly allowed localizations.
Set c_1=1 or -3R according to epsilon_1, and c_2=3R or -R according to
epsilon_2. If the common packet image is a unit, (1) implies Lambda_i is
a unit, and hence h c_1 and k c_2 are units as well. Return

    y=(k c_2)/(h c_1) mod N;                 y^2=R mod N.           (4)

This proves recoverability for the witnesses in (3), as well as abstract
target membership. Verify (3), the field equalities and (4) before returning.

For each constituent row (a,b), first compute g=gcd(a^2-b^2R,N).
A proper g returns a factor; g=1 allows continuation; g=N requires checking
gcd(b,N). A unit b returns a/b as a verified root, a proper gcd returns a
factor, and otherwise this candidate fails. For these coprime reciprocal
packets the last case cannot occur: no prime of N divides both coordinates.
Process both rows in order, so a nonunit packet is never silently inverted.
Apply the same row rule to the four original rows (u_j,1),(v_j,1).

## The specific missing primitive

For each of the four choices in (3), put a=p/q, H=h/q^2, J=k/q^2.
The required witnesses lie on the explicit simultaneous quartics

    epsilon_1 H^2=-a^4+s_1 a^2-t^2,
    epsilon_2 J^2=-a^4+s_2 a^2-t^2.                              (5)

The other orientation gives four further curves. Each quartic has four simple
roots because t!=0 and Delta_i!=0. The two root sets are disjoint: subtraction
forces a=0, which is not a root. Over an algebraic closure their fiber product
is a degree-four cover of the a-line with eight branch points, each contributing
two to ramification. Riemann–Hurwitz gives 2g-2=-8+16, hence g=5.
This statement concerns the smooth projective model, not an arbitrary singular
projective closure of the displayed affine equations.

The involution a->-a has the genus-one quotient, in P^3 with coordinates
(X:H:J:Z),

    X^2-s_1 XZ+t^2 Z^2+epsilon_1 H^2=0,
    X^2-s_2 XZ+t^2 Z^2+epsilon_2 J^2=0.                          (6)

Indeed its degree-four cover of the X/Z-line has four distinct branch points
(the roots of f_1 and f_2); the same count gives genus one. A rational point
on (6) is not enough: it must have Z!=0 and X/Z a nonzero rational square
to lift to (5). A useful lift must also make the packet image a unit modulo N.
No rational point on (6), positive rank, generators, finite-rank certificate,
uniform group distribution or height bound has been supplied by the field law.
The Norm2 point is on a different modular conic and provides none of these.

There is an earlier arithmetic warning than general point-search complexity.
Writing d=s_1-s_2, subtraction of (3) gives the ternary conic

    epsilon_1 h^2-epsilon_2 k^2=d l^2,           l=pq.             (7)

Because N divides d, a rational solution of even this weaker equation with
valid unit reductions of h,k already gives (4): epsilon_1=c_1^2 and
epsilon_2=c_2^2/R modulo N. This conic becomes singular modulo every prime
of N; its reduction does not retain the l coordinate. The trivial solution
of the resulting homogeneous congruence supplies no unit slope. Granting a
cheap solver for *these prescribed unit witnesses* would already grant the
desired modular root, even without completing the reciprocal packet.
This explains precisely why a generic modular norm representation cannot be
substituted at this step. It is not a proof that such witnesses never exist.

A finite bounded attempt enumerates coprime 1<=p,q<=M, tests both orientations
and all four choices in (3), and uses the displayed row gcd and root checks.
All integers and rational coordinates have O(n+log M) bits; the scan costs
M^2 poly(n+log M) bit steps and poly(n+log M) working bits after field setup.
No positive packet-success mass is established. This supporting derivation
does not propose that one-field attainment is missing: W003's accepted
companion packet already supplies it. It instead isolates a different common
row family that forces both absolute norms to be squares from the start.
