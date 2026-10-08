# H015 Grok compositions: preflight, not accepted algorithms

2026-10-08. Raw substantive Grok4.7 output retained in H015-hybrid-grok-raw.md.
Root identified concrete algebraic/specification defects and requested independent
native reviews before any proposed computation. No new numerical run, installed
solver or Lean theorem. Verified improvement remains NONE.

## Exact signed-slope bit identity: hand counterexample

Card3 freezes beta_i=floor(2*rep_p(lambda_i)/p),
lambda_i=(y(T)-y(D_i))/(x(T)-x(D_i)), D_i=[2^i]G, claiming bit_i(k) for T=[k]G.
Using y distinguishes negation but does not establish the proposed scalar-bit
identity. Root found the following counterexample; native Sol independently
verified the arithmetic and read the existing H014 metadata.

Use E:y^2=x^3+x+13 over F59, G=(1,29), q67. The prime-order admission and full
curve count are existing recorded H014 evidence, not a new enumeration or a
new Lean proof. This meets the raw ordinary/prime/q!=p/aut±1 setting; gcd(67,58)=1.
The finite record is research/experiments/H014/initial_results.json, first curve.

By the ordinary affine formulas, computed by hand:

    lambda_G=(3+1)/(2*29)=4/58=-4 mod59,
    2G=(16-2, (-4)*(1-14)-29)=(14,23).
    lambda_(2G)=(3*14^2+1)/(2*23)=589/46=50=-9 mod59,
    4G=(81-28, (-9)*(14-53)-23)=(53,33).

Take k4,T=4G and i0,D0=G. Then lambda0=(33-29)/(53-1)=4/52=50 mod59,
so beta0=floor(100/59)=1, while bit0(4)=0. The denominator52 is nonzero and
D0!=+/-T. Although T=D2, that makes a DIFFERENT index exceptional and cannot
repair the claimed nonexceptional i0 identity. No unspecified exception handler
or complete new solver was executed. One ordinary finite counterexample suffices
to refute this universal exact map, not other functions or biased signed-slope
information. No proposed2^12-scale diagnostic is needed for this claim.

The raw rho0.886*sqrt(q) figure is an idealized addition-count reference. It is
not calibrated complete solver work and does not pay every implementation cost.

## S3 lattice: missing columns and invalid vanishing certificate

Native Astra independently inspected the raw module and confirmed root's
coefficient/column objections. For fixed r and E:y^2=x^3+A*x+C,

    S3(X,Y,r)=(X-Y)^2*r^2
      -2*((X+Y)*(X*Y+A)+2C)*r+(X*Y-A)^2-4C*(X+Y).

Its X^2 coefficient is (Y-r)^2, not a field constant. Scalar normalization
cannot make it monic in X; division by that coefficient enters rational functions
and requires handling Y=r. The X^2*Y^2 coefficient is1, total degree4, absent
from the proposed ten columns of total degree<=3. No nonnegative monomial
multiple of full S3 fits. Dropping the missing term changes the polynomial.

The reviewer found an independent certificate counterexample: proposed row
g=p*X^3 has stated scaled norm p because that column's B^(3-i-j) weight is1.
It passes p*B^(3/2) for B>1, yet g(x,y) is not zero over the integers for x!=0.
Root makes this concrete using the SAME recorded F59 curve above: B=floor(59^(1/3))=3,
r=x(-2G)=14, (X,Y)=(1,1) lies in the box, and
S3(1,1,14)=-944=-16*59. Thus this is an actual modular box root, while
g(1,1)=59!=0. No LLL run or point enumeration occurred. Even a survivor does
not certify an integer common zero. Moreover original f only vanishes modulo p;
an ordinary integer resultant with f requires an additional valid recovery
argument, not merely treating f as integer-zero at the hidden box root.

The relation-count model is also mismatched: two base points plus FIXED R is
a pair decomposition, not three independently chosen base points. For a signed
base of size N=O(B), uniform R has expected unordered pair count at most
N*(N+1)/(2q)=O(B^2/q). A fixed-jump walk does not prove conditional uniformity.
Both signs of one base point have dependent logs; k adds an unknown. The phrase
"B independent rows" supplies no rank/projection proof recovering k. The sign
of R must be normalized or retained in its equation. Changing B does not fix
these definition, yield and recovery defects. No proposed planted2^24 trial.
This rejects the frozen module/certificate, not corrected bivariate lattices.

## Miller progression: impossible divisor and invalid membership operation

For the intended support and sole pole O, the degree-zero divisor is

    D_B=sum(j=0..B-1) ([j]G)-B(O).

Its elliptic group sum is [B*(B-1)/2]G, nonzero for1<B<q with odd prime q.
The Abel-Jacobi isomorphism implies that this divisor cannot be principal,
even over the algebraic closure. Thus no stated rational function has that
divisor. This application uses
[Sutherland, Theorem23.17, pp.7–8](https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/94cf817bccece2b52ba143a8164a3a7c_MIT18_783S21_notes23.pdf),
read independently by root after the reviewer supplied it. The theorem identifies
degree-zero divisor classes with elliptic group sums. Our arithmetic application
concerns this exact support, not every compensated progression divisor.

Other independent problems with the supplied recurrence/query:

- Its initial vertical line has divisor (G)+(-G)-2(O), not the required AP.
  x([0]G)=x(O) is undefined; ordinary baby tables handle O separately.
- With tau_Q(P)=P-Q, g_m composed with tau_(-mD) shifts zeros by -mD,
  not the +mG required to concatenate the stated progression.
- A translated order-d pole moves away from O. Unless existing zeros cancel
  it, correction needs a zero of order d; degree<=4 cannot cancel unbounded d.
  This is a divisor restriction, not an inference that high degree forbids
  compact evaluation circuits.
- Polynomial reduction modulo Pi preserves values at Pi's roots, not at arbitrary
  giant abscissae. Taking g=Pi gives remainder0 and falsely labels every giant a
  hit. General Fp(E) functions additionally require handling y and denominators.
- E(Fp) of odd prime order q has no nonidentity point with order dividing the
  proposed power-of-two B<q. Extension-field torsion would need a different
  explicit operation and recovery argument.

The ordinary Miller repeated-point divisor acknowledged in the proposal is
valid; it does not supply the claimed AP function. Reject these exact modules
before anyB8 expansion or walk. A repaired compensated divisor, lattice or query
must be specified and costed separately; this is no general impossibility claim.
