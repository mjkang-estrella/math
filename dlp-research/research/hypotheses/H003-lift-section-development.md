# H003 explicit first-order sections: proposed formulas and concentration test

Native Sol `/root/h003_lift_sections` read-only development. Root transcription
of its derivation, candidate families and full-cost hypothesis. No experiment,
implementation, edits by proposer, children, Lean theorem or verified ECDLP gain.
Independent review is required before adopting the formulas or funding a test.

## Pointwise formula, including corrected normalization

Let p>=5, E:y²=x³+Ax+B smooth, and G=<P> have odd prime order q!=p. Use canonical
integer representatives A0,B0,r,v for A,B,x(R),y(R). Every nonzero R in G has
2y!=0. Lift coefficients to A0+p*a,B0+p*b modulo p². A section with x-coordinate
r+p*phi(R) has y-coordinate
`v+p*(e(R)+a*x+b+(3x²+A)*phi(R))/(2y)`, where
`e=(r³+A0*r+B0−v²)/p modp`. Set s(O)=O.

For odd division polynomial Psi=psi_q, define raw carry
`D=psi_q(r;A0,B0)/p modp`, and derivatives J=Psi_x,U=Psi_A,V=Psi_B at R modp.
Simple odd torsion x-roots give J!=0. The claimed torsion-section coordinate is
`x_tau=r−p*(D+aU+bV)/J`, and displacement under invariant differential dx/(2y)
gives the kernel coordinate
`g_(a,b,phi)(R)=((D+aU+bV)/J+phi(R))/(2y)`.
The proposer's first progress message omitted J on D; THIS corrected formula
divides the entire numerator by J. Preserve that correction explicitly.

Proposed evaluation: a constant-size division-polynomial recurrence window along
halved indices modp², with three derivatives modp, O(log q) modular operations.
Only division by unit2y is needed in the recurrences; no point-difference
denominators, generic ring group-law library, or degree-q² expanded polynomial.
This cost/correctness claim needs code-independent review before implementation.
Background sources supplied by proposer: [Silverman III.3.7, IV](https://www.math.ens.psl.eu/~benoist/refs/Silverman.pdf)
and [Magma division polynomials](https://docs.magma-maths.org/ArithmeticGeometry/EllipticCurves/function_field.html).
The particular formulas are the proposer's derivation, not quoted theorems.

## Three concrete families and an exact representation caveat

1. Coefficient tuning and quadratic correction:
   `(a,b,u0,u1,u2) in {-1,0,1}^5`, phi=u0+u1*x+u2*x²:243 fixed sections.
   Shared features d0=D/(2yJ), hA=U/(2yJ), hB=V/(2yJ), Fi=x^i/(2y).
   Then g=d0+a*hA+b*hB+sum ui*Fi. Weighted homogeneity gives
   `2xJ+4AU+6BV=0`, hence `4A*hA+6B*hB=−2F1`. Infinitesimal scaling
   `(a,b,phi)=(4Aw,6Bw,2wx)` changes no g, so do not count it as a signal.
   This leaves a genuine deformation direction even at j=0 or1728; no claim
   that all such lifts are isomorphic. No reason for concentrated corrections
   has yet been supplied by this finite cancellation family.
2. Teichmueller carry: a=b=0, Fp(x)=(r^p−r)/p modp, with Fp(0)=0;
   phi=c*Fp(x)+d*x*Fp(x), (c,d) in {-1,0,1}²:9 sections. (1,0) lifts x to r^p.
   Carry evaluation O(log p), total pointwise O(log p+log q). Coordinate
   multiplicative symmetry is not elliptic-addition concentration. Automorphism
   support arguments need actual overlap/fiber bounds, not just determinants.
   Both families are negation-equivariant: g(−R)=−g(R). For corrections
   Ck=k*g(P)−g(kP), C_(q−k)=q*g(P)−Ck for nonzero canonical k.
3. Bounded offsets: hB(R)=1+(r modB) for R!=O, hB(O)=0, 1<=B<p.
   Section tau(R)+K(p*hB(R)) has exactly g=hB, with g(P)!=0. If a correction
   dictionary covers beta*(q−1) nonzero scalars, then with L=ceil(q/p),
   `|C|>=beta*(q−1)/(B*L)`: each correction permits at most B residues of k
   modulo p, with at most L canonical lifts. For q~p, B=q^gamma,gamma<1/2,
   this excludes dictionary exponent alpha<1/2 at constant beta. This is scoped
   to small-image g, not every section. Homomorphic g=0 removes all scalar signal.

Choosing `phi=−(D+aU+bV)/J+2y*f(R)` realizes ANY cheap f as g=f. Therefore an
unrestricted section can simply re-express a coordinate predictor; evaluating f
directly avoids section construction. This exact representation claim is not an
impossibility argument against a particular useful predictor.

## Conditional full solver, not an established concentration phenomenon

Fix M=ceil(q^(1/3)),beta=1/4. Hypothesize one of the finitely specified sections
with lambda=g(P)!=0 has at least beta of canonical scalars' corrections in one
unknown cyclic Fp interval of length M. A trial chooses an eligible section,
eight independent known uniform scalars and their corrections. The union of
intervals [Cki−M,Cki+M] contains the hidden interval if any training sample hits
it (probability >=eta=1−(1−beta)^8). Independently shift target Q'=Q+tP with
known uniform t. For every dictionary c, compute r=(g(Q')+c)/lambda modp,
enumerate ALL canonical k' in[0,q) congruent to r modp and verify k'P=Q'.
Return k'−t modq only on verified success. Refresh training/section/shift after
failure. With T candidate sections, success per trial >=eta*beta/T under the
hypothesis. Charge noneligible section detection/selection, setup and failures.

Direct work is O(T/(eta*beta)*(log q+log p+M*L*log q)). Streaming consecutive
residue candidates with precomputed lambda^-1*P and p*P may reduce verification
to O(M*L+log q) group additions, but modulo-p wraps and canonical lift changes
must be explicitly handled. Streaming interval descriptors use polylog storage;
materializing the dictionary uses O(M). A bounded fallback to baseline is possible.
No hidden target scalar, restricted challenge domain, or inverse table is allowed.

## Root decision and proposed cheapest falsifier

The proposer suggests two increasing small ordinary curves with q<=61 and two
fresh generators each, complete Ck histograms for all252 sections, and maximum
cyclic interval mass compared with beta*q. Shared feature costs, all combinations,
histograms/sorting and point generation count toward60seconds/1M primitive events.
That would refute only the specified instance-level concentration claim, not
all sections or large-instance behavior. It has NOT been authorized or run.
There is currently no mechanism establishing why these carries should concentrate;
root requests independent symbolic and cost review first. No generic ring/Lean
infrastructure is justified by the existence of a conditional solver alone.
