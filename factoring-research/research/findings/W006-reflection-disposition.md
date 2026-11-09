# W006 reflection disposition

2026-10-08. Accepted with the exact chart distinctions in the
[independent report](W006-reflection-validation.md). The supplied generic
construction is closed as a factoring speedup. Verified improvement: **NONE**.
No experiment or shared-code/Lean edit was needed.

Let A be primitive of odd norm N, B0=iA, with the parent's dot-product scalars,
tau=bf-ae, H=aE-fC, T=Norm(H), J=bE-eC, L=Norm(J). The exact identities are

    Norm(D)=c*T*L,
    B2=B0+(2*tau/T)*H=-A*bar(H)*i*H/T.

Thus the parameterized two-reflection output is R_H(B0), with H perpendicular
to A. On gcd(T,N)=1, bar(A)*(T*B2)=-N*bar(H)*i*H and the right-gcd norm is
gcd(N,tau). Integral outputs on this chart are among +/-Ai,+/-Aj,+/-Ak.
Such exceptions may still split N, but their factor is already the scalar gcd.
One can therefore skip the reflections and compute gcd(<bA-aB0,E>,N).
If that linear functional is primitive modulo N, unrestricted uniform E gives
a uniform scalar, with balanced-semiprime factor probability Theta(N^(-1/2)).
Conditioning on integrality or the chart may change that law.

The raw chart c*Norm(D) unit implies T unit; merely having a,b,c,Norm(E) unit
does not. Dividing a nonunit scalar out of D can produce normalized unit
directions with useful mixed components. The report gives explicit symbolic
counterexamples. No assertion about all rational rotations is accepted.
For a word of A-perpendicular unit-norm reflections, however, the one-sided
multipliers alternate and integral endpoints are signed-axis associates.

The full raw gcd N is not a factor. The reduced multiplier denominator
delta=T/gcd(T,coefficients(-bar(H)*i*H)) is a concrete cancellation test.
For an integral nonexceptional twin it is a proper divisor of N. Before
integrality is established, only a witnessed proper gcd(delta,N) is a factor.

After primitive normalization H0, final integrality is equivalent to
Norm(H0)|2*tau0. In the full-gcd branch Norm(H0) divisible by N, a nonexceptional
output forces Norm(H0)=2N and B2 perpendicular to both A and iA.
Write A=z+w*j over Z[i]; eta=gcd(z,w) has Norm(eta)|N. A proper such norm
immediately splits N. Norm(eta)=1 leaves only signed-axis solutions to that
simultaneous-orthogonality shell. Norm(eta)=N leaves an alternative two-squares
representation of N to acquire; no cheap acquisition algorithm is supplied.
These conclusions follow from the explicitly parameterized Gaussian solutions
in section 8. They do not import a representation oracle.

The short-reflection bound c<8 for p<q<2p remains valid for proper scalar-gcd
successes with integer reflection coefficient and unit c. Nonexceptional
integral outputs on that unit chart are already excluded by the stronger
multiplier argument. Primitivity of the direction matters if inferring the
coefficient's integrality from the endpoint.

All these tests cost polynomial bit work per given parameter tuple. Generating
useful off-chart tuples is not paid. Larger coordinate boxes or further
A-fixing reflections cannot overturn the regular-chart identity. The
constructive replacement is to investigate different acquisition operations,
including modular group samples and batched collisions, rather than treat
rational parametrization itself as useful integral-point generation.

