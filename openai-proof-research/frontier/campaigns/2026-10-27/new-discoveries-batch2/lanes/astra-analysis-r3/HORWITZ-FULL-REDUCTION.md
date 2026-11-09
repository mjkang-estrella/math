# Full two-parameter reduction, NOT a solution

Target: Horwitz math/0007095v1 Section 4 Conjecture 16. Source pp12–13 read as text and visually. For positive a,b,c, T(a,b,c) is the triple of pairwise logarithmic means. We seek U0(Tv)>=U0(v), U1(Tv)<=U1(v). Neither assertion is proved in this lane.

For distinct ordered positive a<b<c, define

    D0(a,b,c) = -[a,b,c]log,
    D1(a,b,c) = [a,b,c](u log u).

The source formulas are exactly U0=(2D0)^(-1/2), U1=(2D1)^(-1). Both D's are positive: the second-derivative divided-difference integral has positive integrand, since -log has second derivative 1/u² and u log u has second derivative 1/u. Their simplex representations also supply the continuous extension to repeated inputs. Thus the desired signs are D0(v)-D0(Tv)>=0 and D1(Tv)-D1(v)>=0.

By symmetry/homogeneity, every distinct triple is represented by

    (a,b,c)=(exp(-p),1,exp(q)), p,q>0.
    s=p+q, x=(1-exp(-p))/p, z=(exp(q)-1)/q,
    y=(px+qz)/s, d=z-x>0.

Then T(v), in increasing order, is (x,y,z), and

    y-x=q d/s, z-y=p d/s, c-a=s y.

The elementary divided-difference identity gives

    D0(v)=d/(x z s y), D1(v)=1/y-D0(v).

For example D0(v)=[p/(1-a)-q/(c-1)]/(c-a); substituting 1-a=px and c-1=qz proves the first formula. For the second, the successive secant slopes of u log u differ by s+1/z-1/x, and division by c-a gives the formula above. In particular D1>0 is not an extra hypothesis.

Set

    J0=s log y-p log x-q log z,
    J1=p x log x+q z log z-s y log y.

Then

    D0(Tv)=s J0/(p q d²), D1(Tv)=s J1/(p q d²).

Both J0 and J1 are positive by strict concavity of log / strict convexity of u log u and y=(px+qz)/s. However this alone does NOT compare with D0(v),D1(v).

The exact remaining assertions, for all p,q>0, are

    p q d³ - x z s² y J0 >= 0,                    (H0)
    x z s² y J1 - p q d²(x z s-d) >= 0.           (H1)

All factors multiplied away are positive. Accordingly a proof of H0/H1 for the entire quadrant would prove the inequalities for distinct triples. Continuity then gives weak inequalities for repeated triples. Strict equality conditions for Conjecture 15 would still need attention. A single strict negative certified residual would refute Conjecture 16; no such residual was found.

## A possible alternate endpoint

The source gives G(v)<=L3(v)<=P_(1/3)(v), and L3(Tv)=L3(v). Therefore either of the following GLOBAL pairs of inequalities would suffice for the weak part of Conjecture 15:

    U0(v)<=G(T²v),  P_(1/3)(Tv)<=U1(v),

or replace the upper bound with A(T²v)<=U1(v). These are only proposed sufficient inequalities, not theorems. The stronger one-step substitutes U0<=G(Tv) and A(Tv)<=U1 are FALSE; the deterministic checker finds violations even close to the diagonal. No general argument may rely on them.

## Numerical checks, expressly not proofs

`checks/horwitz_full.py` compares the gap formulas to an independently coded barycentric divided-difference formula at 110 decimal digits. On the 256-point grid p,q in {10^k:-8<=k<=3} union {2,3,30,300}, relative formula disagreement was <2e-96; no negative target residual found.

`checks/iterate_envelopes.py` tests 196 p,q pairs across 10^-6 to 10^3. It finds 80 failures of the G(T) lower shortcut and 94 failures of the A(T) upper shortcut. No failure of the three proposed sufficient bounds above was found. Finite floating-point observations neither establish their signs elsewhere nor give interval certificates.

## Exact independent interval checks

`checks/rational_intervals.py` implements interval arithmetic over `fractions.Fraction`, with outward rounding to 10^-80 after each operation. Logarithms use a 100-term atanh series after power-of-two reduction. The explicit geometric tail bound is proved in the script header and valid because the reduced argument has atanh parameter in [0,1/3]. No binary floating point is used in its certification path.

It proves strictly positive D0(v)-D0(Tv) and D1(Tv)-D1(v) at each of

    (1,2,3), (1,10,11), (10,11,100), (1,2,100),
    (1,99,100), (1,10^6,10^12), (1000,1001,1002).

The full rational enclosures are in `checks/rational_intervals.json`. These are SEVEN FINITE CHECKS, not a proof of either source conjecture. They provide independent exact checks of the floating-point implementation and the signs at sample inputs.

The same arithmetic strictly certifies the failed shortcuts without extracting roots: U0(v)>G(Tv) is equivalent to

    1-(2D0(v))^3 (xyz)^2 > 0,

and A(Tv)>U1(v) is equivalent to

    2D1(v)(x+y+z)-3 > 0.

For example the first is certified at (1,2,3), the second at (1,2,100). These only refute proposed helper inequalities; they do not refute Horwitz's conjectures or earn credit.

## Additional symmetric form, not a sign proof

With h(t)=log(sinh(t/2)/(t/2)), direct substitution gives

    J0=(p+q)h(p+q)-p h(p)-q h(q).

Indeed x=exp(-p/2)sinh(p/2)/(p/2), z=exp(q/2)sinh(q/2)/(q/2), and y=exp((q-p)/2)sinh((p+q)/2)/((p+q)/2); their linear exponential terms cancel in J0. This symmetrizes the logarithmic numerator but does not symmetrize the full H0 residual. No unjustified reduction to p=q or to repeated inputs is made.
