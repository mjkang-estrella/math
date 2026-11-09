# W032: high input lifts control the output digit affinely

Parent derivation, 2026-10-08. **Accepted with the subsequent qualification below.**
Verified complete factoring improvement: **NONE**. No numerical run.

The scalar construction has used canonical 0<=a<N. A materially different
proposal is to choose higher N-adic digits of a so as to bias the output
digit. This note derives the actual response instead of treating that
choice as a free selector.

Let R>=2 and assume 2R+1<leastprime(N), N odd. Fix a unit a0 modulo N;
one may take its representative 1<=a0<N. For any t in [0,N), use

    a_t = a0 + N^(2R-2)*t.

The scalar pair-power construction still works for this larger a: its
identity, exact N^2 division, and unit normalization did not require a<N.
Reduce z=N*a modulo the working modulus before powering. These inputs
have O(R log N) bits, fitting the existing precision scale. The first-two-
digit formulas specific to canonical a are NOT silently extended to a_t.

Write V(a)=sum_(k=0..R) N^(2k)G_k(a^2) modulo N^(2R+1).
All denominators are units. Since G_1(a^2)=a^2/24,

    N^2*(G_1(a_t^2)-G_1(a0^2))
      = N^(2R)*(a0/12)*t + N^(4R-2)*t^2/24.

The quadratic term vanishes modulo N^(2R+1), because 4R-2>=2R+1
for R>=2. Each term k>=2 has a difference divisible by
N^(2k+2R-2), hence also vanishes at that precision. Therefore

    V(a_t)-V(a0) = N^(2R)*(a0/12)*t mod N^(2R+1),
    d_R(a_t) = d_R(a0)+(a0/12)*t mod N.                 (3)

The digit identity follows even for canonical V representatives: adding
a multiple of N^(2R) preserves every lower digit, and changing the lift
by N^(2R+1) changes the quotient by a multiple of N. The coefficient
a0/12 is a checked unit.

## What this computation would save, and why it does not amplify yield

After one scalar evaluation at a0, equation (3) computes the entire
N-element lifted family by cheap affine arithmetic. It genuinely shares
the expensive powering. But it also identifies every tested residue
explicitly; no factor-dependent structure remains in this family.

Uniform t modulo N makes d_R exactly uniform modulo N. For distinct
primes N=pq, the proper-gcd probability is exactly

    (p+q-2)/(pq),

because there are q-1 nonzero multiples of p and p-1 nonzero multiples
of q. This is the ordinary random-integer gcd probability, not an
independence heuristic. It is unrelated to the unknown law for canonical
inputs 0<=a<N in the frozen assay.

More strongly, any prescribed c modulo N is reached by the public choice

    t = (c-d_R(a0))*12*a0^(-1) mod N.

Choosing c=0 forces gcd N, not a split. Choosing a c that already has a
proper gcd merely transports that known residue through the scalar
construction. Thus this precise lift-control family is equivalent to
choosing public gcd arguments; it does not supply a new separating oracle.
This is a reduction for this family only, not a lower bound on arbitrary
canonical-input selection or on factoring.

For prime powers or general odd composites the uniform-residue statement
still holds. The displayed probability formula is specifically squarefree
semiprime; do not extend it unchanged to those other inputs.

The constructive question now becomes sharper: can the restricted,
canonical a interval yield correlations that this free affine lift loses?
The floor representation in W032-canonical-floor-structure.md describes
that remaining computation. Blind high-lift randomization or algebraic
forcing of the highest digit is not a route around the yield obligation.
## Subsequent acceptance qualification

The original affine theorem is now accepted in
`W032-symbolic-parent-disposition.md`. Interpret the phrase "no
factor-dependent structure remains" below as no ADDITIONAL response beyond
the acquired base and explicit affine map. The base's information and cost,
adaptive selection and batch consumption remain present in the simulation.
No lower bound on those computations or on factoring is asserted.
