# W006 — independent reflection and component validation

Date: 2026-10-08. **Disposition: revise, with the generic obstruction proved
at its precise chart. Verified new end-to-end factoring improvement: NONE.**

This is a new symbolic review. No numerical mathematical execution, screen,
sampler, package installation, solver/Lean change, recursive delegation,
publication, or commit was performed. Only this owned report was written.
The coefficient portion of the supplied wave is checked in section 10;
the principal result concerns the actual supplied reflection parameterization.
All additional deductions below are submitted for parent disposition, not
silently promoted to an accepted or formally verified theorem.

The decisive identity is the following. Keep the parent's meanings of
`a,b,c,d,e,f,h,S`, put `tau=bf-ae`, and define

    H = a E - f C,       T = Norm(H),
    J = b E - e C,       L = Norm(J).

For the **raw polynomial** direction `D=S C+c tau E`, one has exactly

    Norm(D) = c T L,
    R_D R_C(B0) = B0 + (2 tau/T) H
                = -A bar(H) i H/T.                    (V1)

Thus the polynomial construction is another representation of a single
reflection in an A-perpendicular direction. If `gcd(T,N)=1`, it has
the same image as A at every prime power dividing N; its right-gcd norm
is exactly `gcd(N,tau)`. If its output has integer coordinates, it is one
of the six right signed-axis associates of A. These statements do not
require a or b to be units. In particular they hold on the chart where
both **raw** reflection norms `c` and `Norm(D)` are units modulo N.

This is not a theorem about two arbitrary reflections with unit norms.
Even within the supplied formula, cancelling a common scalar from D can
leave two unit-norm directions and a nonexceptional output. Section 6
gives an explicit symbolic family: a, b, c, and Norm(E) are units, the
normalized directions are 1 and j, and the raw scalar already supplies
a proper factor. Section 7 gives a different family where all the listed
raw scalar gcds are 1 or N: exact cancellation/content extraction is then
necessary. A full gcd N must not be described as an already-found factor.

## 1. Conventions and exact unit hypotheses

Use Hamilton multiplication, `ij=k`, conjugation `bar`, and the usual
integer Cartesian coordinates. N is positive and odd; factoring concerns
N>1. A is primitive with Norm(A)=N, and `B0=i A`. Primitivity here means
gcd of A's four integer coordinates is 1. At odd primes this agrees with
the Hurwitz-order primitivity used in the accepted report. A nontrivial
coordinate content of A already divides N properly, because its square
divides N.

Write `R_N={u/v in Q: gcd(v,N)=1}`. This specifies the localization even
when N is composite. A unit scalar in this report is a unit at every
prime dividing N, not merely a nonzero rational number. Content gcds
of an `R_N`-quaternion are computed after clearing a denominator coprime
to N. At odd primes, integer, doubled Cartesian, and integral Hurwitz
basis contents give the same capped valuations.

There are several distinct domains, which must not be conflated:

* Over Q, (V1) needs only `C != 0` and the **raw** `D != 0`. They imply
  `c,T,L>0`. No nonzero or unit assumption on a, b, tau, S, or d is needed.
* Direct modular evaluation of the original two-reflection expression
  needs `gcd(c Norm(D),N)=1`. By the norm identity this implies that
  c, T, and L are units. Norm(E)=d is not a denominator of this formula.
* After the proved rational cancellation, the larger sufficient chart
  is simply `gcd(T,N)=1`. Neither a, b, c, d, L, nor tau has to be a
  unit for that statement, provided the original rational output exists.
* If D or H is first divided by its integer coordinate content, its
  norm can become a unit although its original norm was not. This is
  an off-chart cancellation case, not evidence against (V1).
* A proof using `z=-2ab/c` as an invertible coefficient must additionally
  assume a and b are units. The proof here never divides by a or b;
  imposing those assumptions would unnecessarily discard valid inputs.

In particular, units a, b, c, and d alone do **not** define a safe chart.
The counterexample in section 6 has all four and still escapes after
cancelling the nonunit scale of D. No assumption about squarefreeness
is hidden in any of these distinctions.

## 2. B1, B2, the polar form, and the polynomial identity

Temporarily let D be any nonzero direction and write `delta=Norm(D)`,
`e_D=<B0,D>`, `f_D=<A,D>`, and `h_D=<C,D>`. Direct substitution gives

    B1 = B0 - 2b C/c,
    B2 = B0 + [-2b delta C + (4b h_D-2c e_D)D]/(c delta),
    <A,B2> = -2[ab delta+c e_D f_D-2b h_D f_D]/(c delta).

Thus both signs, the coefficient 4, and the orthogonality equation in
the original brief are correct. Norm preservation is exact over Q.
Coordinate divisibility by `c delta` is a sufficient and necessary
integrality test when applied to that displayed numerator, though exact
cancellation can make it needlessly large.

Return to the parameter vector E and the parent's `d=Norm(E)`. For
`z=<A,B1>=-2ab/c`, set

    Q(V)=z Norm(V)-2<A,V><B1,V>.

Use the polar convention
`B_Q(X,Y)=(Q(X+Y)-Q(X)-Q(Y))/2`. Since `<B1,C>=-b`, direct calculation
gives

    Q(C)=0,
    B_Q(C,E)=z h-a(e-2bh/c)+bf=bf-ae=tau,
    Q(E)=-2[ab d+c e f-2b f h]/c=-2S/c.

The second-intersection vector `Q(E)C-2 B_Q(C,E)E` is isotropic for Q.
Multiplication by `-c/2` gives the parent's P1 exactly. If it is zero,
there is no resulting reflection; rejecting it is necessary. Tangency
and degeneracy are not a free second point.

For a fully explicit audit of the cancellation, put `k=ce-2bh`. Then

    S=ab d+f k,
    T=a^2 d+c f^2-2afh,
    L=b^2 d+c e^2-2beh,
    S^2+2S tau h+c tau^2 d = T L,                      (V2)
    eS+b tau d=f L,
    bS-tau k=a L.

All three are polynomial identities obtained by expanding the displayed
scalars. In particular

    Norm(D)=c(S^2+2S tau h+c tau^2 d)=c T L,
    <B1,D>=-bS+tau k=-a L.

Substitute these into the second reflection. Its C coefficient reduces
to `-2f tau/T`, and its E coefficient to `2a tau/T`. This proves
`B2=B0+2tau H/T`. Also `<A,H>=0` and `<B0,H>=-tau`, proving both its
orthogonality and its interpretation as `R_H(B0)` without a geometric
component heuristic.

The quaternion Householder formula is

    R_H(V)=-H bar(V) H/T.

Using `bar(iA)=-bar(A)i` and `H bar(A)=-A bar(H)` gives the last equality
in (V1), including its minus sign. Set

    U=-bar(H)iH/T;       Norm(U)=1,       Re(U)=0.

The output is exactly `A U`. This is a statement about this output on
this input; it does not identify the entire four-dimensional operator
`R_D R_C` with a one-sided multiplication or with a single reflection.

If tau=0 and D is nonzero, the construction simply returns B0.
The identity `Norm(D)=cTL` proves that D is zero exactly when H or J is
zero, since the norms here are positive definite over Q. These cases
must be rejected before cancelling T or L.

## 3. Local components, repeated powers, and exceptional outputs

Assume `gcd(T,N)=1`. Then U and its inverse belong to the quaternion
order over R_N. For each `p^r || N`, multiplication on the right by U
preserves A's column lattice over Z_p, hence its image modulo every
`p^s`, `1<=s<=r`. A primitive A has local Smith form `diag(1,p^r)`,
up to units. Thus the output has a primitive rank-one reduction and the
same image line as A throughout those quotients.

There is also a denominator-cleared component identity, stronger than
a statement just over F_p. Put

    Bstar=T B2=T B0+2tau H.

Then

    bar(A) Bstar = -N bar(H)iH.                         (V3)

So every coefficient is divisible by the **full N**, not only by its
radical. This is the common-image side. For the right-gcd side, let O_p
be the local Hurwitz order. Since `B0=iA`, its left ideal is O_p A.
Since T and H are invertible locally,

    O_p A + O_p Bstar = O_p A + O_p(2tau H)
                     = O_p A + p^v_p(tau) O_p.

The Smith form gives the exact index valuation `min(r,v_p(tau))`.
Consequently the accepted coefficient-content formulas give

    Norm(gcrd(A,Bstar)) = gcd(N,tau),
    Norm(gcld(A,Bstar)) = N.                            (V4)

The factor 2 may be omitted only because N is odd. Clearing T does
not change these gcd norms at primes dividing N; no other prime can
divide a common divisor's norm since it divides Norm(A)=N. If B2 is
integral, the same equalities hold with B2 in place of Bstar. This
also proves (V4) directly for the modular cleared-pair option, without
assuming final real-coordinate integrality.

Thus the output occupies the image component at **every** prime power.
At primes where tau is divisible it can additionally meet the kernel
component: the matching depth is exactly the capped valuation of tau.
A proper such right gcd is already the scalar gcd `gcd(N,tau)`. If
tau is a unit, the right kernels differ at every p; if N divides tau,
they agree to each full exponent. At a local intersection the words
"the opposite component" are not a unique label. The explicit image
identity avoids that ambiguity, including when iA is locally a scalar
multiple of A.

If B2 is an integer vector, its unique right multiplier also satisfies

    U=bar(A)B2/N in (1/N)Z^4.

But U is in `R_N^4` by its explicit formula. A rational number with
denominator dividing N and with denominator coprime to N is an integer.
Therefore U is an integer pure quaternion of norm 1, so

    B2 in {+/-A i, +/-A j, +/-A k}.                     (V5)

This last integrality argument itself does not require A to be primitive;
primitivity is required for the exact right-gcd formula and line language.
There is no omitted prime-power case. If a purported integral output
were imprimitive, its content would itself split N; on the unit chart
the local invertibility shows this cannot occur at a prime dividing N.

**Exceptions are not synonymous with no factor.** A right-axis associate
can have a proper right gcd with A. Here that factor is exactly (V4).
Conversely, (V5) excludes every nonexceptional twin on this chart. The
union of twelve signed left/right axes is a sufficient exclusion set for
the accepted twin theorem, not a characterization of all failed gcds.

## 4. Any word whose individual directions fix A

For completeness, the parent's separate word obstruction is correct.
If C is perpendicular to A and has norm c, direct multiplication gives

    R_C(U A)=A[bar(C)bar(U)C/c],
    R_C(A U)=[C bar(U)bar(C)/c]A.                       (V6)

Both bracketed multipliers have norm 1 if U does. Starting from `iA`,
an even number of reflections therefore has form `U A`; an odd number
has form `A U`. If every direction norm is a unit modulo N, every
multiplier remains in the order over R_N. Intermediate integrality is
irrelevant.

If the final point has integer coordinates, the same intersection
`R_N^4 intersect (1/N)Z^4=Z^4` makes its multiplier an integer unit.
Orthogonality makes it a signed imaginary axis. Even words preserve
right kernels and yield left-axis exceptions; odd words preserve images
and yield right-axis exceptions. Exact cancellation of nonunit raw
directions is outside these hypotheses. Nothing here restricts arbitrary
rational rotations or arbitrary two-sided multipliers.

## 5. The short single-reflection inequality

For the parent's actual test, take `C perpendicular A`, `c=Norm(C)`,
`b=<B0,C>`, and require the integer `m=-2b/c`. This divisibility test
is a sufficient integrality test. It becomes necessary for integrality
of the reflected vector if C is primitive; an imprimitive direction may
allow cancellation even when the displayed m is not integral.

On `gcd(c,N)=1`, the accepted reflection theorem and `O B0=O A` give

    Norm(gcrd(A,B0+mC)) = gcd(N,2b) = gcd(N,m).

If this gcd is proper, m is nonzero and `|m|>=p`, where p is the
smallest prime divisor. Cauchy gives

    |m| <= 2 sqrt(N/c),          c <= 4N/p^2.

For `N=pq` and `p<q<2p`, this proves `c<8`, with strictness coming
from `q<2p`. The proof covers repeated primes in the general inequality.
No quaternion-gcd advantage over the scalar m remains.

There is a stronger conclusion than was available in W005: section 4
shows that **every** integral output on this unit-c branch is a right-axis
exception, even if the intermediate coefficient had first been rational.
Thus the claim framed only for nonexceptional outputs is vacuously true.
The inequality remains useful, and nonvacuous, for proper scalar-gcd
successes among exceptional outputs. It does not establish their existence
or density. For `gcd(c,N)` proper, that gcd is already the factor; for
`gcd(c,N)=N`, neither this gcd-norm equality nor the unit-direction
obstruction applies. That branch is addressed below after normalizing
the effective direction, not discarded as impossible.

## 6. Why normalized unit directions are insufficient: explicit counterexample

Let

    P=x-y k,       Q=z+w j,
    s=x^2+y^2,     t=z^2+w^2,       N=st,
    A=P Q=(xz, yw, xw, -yz).

Assume s,t are coprime odd integers greater than 1; x,y and z,w are
coprime within each pair, all four are nonzero, and
`gcd(x y z w,N)=1`. These conditions make A primitive. Oddness excludes
`|x|=|y|` and `|z|=|w|`. This is a symbolic conditional family, not a
claim about an infinite prime family or a factor-blind input generator.

Choose the fixed parameters

    C=1,      E=j-1.

Their scalar data are

    c=1, d=2, h=-1,
    a=xz, b=-yw, f=x(w-z), e=y(w+z),
    tau=-xy t,       S=-xy t,
    H=x(-w+zj),      T=x^2 t,
    J=-y(z+wj),      L=y^2 t,
    D=-xy t j.

All follow by direct multiplication and dot products. In particular,
a,b,c,d are units modulo N. After cancelling D's nonzero scalar, the
two directions are **1 and j**, with norm 1 each, and

    R_j R_1(iA)=(yw, xz, -yz, xw)=P i Q.                (V7)

This is an integer norm-N twin perpendicular to A. Its left multiplier
`P i P^(-1)` has two nonzero imaginary coordinates, as does its right
multiplier `Q^(-1)iQ`; neither is a signed axis. Thus it is nonexceptional.
Their reduced denominators are s and t respectively: primitivity of each
two-coordinate factor and its odd norm prevent further cancellation.
Consequently `g_V=t` and `g_W=s`. The output matches A's right kernel
at the full prime powers in t and A's image at the full prime powers in
s. This is actual CRT component mixing, with no squarefree assumption.
This directly refutes a unit-denominator claim about the normalized
two-reflection operator, even for this supplied parameterization.

It does not refute the raw chart theorem: here

    gcd(N,tau)=gcd(N,T)=gcd(N,L)=t,
    gcd(N,Norm(D))=t.

The fixed-degree formula has already exposed a proper factor before
normalization. The actual representation failing the generic hypothesis
is the nonunit homogeneous scale of D and the nonunit effective norm T.
Increasing a direction box is not what acquires this component choice;
the special input representation encodes it.

## 7. Nonunit norms with full gcd N: cancellation and a second counterexample

A proper scalar gcd of any parameter is of course a factor. A full gcd
is not. To see that this distinction matters, instead take

    P=x+yi,       Q=z+wi,       A=P Q,       B=P j Q,
    s=Norm(P)>1, t=Norm(Q)>1,   gcd(s,t)=1, N=st odd,
    gcd(x,y)=gcd(z,w)=1,        xyzw != 0.

A and B are primitive, equal-norm, perpendicular, and nonexceptional:
their one-sided multipliers have two nonzero coordinates. A and B0=iA
lie in the complex i-plane, whereas B lies in the j,k-plane, so also
`<B0,B>=0`. Feed the already specified target into

    C=A,        E=B-B0.

Then

    c=a=N, b=f=h=0, d=2N, e=-N,
    S=0, tau=N^2, D=N^3 E,
    T=2N^3, L=N^3, Norm(D)=2N^7.

The first reflection fixes B0; the second returns B. Every one of the
listed raw scalar gcds with N is either 1 or N, never a proper factor.
Thus a blanket assertion that useful off-chart outputs are always caught
by one of these *raw* scalar gcds is false. This example takes a known
factored representation, and E explicitly contains the target B; it
does not supply an N-only algorithm or a useful sampling probability.

There is nevertheless an exact polynomial-cost cancellation test. For
any valid output of P1, form

    M=-bar(H)iH,
    G=gcd(T,M_0,M_1,M_2,M_3),       delta=T/G.           (V8)

Delta is the reduced common denominator of U=M/T. If B2 is integral,
`U=bar(A)B2/N` gives

    delta = N/g_W,     g_W=gcd(N,coefficients(bar(A)B2)).

For a nonexceptional twin, the accepted content theorem gives
`1<g_W<N`, hence `1<delta<N` and delta divides N. Thus its factor is
visible through ordinary scalar gcd and cancellation, even when every
raw norm gcd was full. In the present family the multiplier is
`Q^(-1)jQ`, whose reduced denominator is exactly t: the coefficients
`z^2-w^2` and `2zw` have no common factor with the odd norm t. Formula
(V8) therefore recovers t.

This is an explicit content computation, not a claim that finding the
parameters is easy. Delta may have primes outside N before integrality
has been established. One may always test `gcd(delta,N)`, but one may
assert `delta|N` only after the integrality condition (or an equivalent
local condition) is proved. Similarly, nonunit raw denominators cannot
be inverted modulo N before cancellation.

## 8. A more concrete treatment of the full-gcd branch

The following additional deductions sharpen that branch and supply an
actual inexpensive test, rather than a proposal to enumerate more D's.
Divide H by its integer content g, writing `H=g H0`, where H0 is
primitive. Set

    T0=Norm(H0),       tau0=-<B0,H0>,
    B2=B0+(2tau0/T0)H0.

Final integer coordinates are equivalent to `T0|2tau0`: a Bezout
combination of H0's coordinates proves necessity. Suppose B2 is an
integral nonexceptional output and `gcd(T0,N)=N`. Put
`m0=2tau0/T0 != 0` and `T0=lambda N`. Then

    m0^2 lambda N=Norm(B2-B0)<=4N,
    lambda m0 is even,

the second assertion using odd N and `T0 m0=2tau0`. The possible
positive lambda and nonzero integer m0 leave only:

* lambda=1, |m0|=2, which attains equality and gives B2=-B0;
* lambda=2, |m0|=1;
* lambda=4, |m0|=1, which again gives B2=-B0 and would make H0
  a nonprimitive multiple of B0.

Lambda=3, |m0|=1 fails parity. Consequently the nonexceptional case
necessarily has

    T0=2N,       |m0|=1,       <B0,B2>=0.              (V9)

Thus after primitive direction normalization, the remaining full-gcd
case is the **simultaneously perpendicular** shell, not an arbitrary
three-dimensional twin search.

Here is an actual computation for it. Write

    A=z+w j,     z,w in Z[i],
    eta=gcd_Z[i](z,w),      h_eta=Norm(eta).

The Gaussian Euclidean algorithm computes eta in polynomial bit time;
`h_eta|N`. If `1<h_eta<N`, stop with that factor. If `h_eta=1`, there
is **no nonexceptional** integral B perpendicular to both A and iA.
Indeed, write B=v+u j. The two orthogonality equations are exactly

    z bar(v)+w bar(u)=0.

After `z=eta z0`, `w=eta w0` with z0,w0 coprime in Z[i], all integer
solutions are

    B=lambda(-bar(w0)+bar(z0)j),       lambda in Z[i].

Their norm is `Norm(lambda) N/h_eta`; the shell condition is precisely
`Norm(lambda)=h_eta`. When h_eta=1 this gives only the four left axes
`+/-jA,+/-kA`, up to Gaussian units absorbed from eta.

If h_eta=N, then `Norm(z0)+Norm(w0)=1`. A lies in one of the two
coordinate complex planes, up to a Gaussian unit. The residual problem
is an alternative Gaussian representation of N with a useful choice
of prime factors. The second example in section 7 lies exactly here.
Enumerating `0<=u<=floor(sqrt(N))`, testing whether `N-u^2` is an
integer square, and checking the resulting signed lambda gives a finite
`O(sqrt(N) poly(log N))`-bit reference search. It is not an improved
factoring bound. The proper Gaussian gcd case costs only polynomial
work and should precede such a search; merely invoking a two-squares
oracle in the h_eta=N case would leave acquisition unpaid.

This Gaussian test is a materially different actual computation from
the four-coordinate reflection loop, with a proved interpretation and
priced failure cases. It is also closely related to established
Gaussian/quaternion divisor tests, not asserted as new prior art.

## 9. Costs, remaining acquisition, and an honest replacement computation

Let n be the bit length of N and let beta bound the bit lengths of the
input coordinates C,E. A has O(n)-bit coordinates. All of c,d,a,b,e,f,h,
S,tau,H,J,T,L,D and the unreduced reflection numerators are fixed-degree
expressions in these inputs. Each has `O(n+beta)` bits; a product of
several such scalars still has that asymptotic width because its degree
is fixed. Norm tests, coordinate contents, exact divisions, modular
inverses when legal, and (V8) therefore take conservatively
`O((n+beta)^3)` schoolbook bit time and `O(n+beta)` working bits per
candidate. No enormous rational iteration is hidden in this bound.

The Gaussian Euclidean test uses exact nearest-Gaussian-integer rounding.
Each nonzero remainder has norm at most half the divisor's norm, so
there are O(n) divisions on O(n)-bit numbers. It costs O(n^3) schoolbook
bit time and O(n) working bits. It needs no prime factors or external
package. It does not need to be executed in this symbolic review.

Input acquisition, enumerating/sampling C,E, primitive normalization,
all rejections, and the number of attempts remain charged. A box of
eight coordinates of height 2^beta has exponentially many candidates
in beta; the fixed-degree formula supplies no useful-output law.

On the unit-T branch an exact computational replacement is to skip D,
the reflections, and final integrality completely, and compute

    v=b A-a B0,       tau=<v,E>,       gcd(tau,N).

This recovers **every** right-gcd success on that branch. If the content
gcd of v with N is proper it already splits N. If that content gcd is
1, and E is uniform in `(Z/NZ)^4`, tau is exactly uniform in Z/NZ:
the linear homomorphism is surjective by Bezout, so all fibers have
equal size. For a balanced distinct-prime semiprime the resulting
success probability is

    1/p+1/q-2/(pq) = Theta(N^(-1/2)).

This law is for the unrestricted scalar experiment. Conditioning on
`gcd(T,N)=1`, on D being nonzero, or on final integrality can change it,
so it is not transferred to the reflection sampler. If the content gcd
of v is N, the scalar is identically zero. Uniform residues can be
generated by charged rejection sampling, or by a stated finite random
budget with failures retained. This is an actual paid scalar-gcd
computation, not an asymptotic gain or a changed favorable correlation.

Beyond the unit branch, sections 7–8 specify exact cancellation and
Gaussian-gcd operations. No faster factor-blind acquisition algorithm
for their remaining alternative-representation case is proved here.
The accepted construction `A=P Q -> P u Q` after a supplied factor
remains a polynomial-cost conversion, and factoring first remains an
honest upper-bound comparator. Adding reflections that fix A cannot
change the obstruction in section 4. Arbitrary transformations require
their own analysis; (V7) already prohibits a universal rotation claim.

## 10. Coefficient portion of the supplied wave

### Central selector

For odd primes `p<q<2p`, set `m=(pq-1)/2`. The supplied identity

    gcd(binomial(pq-1,m),pq)=p

is correct. In base q the digits of pq-1 are `(p-1,q-1)` and those of
m are `((p-1)/2,(q-1)/2)`, written most significant first. The two
digit-binomial factors are nonzero modulo q. This follows directly
by expanding `(1+X)^(pq-1)` in characteristic q using
`(1+X)^q=1+X^q`; no unknown-prime computation is supplied to the solver.

In base p, pq-1 has digits `(1,q-p-1,p-1)` and m has leading zero
followed by `((q-1)/2,(p-1)/2)`. The upper nonzero lower digit exceeds
q-p-1, because `2p+1-q>0`. Its coefficient therefore vanishes modulo p.
More precisely, Legendre's factorial sum gives

    floor((pq-1)/p)-2 floor(m/p)=0,
    floor((pq-1)/p^2)-2 floor(m/p^2)=1,

and all higher terms vanish, since `pq<2p^2<=p^3`. At q the first
term is zero and higher ones vanish because `pq<q^2`. Thus the exact
valuations are 1 at p and 0 at q. This statement has the distinct-prime
balanced promise; it does not cover arbitrary repeated-prime inputs.

The elementary bounds
`2^(N-1)/N <= binomial(N-1,(N-1)/2) <= 2^(N-1)` prove its Theta(N)
output bit length. Computing that integer is not a poly(log N) method.

### Cyclic folding and cost

Reduction modulo `(N,X^L-1)` really produces

    F_r = sum_{0<=j<=N-1, j congruent r mod L} binomial(N-1,j) mod N.

Binary exponentiation uses O(log N) length-L multiplications; schoolbook
cyclic convolution uses O(L^2) modular operations per multiplication.
Reduce every product and accumulated sum modulo N, so operands remain
O(n) bits. This gives O(L^2 n^3) schoolbook bit time, plus conservatively
O(L n^3) for the L final gcds, and O(Ln) working bits when L is at most
polynomial in N. If permitting fantastically larger L, index/counter
widths must additionally be charged in log L. None of this preserves
a selected coefficient automatically.

For L=2 the two coefficients are both `2^(N-2)`, hence units for odd N.
For L=4 in the conditional family `q=2p-1`, `p=1 mod 4`, the parent's
obstruction is correct, including the evaluation at -1: it is **0**.
At fourth roots `1,-1,i,-i`, respectively, the values are

    modulo p:  (1,0,1,1),
    modulo q:  (1,0,alpha,alpha),       alpha in {+1,-1}.

Here p-1 divides N-1. Modulo q-1, the exponent N-1 is `(q-1)/2`.
Also q=1 mod 8, so 2 is a square: for a primitive eighth root zeta in
F_q, `(zeta+zeta^(-1))^2=2`. Hence the first value is 1. The two last
values agree since `1-i=-i(1+i)` and `(q-1)/2`
is divisible by 4. The inverse transform is exactly

    (F_0,F_1,F_2,F_3)
       = (1+2alpha, 1, 1-2alpha, 1)/4.                (V10)

For p take alpha=1. All numerators are among 3,1,-1, and none vanishes
for p,q>3. Division by 4 is legal. No assertion about infinitely many
members of this conditional prime family follows.

This also identifies the actual contaminating alias class. Write
`p=4k+1`, so `m=2k(8k+3)`. Its residue modulo 4 is 0 when k is even
and 2 when k is odd. The central summand itself is zero modulo p, but
the sum of **all other** summands in that same class is respectively
`3/4` or `-1/4` modulo p, by (V10). Those aliases erase the zero selector.
This is an exact aggregate identity, not an identification of one
privileged cancelling term or a conclusion about every degree menu.
For the supplied member 37*73, k is odd and the affected class is 2.
No screen or central-binomial evaluator was run.

A literal way to remove all aliases is truncation modulo `X^(m+1)`,
keeping coefficients 0 through m during exponentiation. It needs
Theta(N) residues, Theta(Nn) bits, and O(N^2 n^3) schoolbook bit time.
This is an actual isolated-coefficient computation, priced and
exponential in n; it is not a suggested improvement. Known-prime-power
evaluation formulas do not provide an unfactored-N shortcut merely by
being named.

## 11. Bounded primary-source check and read scope

The mathematical identities (V1)–(V10), the two counterexample families,
and the full-gcd normalization argument were derived symbolically here.
No novelty assertion is made for them. The accepted W005 reports supply
the precise primitive coefficient-content and twin statements used above;
their sampler law is not generalized to this correlated generator.

Primary-source retrieval was bounded to these topics:

* [Machiavelo–Roçadas, *Connections between the Arithmetic and the
  Geometry of Lipschitz Integers*](https://cmup.fc.up.pt/main/sites/default/files/publications/Quaternions_AM_LR.pdf):
  the tool returned text from printed pp. 1–8; the relied-on reading is
  Theorem 3.1/Corollary 3.2 on p. 4 and Theorem 3.4 plus the following
  factoring paragraph on p. 5. The latter explicitly connects insertion
  between quaternion factors with factoring, and its theorem concerns
  the Gaussian-coordinate gcd. That is prior art for the underlying
  route, not a source for the new parameter calculation or a fast twin
  acquisition theorem. No further references cited in it were followed.
* Andrew Granville's author-hosted
  [introduction](https://dms.umontreal.ca/~andrew/Binomial/intro.html),
  [residue-class sum section](https://dms.umontreal.ca/~andrew/Binomial/sumsofbcs.html),
  and [prime-power computation section](https://dms.umontreal.ca/~andrew/Binomial/modptoq.html)
  of *Arithmetic Properties of Binomial Coefficients*: returned HTML
  lines 0–83, 0–24, and 0–54 respectively. The focused scope was the
  introductory Kummer/Lucas discussion, the existence of classical
  residue-class congruences, and the explicitly supplied prime-power
  input to Theorem 3 and its algorithm. The author's 1997 publication
  page and contents page were navigation only. The linked PDF returned
  404; two formula GIF requests were unsupported/forbidden. Therefore
  no detailed fast-evaluation bound is claimed from unseen formulas.
  The exact digit/valuation and L=4 proofs above are independent.

The old Lucas/carry mechanism and residue-class-sum subject are clearly
established mathematics. This bounded read did not determine the first
appearance of the exact balanced-semiprime selector A1 or P1. Failure
to find an exact occurrence is not evidence of novelty. No secondary
search snippet is used as a mathematical authority.

Local inputs read: AGENTS.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md,
docs/SPECIFICATION.md, README.md; the current resume section of
research/STATE.md; the full mathematical core and surrounding discussion
of W005-quaternion-validation.md and W005-orthogonal-review.md; and
W006-reflection-parameterization.md. Some broad combined file reads were
truncated by the output budget; the quaternion core and orthogonal
opening were re-read in bounded ranges. No other child's W006 findings
were read, and no shared file was modified. Source retrieval, ordinary
document reading, and writing/reviewing this report were the only work
executed by tools.

## 12. Recommended disposition and next decisive work

Accept B1/B2, P1, and the short-reflection inequality with the qualifications
above. Replace the conjectural generic-component wording by (V1)–(V5).
The exact failure is the norm factorization and resulting one-sided
multiplier with unit effective denominator, not a generic statement that
rational quadrics or shell generation are difficult.

Keep raw and normalized charts separate. Accept the A-perpendicular-word
obstruction (V6); reject any extension to arbitrary unit-denominator
rotations, including to all normalized two-reflection instances of P1.
Do not classify a full raw scalar gcd N as success. Sections 6–8 specify
where proper scalar gcds suffice, where cancellation matters, and what
the remaining simultaneous-orthogonality branch actually computes.

The next useful parent proof would analyze a **specified off-chart
acquisition operation** after primitive normalization and the Gaussian
gcd check, giving its retained factor probability and complete cost.
For the supplied generic branch, a larger box, more fixing-A reflections,
or a numerical screen cannot overturn the identity. For coefficient
compression, a different retained representation must preserve the
middle block with an explicit dimension and bit-cost argument. This
review authorizes or launches no experiment. There is presently no new
complete factoring improvement.
