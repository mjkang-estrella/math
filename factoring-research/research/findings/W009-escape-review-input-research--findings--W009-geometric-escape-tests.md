# W009 — explicit tests of the geometric escape routes

2026-10-08. Parent derivations, PROVISIONAL pending an independent E audit.
No candidate run or new factoring bound. These computations test proposed
ways around the four-fiber reset, rather than treating a lost certificate
as proof of persistent useful structure.

## 1. Coalescing the two roots gives the existing odd reciprocal rule

Deliberately replace the distinct-anchor fold by

    G_y(z)=(z-y)^2/z.

This is a different protocol: y=w, so the previous pair sampler, its clean
probability and its moment laws no longer apply. Suppose P=S^2 is carried
with an explicit square-root CIRCUIT S, initially S=X. Acquire a=S(r) on
a paid unit chart and set y=a^2. Then

    G_(a^2)(S^2)=(S-a^2/S)^2,
    S_new=S-a^2/S.                                                   (1)

No square root modulo N is computed; S was part of the maintained state.
The proposed escape is exactly the one-anchor odd reciprocal mechanism
already written in W009-odd-paired-fold.md. The apparent retained square
index in P supplies no additional factor channel: for odd squarefree N,
gcd(U^2,N)=gcd(U,N), and the same for denominators. Evaluation through S
avoids redundant squaring. It preserves one known square representation,
not an accumulated 2^k-th power.

The residual drift for S remains
sum_a nu(a)*Gamma(-a^2)-4*sum nu^3, with raw root/pole increment 2*sum nu^2.
Any gain must come from this changed weighted incidence, not from describing
the same state as its square. Degree on S is 2 per stage, not 4.
Acquisition costs O(k^2) and a probe O(k) with the explicit chain.

## 2. Elliptic coherence is real, but the cheap cycle is doubling

There is another structured interpretation of the ORIGINAL distinct-anchor
fold that does not rely on torus frame alignment. Write its anchors r,s
here, to distinguish them from a curve's second coordinate. Over any odd
field with r*s*(r-s)!=0, define

    E: Y^2=X*(X-r)*(X-s)=X^3+A*X^2+B*X,
    A=-(r+s), B=r*s.

The usual degree-two isogeny with kernel {O,(0,0)} has x-coordinate

    X'=X+A+B/X=(X-r)*(X-s)/X,

and y-coordinate Y'=Y*(1-B/X^2). Its target is

    E': Y'^2=X'^3-2A*X'^2+(A^2-4B)*X'.                              (2)

Thus the reciprocal fold has a coherent elliptic interpretation. A
generic changing sampled pair need not define the previous target curve;
the mere existence of (2) is not coherence for the original sampler.

The target has full displayed 2-torsion if one can acquire sqrt(B).
A completely explicit family does that: start r=u^2,s=v^2, gcd-checking
u,v,u-v,u+v individually modulo N. Then the two target anchors are

    r'=-(u-v)^2,  s'=-(u+v)^2.

Their product is (u^2-v^2)^2, so the next distinguished isogeny is again
available. Two folds satisfy the exact rational identity

    F_(r',s')(F_(r,s)(X))
      =(X^2-r*s)^2 / [X*(X-r)*(X-s)]
      =4*x([2]Q),                                                   (3)

where x(Q)=X on E or its quadratic twist. The target coefficients after
two steps are 4A,16B, an isomorphic scaling of E. Continuing this known
parameter schedule gives

    P_(2k)(X)=4^k*x([2^k]Q).                                        (4)

Coefficients require only modular additions/multiplications, and the map
has an O(k)-operation projective evaluator. There is no hidden square-root
oracle or random frame-alignment event. This is a genuine cheap coherent
computation, but it is already elliptic doubling. The old W001 dynamics
Card 3 explicitly describes the dual-edge cycle and unchanged odd-order
part. The NEW work here connects W009's sampled rational fold to it and
derives its exact uniform-x supply below; it is not a new factoring method.

## 3. Uniform x sees a curve and its twist; exact kernel supply

Fix a good odd prime and a nonsquare d. Write E^d in the model
d*Y^2=X*(X-r)*(X-s), so its x-line is literally the same. Every rational
projective x-value lifts to E(F_p) or E^d(F_p), and to both exactly at
the rational branch points (including infinity).

For a positive integer m, let
a_m=|E(F_p)[m]| and b_m=|E^d(F_p)[m]|.
The proposed exact pole count of the multiplication x-map on P^1(F_p) is

    # {x : x([m]Q)=infinity} = (a_m+b_m)/2.                          (5)

Proof: negation pairs the m-torsion points except their 2-torsion.
Put t_m=|E(F_p)[gcd(m,2)]|, the same on the twist. Their distinct x counts
are (a_m+t_m)/2 and (b_m+t_m)/2; their intersection has size t_m.
Subtracting the overlap proves (5). This reasoning includes O and
does not require choosing a square root or an actual point in the evaluator.

For uniform AFFINE input, the initial infinity point must be removed, giving

    h_m=(a_m+b_m-2)/(2p).                                          (6)

For the even-stage chain (4), m=2^k. In terms of invariant factors
E(F_p)=C_a x C_b and its twist C_c x C_d, the two quantities in (6) are

    a_(2^k)=gcd(a,2^k)*gcd(b,2^k),
    b_(2^k)=gcd(c,2^k)*gcd(d,2^k).

They saturate at the 2-primary subgroup sizes, rather than geometric
degree 4^k. A denominator-only probe on N=pq has proper-factor probability
h_p*(1-h_q)+h_q*(1-h_p), for a FIXED good curve and fresh uniform x.
Extra root/intermediate gcds need their own union of kernel cosets and
must not be silently identified with this one test.

This is analysis of the actually available x-coordinate circuit. The two
curve orders, their invariant factors, twist selection and torsion points
are not inputs to it. Including a twist does not create fresh independent
curve-order trials. This exact supply law gives a decisive comparison
before any numerical benchmark: more doubling depth cannot remove the
odd-order components. No improved general factoring bound follows.

## 4. Changing kernels exposes a paid square-root condition

To avoid taking the dual edge, choose the known kernel (r,0) rather than
(0,0). Translating X by r yields the remaining roots -r and s-r,
so the new coefficient B is

    B_r=r*(r-s).

Full target 2-torsion then requires a square root of B_r, not merely of r*s.
For the initial r=u^2,s=v^2 this becomes sqrt(u^2-v^2), apart from the known
factor u. A Pythagorean parametrization can make that ONE branch available.
It does not supply an all-depth nonbacktracking generator. At a prime a
degree-2 chain still preserves every odd-primary part of a carried point's
order. Obtaining a rough-degree kernel would need a different paid procedure;
if that kernel's order already annihilates the carried point, ordinary
scalar multiplication is the comparison.

Primary-source leads, not yet adopted as a complete chain classification:
the rational cyclic-isogeny degree classification would prohibit a cyclic
2^k isogeny over Q for k>=5. A nonbacktracking chain must first be shown
to have cyclic composite kernel, and this characteristic-zero restriction
must NOT be transferred to arbitrary N-dependent modular coefficients.
The independent audit should verify exactly that scope if it uses the lead.

The next meaningful escape would need either a useful finite-field
correlation outside the geometric power index, a paid nonisogenous transfer
that retains useful fiber data while changing order, or a faster scalar
detector. None is supplied by these identities. Keep that distinction
rather than relabeling the dual cycle or the square of S as a new algorithm.

