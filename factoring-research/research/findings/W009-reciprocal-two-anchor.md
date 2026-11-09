# W009 — two-anchor reciprocal folding and a two-color factor test

Post-review: the original derivation below is preserved. Its exact laws
are accepted in the [parent disposition](W009-reciprocal-disposition.md),
which also corrects overclaims in the independent review. Persistence and
complexity improvements remain unproved; the newer simple-pole envelope
has its own ongoing audit.

2026-10-08. New parent constructive variant, PROVISIONAL. No candidate
run, shared solver/Lean edit, or claimed complexity improvement.
This is not in the frozen three-anchor audit. It removes the third
training evaluation and avoids pinning energy at a sampled translation.

## The changed computation

For a current rational circuit P, draw two fresh input residues and
evaluate finite nonzero values y,w. Gcd-test the projective denominators,
y,w and y-w. A proper gcd is a factor; full-gcd chart failure is charged.
On the unit/distinct chart use

    F_(y,w)(z)=(z-y)*(z-w)/z = z-(y+w)+(y*w)/z,
    P_new=F_(y,w) composed with P.

In projective coordinates the actual update is

    [U:V] -> [(U-y*V)*(U-w*V) : U*V].                 (1)

No square root or per-point division is used. The map has degree two
over each component because y*w is a unit, and it has no local basepoint.
It sends 0 and infinity to infinity, and y and w to zero. Thus the union
of the root and pole fibers is absorbing, although the zero color moves
to the infinity color at the next update.

The involution is iota_c(z)=c/z with c=y*w, and

    F(z)-F(u)=(z-u)*(z*u-c)/(z*u).                    (2)

The output translation y+w plants the sampled orbit at zero; the whole
collision partition depends only on the PRODUCT c. This is an actual
alternative to the three-anchor sampler's pinned shifted energy.
Two acquired evaluations per stage still cost O(k^2) work through depth k;
each fresh probe costs O(k). This reduces a constant, not the exponent.

## Exact proposed local law, including chart rejection

Fix the projective output law mu. Set z0=mu(0), h=mu(infinity), let nu be
its restriction to F_p^*, and define s=sum nu, v=sum nu^2, u3=sum nu^3,
q4=sum nu^4. The local legal probability is

    ell2=s^2-v.

For c!=0 put

    Gamma(c)=sum_(a*b=c, a!=b) nu(a)*nu(b).

The unnormalized probability of acquiring c is exactly Gamma(c), and
sum_c Gamma(c)=ell2. Thus pair sampling automatically favors reciprocal
involutions with large current pairing mass; this is not an energy oracle.

For a fixed legal pair,

    z0_new=nu(y)+nu(w),
    h_new=z0+h,
    v_new-v=Gamma(c)-(nu(y)+nu(w))^2.                 (3)

The full collision gain is 2*z0*h+Gamma(c). Removing the squares of
both new atoms cancels 2*z0*h and gives (3). In particular the planted
pair's 2*nu(y)*nu(w) contribution is already part of Gamma and must not
be counted a second time.

Summing over the actual ordered samples yields

    ell2*E[v_new-v | legal]
      =sum_c Gamma(c)^2 - 2*s*u3 - 2*v^2 + 4*q4,
    ell2*E[(z0+h)_new-(z0+h) | legal]=2*(s*v-u3).     (4)

This turns the positive term into ordinary multiplicative energy of
the residual law, with its diagonal removed. The key remaining question
is whether that energy persists after the reciprocal fold. A high-energy
initial law alone is insufficient.

## A concrete favorable input law and its unpaid persistence

If nu is flat, mass s/m on a multiplicative subgroup G of size m>=2,
then every sampled c lies in G and iota_c preserves G. For odd m,
each c has one fixed point in G; for even m half have two and half zero.
The proposed averaged drift from (4) is

    odd m:   E[Delta v | legal]=s^2*(m-5)/m^2,
    even m:  E[Delta v | legal]=s^2*(m^2-6*m+6)/(m^2*(m-1)).

Thus a large flat subgroup law nearly doubles v for ONE update. The
next nonzero support is a translated trace set {z+c/z-(y+w): z in G},
not automatically another multiplicative subgroup. Treating it as one
would assume away the main bottleneck. Starting with x^d gives a
subgroup image but obtaining a large kernel depends on gcd(d,p-1), the
usual local-order issue; that is not a new free generator.

For the actual uniform affine start and fixed legal y,w, the finite
output counts have the explicit shape

    n(b)=1+chi((b+y+w)^2-4*y*w),
    n(infinity)=1,

where chi is the Legendre symbol with chi(0)=0. The zero count is two.
This identifies the next cheap symbolic question: compute or sharply
bound the multiplicative energy of THIS trace law, with the zero and
infinity atoms removed, instead of extrapolating the subgroup drift.
An initial almost-doubling of v is not evidence of persistent doubling.

## Why separate numerator/pole tests matter

For a fixed valid projective map modulo N=pq, let (z_p,h_p,r_p) and
(z_q,h_q,r_q) be the probabilities of zero, infinity, or neither at
each prime for a fresh uniform input. Test gcd(U,N) and gcd(V,N)
separately. The exact proposed proper-factor probability is

    s_factor=1-r_p*r_q-z_p*z_q-h_p*h_q.               (5)

Different local colors produce a proper gcd. In particular zero at p
and infinity at q is useful, even though gcd(U*V,N)=N would mask it.
Both zero at both primes and infinity at both primes fail. Valid
projective coordinates ensure U,V do not simultaneously vanish locally.
The formula is conditional on the constructed map; stopped histories
still need their actual joint distribution.

This offers a concrete benefit over a single absorbing zero: if both
local maps reach a nonconstant two-color partition, they can still
yield factors. It is not a procedure for acquiring that partition.
A globally computed binary label does not supply separate local colors.

## Decisive validation gate

First audit (1)-(5), including even/odd subgroup cases, local basepoints,
and clean-chart acquisition over the composite ring. Next inspect the
actual trace-law energy or its primary-source bound. Do not run a depth
sweep before identifying a non-forced energy contribution capable of
beating the paid k^2 training plus k-per-probe cost. This adaptive rule
must be compared with known trace/torus rational maps without importing
their group-order information or confusing a fixed map with this changing
sampled parameter. No such end-to-end improvement is currently supplied.
