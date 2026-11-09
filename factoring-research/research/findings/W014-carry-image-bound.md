# W014 Composite denominators and the carry image

2026-10-08. Parent continuation of W014 B, pending independent review.
Verified complete factoring improvement: NONE. This gives a scoped obstruction
to one input generator for the explicit carry-image consumer; it is not a
lower bound on factoring or on implicit image processing. No experiment run.

## First remove a denominator that changes no rounded value

Let P(h)=a0+sum_(j=1)^d a_j*h^j in Z[h], M>=1, with fixed d>=1. Compute

    g=gcd(M,a1,...,ad),      M'=M/g,
    r0=a0 mod g,            c=(a0-r0)/g,
    Q(h)=c+sum_(j=1)^d (a_j/g)*h^j.

The Euclidean remainder satisfies 0<=r0<g, including negative a0. Then

    floor(P(h)/M)=floor(Q(h)/M')                 (1)

for EVERY integer h, because P/M=(Q+r0/g)/M' and adding a number in [0,1)
to an integer cannot cross the next multiple of the positive integer M'.
If M'=1 there is no carry search left. Otherwise, for each prime ell|M',
at least one nonconstant coefficient of Q is not divisible by ell. This
normalization needs only gcd and exact division, not factorization of M.

The original remainder image is r0+g times the image of Q mod M', so the
image cardinality is unchanged. The W014 consumer can instead use M', Q
directly because its rounded A is unchanged. Thus an obvious coefficient
common divisor must be cancelled before claiming image compression.

## Full residue image bound for a fixed degree

Parent claim. There exists C_d>0 depending only on d such that, under the
primitive nonconstant-coefficient condition above,

    |Q(Z/M'Z)| >= M' / (C_d*(2*d)^omega(M')),     (2)

where omega counts distinct prime factors. Hence, as M' grows with fixed d,
the full image has size at least M'^(1-o(1)). No factorization of M' is
required by the normalization or presumed free by an implementation; prime
powers here are used only to prove the image bound by CRT.

For a prime power ell^k with ell>2d, the reduction Q mod ell is a nonconstant
polynomial of degree at most d. Its derivative is nonzero and has at most d-1
roots. At least ell-d+1 residues have unit derivative. Their images number
at least (ell-d+1)/d, since a nonzero degree-d polynomial has at most d roots.
Each such regular image lifts to ALL ell^(k-1) residues with that image
modulo ell: lift a regular preimage one digit at a time. Consequently

    |Q(Z/ell^k Z)| >= ell^(k-1)*(ell-d+1)/d
                    >= ell^k/(2d).             (3)

For the finitely many primes ell<=2d, a bound uniform in coefficient size
and k is needed; simply ignoring these prime powers is invalid. Put

    s_max=floor(log_ell d)+v_ell((d-1)!).

Some coefficient of R=Q' has valuation at most floor(log_ell d), because
some nonconstant coefficient of Q is an ell-adic unit. There is an integer
x0 in {0,...,d-1} with s=v_ell(R(x0))<=s_max. To see this, if all R(x0)
were divisible by ell^(s_max+1), all their forward differences would be.
The Newton expansion of R in binomial(x,j), multiplied by (d-1)!, would
make every coefficient of R divisible by a larger power than its minimum
valuation. This contradicts the preceding coefficient bound. In particular
the selected derivative value is nonzero.

Taylor expansion at this integer x0 has integer coefficients and gives

    Q(x0+ell^(s+1)*t)-Q(x0)
      = ell^(2s+1)*(u*t+ell*V(t)),              (4)

where ell does not divide u and V is in Z[t]. The polynomial inside the
parentheses is a bijection modulo every ell^r: it is a nonzero linear map
modulo ell and has unit derivative, so every residue has a unique successive
digit lift. Thus Q's image modulo ell^k contains the complete coset
Q(x0)+ell^(2s+1)*(Z/ell^k Z) if k>2s+1. For smaller k, its image is at
least one point. In both cases

    |Q(Z/ell^k Z)| >= ell^k / ell^(2*s_max+1).   (5)

Take C_d as the finite product of ell^(2*s_max+1) for primes ell<=2d.
CRT makes the full image exactly the Cartesian product of the prime-power
images; (3) and (5) imply (2), with the harmless (2d) factor also allowed
for the small primes. The elementary omega(M')=o(log M') bound follows
by ordering its distinct primes: their product is at least omega(M')!,
so a fixed base to the power omega(M') is M'^(o(1)).

This argument includes d=1: s_max=0, and the stronger exact image size
M' also follows from its unit linear coefficient. A constant Q is treated
by M'=1 in the normalization, not by the derivative argument.

## Consequence and changed computation

If a block covers a complete residue system modulo M', the explicit image
list needed in W014 B has nearly M' entries at fixed degree. Merely choosing
M' composite cannot provide a fixed-power saving in that list length once
the irrelevant common divisor is removed. This closes a specific proposed
input shortcut even though the carry-aware consumer itself remains useful
as a conditional primitive.

The theorem does not assume or prove that a factor-search block covers all
residues. It does not yet cover an arbitrary retained domain, including a
domain excluding small-prime residue classes; extending the bound there
requires counting actual regular preimages. It also does not bound growing
degree uniformly (C_d is large), prohibit a compact image description, or
lower-bound a scalar product over an implicit image. These distinctions
identify actual changes to try:

* certify a sparse input domain containing a factor and obtain its image
  without scanning it; domain acquisition and coverage are part of the task;
* evaluate the collision product over a structured image without listing all
  of it, retaining tagged full-collision recovery;
* use a nonpolynomial integer circuit with simultaneously bounded exponent
  bit length, cheap inversion and a small exact carry image.

For example, applying Euler powering only modulo M' can make a small image
cheaply, but does not produce the integer exponent or solve the recovery
equation required by the consumer. That concrete mismatch must be removed
by a computation, not by relabeling modular evaluation as integer evaluation.
