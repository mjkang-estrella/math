# H012 — checked algebraic certificate interface

Date: 2026-10-08. [Factoring/Certificates.lean](../../Factoring/Certificates.lean)
formalizes the exact algebra used by reciprocal certificates. This is existing
algebraic machinery, not a new complexity result or a formalization of the
Python prototype.

The certificate stores signed integer u,v,t and integer witnesses for
`v+2uj=m*slope` and `Nt+uj²+vj=m²*constant`. It also requires u or t nonzero.
Five Lean theorems check:

1. Its integer polynomial evaluates to `(up²+vp+Nt)/m²` at p=mx+j,
   expressed without division so it is valid even at degenerate m.
2. For N=pq, p=mx+j and gcd(m²,p)=1, there exists an integer i with
   `m²i=up+v+tq`. The proof explicitly cancels the coprime p from divisibility.
3. Such a quotient implies `up²+(v-im²)p+tN=0`.
4. For nonzero p, that recovery equation is equivalent to the exact quotient.
5. For nonzero N the recovery polynomial has a nonzero coefficient, using
   the excluded constant-quotient direction.

The algebra does not require primality of p. A modular exponent collision is
not identified with the exact quotient: order bounds and partial-collision
recovery are separate obligations. Likewise no bound on i, interval cover,
number of certificates, search cost, or existence of a fast factorer is assumed
or concluded. Signed coefficients and zero u/t cases are included in the
statements. The module is imported by Factoring.lean and each theorem is in
Audit.lean; the kernel, source screen and printed assumptions are checked by
the ordinary project check command.
