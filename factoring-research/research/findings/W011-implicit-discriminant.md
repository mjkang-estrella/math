# W011 implicit discriminant: fast scalar, narrow selector

2026-10-08. Parent constructive calculation, not an independently reviewed
new theorem or factoring improvement. This is a different computation from
sampling output collisions: attempt to detect a useful collision across
an exponentially large implicit polynomial by computing its discriminant.

## Explicit scalar computation

Let f be monic of degree d, with d a unit modulo an odd semiprime N.
Set P_k=f composed with itself k times, degree D=d^k. Over an algebraic
closure of a component field, list the d-1 critical points c of f with
multiplicity. The chain rule and multiplicativity of the resultant give,
up to a sign irrelevant for gcd,

    Disc_X(P_k(X)-t)
      = +/- d^(k*d^k)
        product_(j=1)^k product_(f'(c)=0)
          (f^j(c)-t)^(d^(k-j)).                         (1)

Derivation: P_k' is the product of f'(P_i), i=0,...,k-1.
For each critical point c,
Res(P_k-t,P_i-c) equals, up to sign,
(f^(k-i)(c)-t)^(d^i), since P_k=f^(k-i) composed with P_i.
Each derivative factor contributes d^D. Reindex j=k-i.
These are polynomial/resultant identities, including root multiplicities;
geometric distinctness or rational critical points are not assumed.

The narrowly checked prior-art context is Gomez-Perez, Ostafe and
Shparlinski, [On irreducible divisors of iterated polynomials](https://ems.press/content/serial-article-files/38505),
section 3, Lemmas 1-3, printed pp.1125-1126. Their resultant composition
rules and critical-orbit discriminant recurrence confirm that the
compression itself is known. The shifted-target form (1) is derived
above; no novelty claim or inference about their later theorems is made.

For f(X)=X^d+c0, the only critical point is zero, with multiplicity d-1.
Compute u_0=0, u_(j+1)=u_j^d+c0 modulo N. Testing

    gcd(product_(j=1)^k (u_j-t), N)                       (2)

has exactly the same prime support as (1), after gcd(d,N) preprocessing.
Full product gcds are split with a product tree or individual leaf gcds;
a leaf equal to zero modulo N gives no factor and does not suppress
other leaves. This replaces a degree-d^k discriminant by k modular
exponentiations and O(k) products, plus extraction. It is executable
without polynomial expansion or known factors. Modular powering costs
O(log d) multiplications, with log d and all operand widths charged.
No numerical candidate experiment has been run.

## Why this saving does not multiply useful tests

Choose f and its whole orbit before a fresh uniform t modulo N.
At prime p not dividing d, the discriminant vanishes exactly when t
lies in the set {u_1,...,u_k} reduced modulo p. Thus

    Pr_p(discriminant zero) = |{u_1,...,u_k} mod p|/p <= k/p.

The probability of any proper-factor outcome from (2) and its leaves is
at most min(1,k/p+k/q). Full-gcd masking can lower it. The enormous degree
and exponents in (1) repeat prime support; they do not supply d^k
independent opportunities. A general monic f has at most k(d-1)
geometric postcritical values; only the values rational over F_p can
equal uniform t. Its analogous bound is k(d-1)/p, but acquiring critical
points or computing their orbit norms must also be paid.

This closes the specific random-target discriminant shortcut. It does
not bound adaptive target rules, pair collisions, periodic-point
discriminants, arbitrary compressed resultants, or factoring generally.

## Constructive response: what computation would have to change

The lost information is ordinary equality between distinct sampled
outputs; the discriminant only records ramification of a single fiber.
W010's priced batch detector retains ordinary equality, and W008's
four-list product retains a much larger implicit zero set, at the cost
of its unresolved scalar evaluation. Replacing either by (1) would
discard precisely the extra opportunities it needs.

A concrete broader family worth distinguishing is f(X)=X^d+aX.
Its critical points obey c^(d-1)=-a/d and their first images are scalar
multiples of c. With no constant translation this symmetry persists,
so the compact norm is controlled by roots of unity; its rational
support is restricted by gcd(d-1,p-1). It cannot count d-1 rational
critical images for free. Adding a constant translation breaks that
closure: already the next critical-image norm is a resultant involving
a binomial and a translated high power. The missing computation is then
a fast scalar resultant, not a supplied algorithm. Do not promote that
restatement to a survivor without an explicit recurrence and paid work.

The immediate useful outcome is an exact separation: exponential
algebraic degree can coexist with O(k) scalar work only because this
particular selector has O(k) opportunities. Keep the scalar-product
branch open, but require any proposed compression to preserve the
underlying distinct root events.
