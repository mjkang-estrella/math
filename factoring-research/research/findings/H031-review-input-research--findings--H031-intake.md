# H031 — Coordinator intake: productive roots across fields

2026-10-08. **Exploratory organizing calculation; not an accepted new algorithm.**
Verified full factoring complexity improvement: **NONE**.

The prior-art gate is explicit. Lee–Venkatesan section 7 already treats the
productive-root character, its independence from imposed constraints, and a
multiple-field extension. H028's accepted reconstruction already combines
fieldwise algebraic squares while imposing rational parity globally.
A reformulation of those operations is not a new mechanism.
[Primary text, section 7](https://arxiv.org/html/1805.08873v1).

Here is a finite packet interface to make a proposed sampler accountable.
Let N=pq with distinct p,q congruent to 3 modulo 4. The algorithm receives
N alone. Choose a common list of prime units b_1,...,b_s. A paid packet is
a unit x modulo N, a positive fully factored integer
r=product_j b_j^a_j, and a verification x²=r mod N. Define

    v_j=a_j mod 2,
    c=product_j b_j^floor(a_j/2) mod N,
    z=x*c^(-1) mod N.

Then z²=product_j b_j^v_j mod N. Two actual packets with the same v give
rho=z_1*z_2^(-1), rho²=1. If Jacobi(z_1,N) and Jacobi(z_2,N) differ,
rho has mixed CRT signs and gcd(rho-1,N) is a proper factor. This is an
elementary organizing identity to check, not a method to obtain the packets.
Positive r is an explicit restriction; signed data require a sign coordinate
and a separately justified normalization.

In a number-field source, obtaining x means actual algebraic-square extraction
and a verified reduction map with unit denominators. Even ideal parity does
not supply x. Finding matching rational parities, making packets distinct,
and obtaining opposite signs all require costed algorithms and justified
laws. A birthday argument over an exponentially large parity space is not
free. Producing a basis of packets can require many expensive algebraic roots;
one cannot charge only the final successful root.

The selected constructive lens is a coupled pair of input-only polynomial
families with common modular root, such as a fully specified
f_2=f_1+(X-m)g family. Generation, actual heights, relation streams, separate
field ideal constraints, and maps must be constructed. Seek an actual random
law and mechanism giving a productive matching pair; field independence,
uniform parity, nontrivial character restrictions and root-sign randomness
are not assumptions to import. More fields or a larger matrix alone do not
resolve the existing character gap.

H030 owns exact RootProduct batching and must not be duplicated. H031 has
a different possible outcome: a rigorous useful-congruence bound initially
for this restricted prime family. Such a result would still need its precise
scope and comparison; it would not establish general polynomial factoring.
No experiment or code is selected by this intake.
