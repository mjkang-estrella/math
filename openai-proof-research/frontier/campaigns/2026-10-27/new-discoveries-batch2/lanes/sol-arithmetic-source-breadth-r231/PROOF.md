# Complete ordinary bridge, uncredited

Source: Gallardo–Rahavandrainy, *A Polynomial Variant of Perfect Numbers*,
J. Integer Sequences 23 (2020), Article 20.8.6, printed p.6, computational
item 2. Journal body published 11 October 2020; retrieved 30 October 2026.
https://cs.uwaterloo.ca/journals/JIS/VOL23/Gallardo/gallardo7.pdf
The literal conjectural sentence is:

> “Ru is prime if and only if u is a prime number such that 2 is a primitive root modulo u”

Here the preceding paragraph fixes an odd integer u>1 and P=x²+x+1 in
F₂[x], with R_u=1+P+...+P^(u−1). Prime means irreducible polynomial.
The question about perfect powers R_u^(2^n) in the same paragraph is a
different, unsolved question; this proof does not settle it.

## All-parameter proof by a quadratic field extension

Put H_u(Y)=1+Y+...+Y^(u−1). If u=ab is composite, a,b>1, then
H_u(Y)=H_a(Y)H_b(Y^a). Substitution Y=P gives two positive-degree
factors. Thus irreducibility of R_u forces u to be prime.

Suppose u=ℓ is an odd prime. In an algebraic closure of F₂, the roots of
H_ℓ are exactly the nonidentity ℓth roots of unity. They are distinct:
Y^ℓ−1 has derivative Y^(ℓ−1), coprime to Y^ℓ−1. For a primitive ℓth root
α, its Frobenius orbit has length d=ord_ℓ(2), because
α^(2^j)=α iff 2^j≡1 mod ℓ. Its minimal polynomial consequently has
degree d. (A finite Frobenius orbit gives a polynomial with coefficients
fixed by squaring, hence in F₂; any F₂ polynomial vanishing at α vanishes
at the entire orbit.) Therefore H_ℓ is irreducible iff d=ℓ−1. If H_ℓ is
reducible, substitution in its proper factors again makes R_ℓ reducible.
This proves the necessity of the primitive-root condition.

For sufficiency let d=ℓ−1 and K=F₂(α), a field of 2^d elements.
For T(z)=z+z²+...+z^(2^(d−1)), we have T(z)²=T(z); so T maps K into F₂.
It is F₂-linear and nonzero, since its defining nonzero polynomial has
degree 2^(d−1)<|K| and cannot vanish at all elements of K. Thus its kernel
has size |K|/2. The map A(z)=z²+z is F₂-linear with kernel {0,1},
and T(A(z))=0 by telescoping. Its image also has size |K|/2, proving
im A=ker T without relying on an external trace-solvability theorem.

The orbit of α consists of all nonidentity ℓth roots. Hence
T(α)=sum_(i=1)^(ℓ−1) α^i=1. Also T(1)=d mod 2=0, because ℓ is odd.
It follows that T(α+1)=1, and z²+z=α+1 has no solution in K.
Consequently z²+z+1+α is irreducible over K. Let β be a root.
Then P(β)=α, so K⊂F₂(β). The tower formula gives
[F₂(β):F₂]=[K(β):K][K:F₂]=2d.
But R_ℓ(β)=H_ℓ(α)=0 and deg R_ℓ=2d. The monic polynomial R_ℓ is
therefore the minimal polynomial of β and is irreducible. This covers
every allowed u, including ℓ=3.

## Second mechanism: direct Frobenius dynamics

This gives a direct root-orbit certificate rather than invoking the quadratic
image criterion. Let d=ℓ−1, α primitive, β²+β=α+1. Iterating squaring gives

β^(2^d)+β = sum_(j=0)^(d−1)(α^(2^j)+1)=1.

Thus the dth Frobenius power interchanges β and β+1, and the 2dth fixes β.
If the Frobenius period m of β were smaller, then α=P(β) would have period
dividing m, so d|m. Since m|2d, only d or 2d are possible; the displayed
identity excludes d. Thus β has degree 2d, proving irreducibility again.
Both mechanisms share the cyclotomic orbit computation; they are not claimed
to be independent discoveries or two separate outcomes.

## Strongest subsumption and eligibility objection

This is precisely the classical cyclotomic irreducibility plus quadratic
Artin–Schreier/trace bridge (equivalently the degree-two case of composition
irreducibility). It is short because its mechanism is classical, not because
parameter quantifiers were dropped. It supplies the source claim completely,
but should receive **zero substantive discovery credit** under the campaign's
routine-corollary exclusion. No claim of first public proof is made.

The actual same-object 2021 body, arXiv:2106.10008v1, Theorem 1.1 and
Conjecture 1.2, treats non-Mersenne factors of Φ_p(M) for general Mersenne
primes with exceptional sets; its proof explicitly excludes M=1+x+x² in
Lemma 2.3(ii). It does not by itself clear priority for this special composition.
The actual October 2026 arXiv:2606.08640v3 body instead studies special
odd perfect polynomials and retains that existence issue. Neither an abstract
nor that different issue is used as evidence that our irreducibility bridge is new.
Current public proof-registry clearance is unavailable within inherited denied
routes, which were not retried. No eligible candidate is nominated.
