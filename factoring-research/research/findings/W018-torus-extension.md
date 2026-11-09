# W018 follow-through: powered norm-one bases

Parent derivation, 2026-10-08. Provisional; not in the original W018 audit brief.
Verified complete factoring improvement: NONE. This supplies an explicit
randomized operation for a torus-order obligation identified by the W014 C
review, rather than assigning an ordinary unit routine to a different group.

## Semiprime primitive

Assume N=p*q for distinct odd primes (analysis scope), a public unit d with
Jacobi(d,N)=-1, a positive binary M and B>=1. Work in
R=(Z/NZ)[t]/(t^2-d). Exactly one prime is inert; label it p. The norm-one
groups modulo p and q are cyclic of orders p+1 and q-1 respectively.

Sample a uniformly modulo N and check gcd(a^2-d,N). A nonunit is a proper
factor, since a^2=d is impossible at the inert prime. Otherwise set

    z=(a+t)/(a-t),       beta=z^M.

Use the same bounded-order BSGS as W018 on pairs of residues. If ord(beta)>B,
return z,beta. Otherwise obtain r=ord(beta), so z^(M*r)=1, and run the
annihilator squaring chain. For a chain element x+y*t, test gcd(x-1,N).
When the local 2-adic orders differ, one chain stage has scalar component 1
at one prime and -1 at the other. Its gcd is a proper factor. No root of d
modulo a hidden prime is constructed.

All pair operations use a constant number of modular operations; inverse of a
norm-one element is its conjugate. The initial inverse uses the already checked
unit a^2-d. Thus one trial has the same proposed bit-cost scale as W018,
O~((bitlen(M)+sqrt(B)+1)*poly(log N)).

## Exact sampling and success bound

Conditioned on the denominator being a unit, CRT makes the two a-components
independent and uniform on their allowed local domains. The Cayley map is
bijective onto the corresponding cyclic norm-one group with its identity
removed. At the split prime the two forbidden poles remove w=0 and the
point at infinity; the image is F_q^* minus {1}. In particular -1 remains
attainable at a=0. At the inert prime the image is likewise the whole
order-(p+1) torus minus {1}.

For a cyclic group of even order h=2^s*u, u odd, uniform sampling excluding
the identity has 2-adic order probabilities

    Pr(v=0)=(u-1)/(h-1),
    Pr(v=j)=2^(j-1)*u/(h-1), 1<=j<=s.

For h>=4 every atom is at most 2/3: the largest positive-j atom is
h/(2*(h-1))<=2/3, and the zero atom is smaller than 1/2. At least one
component has h>=4 (the inert component always does). Independence therefore
gives Pr(v_p=v_q)<=2/3 even if the other group has order two. If the powered
order search returns small order, unequal valuations guarantee extraction;
if it returns large order, the trial already succeeded. Failure probability
is at most 2/3, without conditioning the valuation law on small order.
Nonunit denominators succeed immediately. Expected trials are at most three.

Do not silently change the sampler by conditioning additionally on gcd(a,N)=1:
that removes -1 in each component and changes this probability proof. A check
which immediately returns a proper factor is harmless only with its success
probability accounted for; the algorithm above needs no such extra condition.
Uniform d sampling with gcd/Jacobi checks supplies a suitable d in expected
constant trials for this semiprime scope, or returns a factor.

## A concrete use in a two-dimensional collision table

Let g=(u,z), h=(u,z^(-1)), and a rational line slope produce
g'=g^b*h^a with integer b>0. A baby indexed by 0<=j<H1 and 0<=e<B0 is

    g'^j*h^e = (u^((b+a)*j+e), z^((b-a)*j-e)).

If the GLOBAL orders of u and z exceed respectively

    |b+a|*(H1-1)+(B0-1),
    |b-a|*(H1-1)+(B0-1),

then equality of two babies forces both integer exponent differences to be
zero. Adding them gives 2b*(j-j')=0, hence j=j' and e=e'. This is a paid
injectivity condition, not a presumption of independence between generators.
Ordinary W018 preparation (M=1) and this torus routine (M=1) provide the two
orders or a factor at square-root cost in these thresholds. Charge those
thresholds, the H1*B0 entries, giants and all verification explicitly.

This repairs a possible randomized implementation obligation for the specified
table. It does not show that such a table beats a one-coordinate sum search,
or that any W014 exponent improves. Arbitrary composites and other torus
sampling laws require their own proof; this note asserts only distinct odd
semiprimes with the stated Jacobi sign.
