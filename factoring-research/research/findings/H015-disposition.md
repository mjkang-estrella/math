# H015 — Simple literal-exponent batching premise closed

2026-10-08. The independent review accepts both derivations with explicit
thresholds and rounding. Verified factoring complexity improvement: **NONE**.

Assume a nontrivial reciprocal certificate for every unit residue, covering
one common whole real cell [P,2P] at sqrt(N)/4<=P<=sqrt(N)/2, with
H<=C*sqrt(N*m), C fixed. For m>(48C)^2, the fixed family key
(u,t,v mod m^2) covers at most 96C*sqrt(m) residues. The number of such
keys is at least ceil(phi(m)/(96C*sqrt(m))). This counts keys, not all possible
merged geometric blocks.

The stronger derivation permits merging different u,v. Put
R_m=2^(omega(m)+1) and D0=ceil(phi(m)/(96C*sqrt(m)*R_m)). At least D0
distinct signed t values occur. For P>=1 and H<=N/196 their actual integer
exponents lie in separated bands [Nt-49H,Nt+49H]. Any run of stride m^2
meeting two bands requires at least

    B = 1 + ceil((N-98H)/m^2)

represented positions. If the total represented length is below B, at least
D0 runs are needed. This sharpens the parent's sufficient cutoff; it does
not assert that merging becomes possible at equality. At m=N^(1/5+o(1)),
D0>=N^(1/10-o(1)) and B=N^(3/5+o(1)). The review checks that a qualifying
whole cell occurs in H012's actual grid for sufficiently large inputs.

The coordinator checked the nonprimitive gcd division, unit quadratic roots
modulo prime powers, lifting counts, negative coefficients, and band argument.
The estimates are conditional representation bounds, not bit-runtime lower
bounds. Distinct actual exponents may give equal modular powers. A conventional
multipoint upper-cost expression cannot be reversed to prove a lower bound.

Close polynomially many short literal-exponent runs at this stride as the
proposed automatic batching repair. Other strides, justified modular-order
identifications, sparse or implicit evaluation, changed coverage obligations,
and faster collective processing of the many short runs remain open. Any new
primitive must pay for finding its structure and recovering factors. The field
operation bounds of Bostan–Schost are not a free oracle over Z/NZ.

[Independent review](H015-independent-review.md),
[family derivation](H015-geometric-family-bound.md),
[short-run derivation](H015-short-block-extension.md). Input hashes match;
this was a proof review, not a new experiment or a Lean theorem.
research/tasks-H015.json is complete.
