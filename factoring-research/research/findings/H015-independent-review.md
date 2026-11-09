**H015 independent review — 2026-10-08**

**Disposition: accept both derivations with the explicit thresholds, rounding,
and scope below.** The fixed-family count and the distinct-cofactor-band count
are valid conditional representation bounds. They reject polynomially many
fixed families, and polynomially many short literal-exponent runs, at the stated
parameters. They do not reject every faster batching algorithm. **Verified
factoring complexity improvement: NONE.** No novelty claim or Lean theorem.

Read the five required project instructions, research/STATE.md, the complete
W001-deterministic report (including Cards A/B and shared costs), both requested
H012 reports, H015.md, and both H015 derivations. Also inspected the H012 source's
grid and ceiling definitions and the cited Bostan–Schost paper. This is proof
review only: no finite experiment, script execution, or parameter sweep was
needed. Only this review and its [input-hash record](H015-review-input-sha256.txt)
were written.
H012's proposed full-range obstruction remains under separate review; it is
neither accepted nor used here. H014 is independent.

**Quantifiers and coefficient bounds.** Fix C>0 independently of N,m. Let N,m
be positive integers, gcd(N,m)=1, 0<=H<=C*sqrt(N*m), and let the common real cell
be [P,2P], with sqrt(N)/4<=P<=sqrt(N)/2. For every unit residue j modulo m,
suppose a selected integer triple (u,v,t), with (u,t)!=(0,0), satisfies both
congruences

    v+2u*j = 0 modulo m,
    N*t+u*j²+v*j = 0 modulo m²,

and |F(z)|<=H for every real z in that cell, where
F(z)=u*z+v+N*t/z. All conclusions hold for **every** such selection, without
restricting the certificate generator. Existence of this selection is an
assumption, not a conclusion about a lattice algorithm or actual factors.
Here phi is Euler's totient and omega counts distinct prime divisors.

The exact identities are

    F(P)-3F(3P/2)+2F(2P) = u*P/2,
    F(P)-2F(3P/2)+F(2P) = N*t/(6P).

The sums of absolute weights are 6 and 4. Thus

    |u| <= 12H/P <= U := 48C*sqrt(m),
    |t| <= 24H*P/N <= T := 12C*sqrt(m).

The congruences imply u*j²=N*t modulo m. Since N,j are units, u=0 forces
m|t, and t=0 forces m|u. Accordingly m>(12C)² suffices to exclude u=0;
**m>(48C)²** suffices to exclude both axes. These are strict thresholds:
equality only gives a coefficient bound <=m and does not exclude a nonzero
multiple of m. All later claims may use the latter threshold. Integer
coefficient counts use floors of U,T. Negative u,t,v cause no sign exception.

**First derivation: fixed-family capacity.** For a fixed key (u,t,r), where
r=v mod m², the first congruence requires 2u*j=-r modulo m. Its solution
count modulo m is either zero or gcd(2u,m); requiring unit j and the second
congruence can only reduce it. For u!=0,

    capacity <= gcd(2u,m) <= 2|u| <= 96C*sqrt(m).

If f is the number of represented keys, then

    f >= ceil(phi(m)/(96C*sqrt(m))).

This proves exactly the parent family bound. For any unit alpha modulo N,
v=r+m²*k gives alpha^(u+v+N*t)=alpha^(u+r+N*t)*gamma^k modulo N, with
gamma=alpha^(m²); inverse powers handle negative k or exponents. A key supplies
one containing progression, not necessarily one occupied consecutive block.
Sparse k can require extra blocks or padding. Conversely different keys can
merge into one block: f is **not** a lower bound on arbitrary block counts or
distinct modular values. The hypothesis file's phrase that sparsity cannot
reduce the lower count must be read as a count of keys only.

**Extension: capacity of one signed integer t.** Assume m>(48C)². Fix an
occurring t!=0 and put g=gcd(|t|,m), q=m/g. The congruence and the unit
conditions imply

    gcd(u,m)=gcd(t,m)=g.

There are at most 2*floor(U/g) possible nonzero multiples u of g, including
both signs. For each eligible u, division of the congruence by g gives

    (u/g)*j² = N*(t/g) modulo q.

Both coefficients are units modulo q: gcd(u/g,q)=gcd(t/g,q)=1. Hence this
is a unit square-root problem, despite u,t possibly being nonprimitive
modulo m. This division is valid for negative t as well.

For an odd prime power p^a, compare a fixed root y with any other root x.
The divisibility p^a|(x-y)(x+y), and the fact that p cannot divide both
factors for unit x,y, imply x=+/-y modulo p^a: at most two roots. Modulo
2 and 4 the bounds are one and two. For 2^a with a>=3, odd x,y have
min(v_2(x-y),v_2(x+y))=1 (with the usual convention for a zero factor).
Thus x=+/-y modulo 2^(a-1); these two classes have at most four lifts
modulo 2^a. CRT therefore bounds roots modulo q by

    R_m := 2^(omega(m)+1).

For q=1 the sole residue also satisfies this bound, although q=1 cannot
occur once 0<|t|<m. Each root modulo q has exactly g residue lifts modulo m,
of which at most g are units. Taking a union over u proves the finite bound

    capacity(t) <= min(phi(m), 2*floor(U/g)*g*R_m)
                <= 2U*R_m.

Ignoring v and overlapping solution sets only enlarges this upper bound.
Consequently the number d of distinct **signed integer** t values satisfies

    d >= D0 := ceil(phi(m)/(96C*sqrt(m)*R_m)).

No averaging of square residues, squarefreeness, or factorization of N is
used. The bound holds for arbitrary m, including smooth prime powers and
nonprimitive pairs. Since a product of k distinct primes is at least k!,
omega(m)=o(log m); also phi(m)>=m/2^omega(m). The displayed real lower
bound is m^(1/2-o(1)) as m grows with C fixed. Write **d>=m^(1/2-o(1))**,
not an equality for d. A complete selection additionally has d<=2*floor(T).

**Bands and the exact run-length boundary.** At P, the sharper bounds give

    |v| <= H+|u|P+N|t|/P <= 37H.

If P>=1, then |u|<=12H, and each actual integer exponent E=u+v+N*t lies
in the closed band I_t=[N*t-49H,N*t+49H]. The constants 37 and 49 are
valid upper bounds, without a claim of optimality. P>=1 is an additional
condition; N>=16 suffices under the prescribed P range.

For t1!=t2, the distance between these bands is at least

    N*|t1-t2|-98H >= delta := N-98H.

Assume H<=N/196, so delta>=N/2>0, including equality at the endpoint.
Different t then force different actual exponents. This does not imply
different modular powers of alpha.

Consider any finite collection of nonempty runs

    R_a = {b_a+h*m² : h integer, 0<=h<L_a},
    b_a integer, L_a positive integer,

whose union contains all selected **actual exponents**, with equality in Z.
Let R be its number of runs and S=sum_a L_a its total represented length,
counting all padding and repeated positions. A run containing exponents from
two distinct bands must satisfy

    (L_a-1)*m² >= delta,
    L_a >= B := 1+ceil((N-98H)/m²)
             >= 1+ceil(N/(2m²)).

Therefore

    S < B  implies  R >= d >= D0;
    in particular, R < D0 implies S >= B.

This is the exact rounded cutoff furnished by this proof, not a sufficiency
claim for merging at S=B: exponent congruences modulo m² can prevent it
altogether. The parent's S<N/(2m²) condition is correct but unnecessarily
restrictive. It also suffices that every individual L_a<B, regardless of S.
To see the count, assign one covered exponent to each occurring t; without
a run meeting two bands, no run can cover two of these representatives.
This argument permits arbitrary merging of u,v families inside each band.

At m=N^(1/5+o(1)) and fixed C, H/N<=C*sqrt(m/N) tends to zero, so the
extra conditions hold eventually. One has D0>=N^(1/10-o(1)) and
B=N^(3/5+o(1)); in particular B>=N^(3/5-o(1)). Thus polynomially many
runs in n=bit_length(N) require a long represented run at this latter scale.
The alternative of at least D0 short runs is exponential in n, but can still
be much smaller than the N^(1/5+o(1)) giant-list scale. These facts alone do
not imply that an improved total factoring cost is impossible.

**Application boundaries and rounding.** In H012, put
x=sqrt(N/m³), K=16*ceil(x), H=K*m². If m³<=N, then x>=1 and
H<=32*sqrt(N*m), so C=32 is a valid fixed choice. The source's modulus
satisfies m<=N^(1/5), hence this condition holds. For general larger m,
the ceiling term 16m² cannot silently be absorbed into the same constant.

The source grid starts at A=ceil(N^(1/3)), doubles, and ends at
floor(sqrt(N)). Whenever A<=sqrt(N)/2 (for example N>=4096 suffices),
take the first grid start P>=sqrt(N)/4. It satisfies P<=sqrt(N)/2:
either P=A, or its predecessor is below sqrt(N)/4. Since 2P is an integer
<=sqrt(N), that cell ends at exactly 2P without clipping. Thus the exact
balanced-cell assumptions can be met without changing constants. Endpoint
and midpoint evaluations concern real coverage; 3P/2 need not be integral.
The frozen 16 sampled residues per input do not constitute the required
all-unit selection. These observations apply a conditional theorem; they
do not extrapolate the finite screen to universal existence of covers.

**Cost interpretation and the surviving escape condition.**
[Bostan–Schost](https://mathexp.eu/bostan/publications/BoSc05.pdf), Section 1,
Table 1 and Section 5, explicitly state field-operation bounds; Propositions
3–5 concern distinct geometric points, and their displayed formulas include
inverses. They provide background, not a bit-cost theorem over Z/NZ.
Any imported routine must justify its particular inverses/unit and order
conditions over that ring. Distinct residues alone do not make their
differences units; a failed inverse needs valid factor extraction or other
handling, including the gcd=N case. The elementary counts above use none
of those algorithms.

Likewise a conventional O(M(G)*log L) upper bound cannot be reversed into
a lower bound. At m=N^(1/5+o(1)), counting these keys as L gives
log L=Omega(n) (and Theta(n) if L<=m*poly(n)); this defeats only that proposed
substitution into that formula. Neither report proves a general product-tree,
multipoint-evaluation, arithmetic-circuit, or factoring lower bound.

The precise remaining requirement is a uniformly correct, fully costed
primitive that handles this obligated exponent set. To retain polynomially
many runs of small total represented length, it must change a named premise:
use and justify modular-order identifications instead of literal exponents;
use other strides/bases or a sparse/implicit representation that does not
process the padded span; or avoid the all-unit common-whole-cell obligation
with a proved coverage/search rule (or change the fixed-slack parameters and
rebalance all costs). Merely dropping u from the family key or merging v
families cannot evade the distinct-t argument. An algorithm may instead
**accept the many short runs and process them collectively faster**; that too
remains open and does not contradict the theorem. In every case construction,
metadata, recovery, preprocessing, ring arithmetic, and the shared collision
costs still need payment. No order oracle or free sparse evaluator is supplied.

Next decisive work, if this batching route is pursued, is such a concrete
primitive and its cost proof. More same-family samples cannot change these
conditional counts, and neither H012's separate obstruction nor H014's
enumerator is needed for this disposition.
