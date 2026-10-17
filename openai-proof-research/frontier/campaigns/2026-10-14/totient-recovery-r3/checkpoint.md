# Recovery checkpoint: exact support problem and a construction boundary

Myeongjin Kang; no affiliation. Original prose CC BY 4.0, code MIT.

**UNRESOLVED full target.** No substantial theorem nominated. The unchanged
claim in scope.md is not proved or refuted. This recovery did real finite
support calculations and proved a general limitation of the proposed fixed
smooth-support exponent construction. These are supporting observations,
not substitutes for the target and not a sixth campaign result.

## 1. Exact inverse-support formulation

Write d=product(q in S) q^b_q, where S is its prime support and b_q>0.
Let P(d)={p prime : p−1 divides d}. This finite list is obtained by testing
u+1 for every positive divisor u of d. For p in P(d), the possible positive
exponents in a preimage are 1<=e<=1+v_p(d), taking v_p(d)=0 when p is not
in S. Define the nonnegative integer column

    A(q;p,e)=v_q(p−1)+(e−1)1[q=p].

A complete inverse fiber is EXACTLY the family of selections x_(p,e) in
{0,1}, with sum_e x_(p,e)<=1 for each p, and

    sum_(p,e) A(q;p,e)x_(p,e)=b_q  for every q in S.

The corresponding preimage is n=product_(p,e) p^(e*x_(p,e)). Indeed
phi(p^e)=(p−1)p^(e−1), so every selection satisfying these equations has
phi(n)=d. Conversely unique prime factorization of an arbitrary preimage
gives this selection: p−1 divides d and p^(e−1) divides d. There are no
unrecorded prime coordinates because p−1|d. The conventions cover d=1:
S is empty, P={2}, the empty selection gives n=1, and selecting (2,1)
gives n=2. In particular prime 2 and all permitted prime powers are included.

The objective log(n/d) is exactly

    sum_(p,e) x_(p,e) log(p/(p−1)).

A sufficient certificate for ell(d)/d>=L consists of positive rational
numbers C_q (not necessarily >=1) such that, for EVERY allowed (p,e),

    product_q C_q^A(q;p,e) <= p/(p−1),
    product_q C_q^b_q >= L.

Multiplying the first inequalities over any feasible selection proves the
conclusion. All tests can be exact rational tests. This is a sufficient
linear-dual-style certificate after taking logarithms, not a theorem that
such certificates exist with unbounded L. Omitting columns, even ones
corresponding to unexpected large primes, invalidates this lower bound.

## 2. Fixed smooth support cannot work, regardless of exponents

For any d=phi(n),

    log(n/d)
      = sum_(p|n) log(1+1/(p−1))
      <= sum_(p|n) 1/(p−1)
      <= sum_(u|d) 1/u
      = product_(q|d) (1+1/q+...+1/q^b_q)
      <= product_(q|d) (1−1/q)^(-1) = d/phi(d).

The penultimate inequality uses the injective map p -> p−1 from the prime
support of n into the divisors of d; no primality heuristic occurs. The
identity for n/d also holds for n=1 by the empty-product convention.
Consequently, if every prime divisor of d lies in a FIXED finite set S,
then EVERY preimage has

    n/d <= exp(product_(q in S) q/(q−1)).

Thus exponent boxes over a fixed S, however large or cleverly selected,
cannot prove the target. The same conclusion holds uniformly over supports
S in any class for which sum_(q in S)1/q is bounded: since
-log(1−1/q)<=2/q for primes q, the displayed product is uniformly bounded.
A successful construction must therefore allow the reciprocal-prime mass
of the support of d to grow without bound. This is necessary, not sufficient.
It does not refute the growing-S operation proposed by the previous worker.

## 3. Complete finite fibers and actual failures of naive seeds

inverse_support.py recursively chooses the largest prime p of a preimage,
then its exponent e, and recurses on d/phi(p^e) with strictly smaller allowed
primes. Therefore every branch has distinct prime factors, all fibers are
complete, and no choice of a single favored preimage is mistaken for a
minimum. The zero-cost phi(2)=1 branch terminates because the prime bound
strictly decreases. Memoization changes only running time.

The implementation was checked against an independent direct phi table for
EVERY 1<=d<=150, enumerating 1<=n<=45000. This is a rigorous finite range
for the comparison: phi(n)^2/n is the product of
p^(e−2)(p−1)^2, at least1 for every odd prime power, and at least1/2 for the
2-primary factor. Hence n<=2*phi(n)^2, so no omitted preimage of these d
can lie above45000. All150 comparisons passed.

The experiment then searched129 distinct d (125 totients): the box
2^a3^b5^c with 1<=a<=8, 0<=b<=4, 0<=c<=2; five Ford examples; and phi(P^e)
where P is the product of the first k primes, 2<=k<=7 and e=1,2.
Primality inputs are below2^64; SymPy uses its deterministic test in that
range. No floating-point comparison determines an ordering or result.
The JSON stores exact rational ratios. Among this finite set the largest
least ratio is Ford's existing example d=2^18*257=67371008:

    ell(d)=135268352, ell(d)/d=257/128, fiber size8.

This is a reproduction, not a new record. Ford's d=54,12500,294,110 have
least preimages81,15625,343,121, respectively.

Growing the support by taking primorial powers does not itself force it
into every inverse. For P=2*3*5*7*11*13=30030 and d=phi(P^2)=172972800,
the exact search finds d+1=172972801 prime, so ell(d)=d+1. There are19133
preimages in the complete fiber. The intended P^2 preimage has ratio
P/phi(P)=1001/192, while the least ratio is172972801/172972800. Thus a
large ratio for the canonical support is emphatically insufficient.
For P through17 and e=2 the complete fiber has338304 members and least
ratio47049036403/47048601600, again close to1. These are finite failures,
not a theorem excluding all primorial-power choices.

Reproduce with a Python environment containing SymPy:

    python inverse_support.py

An existing /tmp/sympy-venv/bin/python was used. The system Python lacked
SymPy. An initial larger exploratory run was interrupted to keep the finite
search bounded; no results from it are claimed. experiment.json is from the
completed stated search; verbose primorial fibers were omitted from the JSON
while preserving their exact sizes, minima, and common divisors.

## 4. Source leverage and what is still unpaid

The pinned family024 statements.tex and companion.tex explicitly leave
unbounded ell(d)/d unresolved. The companion's weighted asymptotic has a
positive coefficient for k EXACTLY WHEN a seed with ell(d)>kd exists.
It supplies no new seed. Its ratio-tightness assertion is consistent with
unbounded ratios on exceptional values.

The actual primary Ford proof, Section5 pp24–26 equations(5.10)–(5.19),
constructs b=p0...pL with pL>=max(d+2,17) and eliminates nontrivial fibers.
Section7.3 p39 records complete-fiber propagation and the examples used
above. It expressly says common divisibility by6 might never occur; one
cannot assume arbitrary common small-prime divisibility follows from it.
The parent's exact propagation objection remains: the gain is b/phi(b),
with no uniform factor>1 supplied, and gcd(b,u)=1 for every seed preimage u.

The missing constructive operation is now precise: find growing finite
supports and exponent vectors for which EVERY exact cover in Section1 has
unbounded objective, while at least one cover exists. No argument here
produces those vectors, and the source's existence/density propagation
cannot be substituted for that step. The rational certificate is a tool to
verify a future construction, not evidence that it exists. No independent
proof or contribution gate is requested for the full target at this point.

## Final disposition

There is no concrete growing-support construction surviving this attempt.
The exact-cover optimizer and rational certificate specify a verification
problem, not a mechanism generating solvable instances with divergent
minimum objective. The tested primorial-power choice supplies no such
mechanism, and fixed-support exponent growth is rigorously bounded above.
Accordingly further generic optimization or larger finite boxes is not
justified as progress toward the full theorem. Preserve the full target
as unresolved; no counterexample to it and no substantial acceptance.
