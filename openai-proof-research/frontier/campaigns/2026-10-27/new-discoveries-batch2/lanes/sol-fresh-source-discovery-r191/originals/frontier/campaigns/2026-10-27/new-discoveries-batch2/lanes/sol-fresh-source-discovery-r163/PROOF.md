# Complete classical bridge — uncredited

Research date: 2026-10-30 UTC. This is an ordinary proof of the full source
Conjecture, not a discovery nomination or an independently reviewed certificate.

## Exact statement

Let R be any commutative integral domain with identity. Let n>1 be an integer,
and c0,...,cn in R. Let ω be a Dumas valuation in the literal sense of
Širola, arXiv:2402.14163v2, Definition1.2 with Γ=N0 (not an arbitrary Γ).
Thus ω is additive on products, finite and nonnegative integer valued on
nonzero elements, zero exactly at the appropriate infinity, and has the max
triangle inequality for the first kind, min triangle inequality for the second
kind, with equality on unequal values. Assume ω(cn)=0, m=ω(c0)>0,
gcd(n,m)=1. For 0<j<n assume nω(cj)≤(n−j)m in the first kind, or
nω(cj)≥(n−j)m in the second kind, interpreting zero with its stated infinity.
Then f=Σ cj X^j has no factorization gh in R[X] with deg g,deg h>0.
There is no restriction on n, characteristic, Noetherianity, UFD property,
normality, or number of variables in R. This is the introduction's entire
Conjecture, including both kinds, extending its Theorem0.1's degree bounds.
No assertion about irreducibility as an element (constant nonunits) is needed.

## Signed valuation and weighted extremal indices

On nonzero elements put v=−ω for the first kind, v=ω for the second kind,
and v(0)=+∞. In both cases v(ab)=v(a)+v(b), v(a+b)≥min(v(a),v(b)),
with equality for distinct finite values. All finite values are integers.
The first kind is allowed to take negative values; one must not assume R
lies in its valuation ring. Put a=v(c0), which equals −m or m respectively.
Both source inequalities become n v(cj)≥(n−j)a. Also v(cn)=0.

For any nonzero polynomial P=Σ pi X^i and λ=a/n in Q, define
W(P)=min_i(v(pi)+iλ), ignoring zero coefficients. Let l(P),r(P) be the
smallest and largest indices attaining this minimum. They exist since the
support is finite.

For nonzero P,Q one has

    W(PQ)=W(P)+W(Q),
    l(PQ)=l(P)+l(Q),   r(PQ)=r(P)+r(Q).                 (*)

Here is a proof with cancellation accounted for. Every contribution pi qj to
the coefficient of degree k=i+j has weighted value at least W(P)+W(Q).
For k=l(P)+l(Q), exactly one contribution can attain this bound: i=l(P),
j=l(Q). If another pair of minimizers had this sum, one index would be
smaller than its smallest minimizer. All other contributions have strictly
larger weighted value, and at fixed k that is a strict inequality of ordinary
v-values. Repeated application of the unequal-value rule makes the sum have
the unique smallest contribution's value. At degrees below k, every term
has strictly larger weighted value. A finite sum of such terms also does,
by the min inequality. This proves W and l. Using the largest minimizers
instead proves r by exactly the same argument with degrees above their sum.
Zeros and empty convolution sums have value +∞, so do not affect the proof.
The unique extremal product is nonzero because R is a domain.

For f, the source inequalities give W(f)=a, with indices 0 and n attaining
it; in fact no interior index can tie, since equality would give
n v(cj)=(n−j)a, forcing n|j by gcd(n,a)=1. Thus l(f)=0,r(f)=n.

If f=gh with degrees s,t>0, then s+t=n in a domain. Formula(*) gives
l(g)+l(h)=0, so l(g)=l(h)=0. Also r(g)+r(h)=n=s+t, while r(g)≤s,
r(h)≤t, so r(g)=s,r(h)=t. Consequently the constant and leading
coefficients of g both attain W(g), and

    v(g0)=v(gs)+s a/n.

All finite v-values are integers, hence n|s a and therefore n|s. This
contradicts 0<s<n. This proves the entire source statement for both kinds.

## Complete bridge to an actual earlier theorem

This mechanism is the classical single-segment Newton-polygon argument.
To substantiate subsumption rather than declaring the proof 'short', apply
El Fadil, Tatra Mt.Math.Publ.83(2023),51–60, Theorem3.1 (p55), whose proof
on p56 was read. Take its key polynomial φ=X and gcd(height,n)=1.
The following checks supply every domain and sign bridge.

For K=Frac(R), extend v by v(b/c)=v(b)−v(c). This is well-defined because
b/c=b'/c' gives bc'=b'c and equal values by multiplicativity. The min rule
follows after taking common denominators, and multiplicativity is immediate.
The value group is a nonzero subgroup dZ of Z, since m>0. Replace v by
v/d, obtaining a surjective rank-one discrete valuation. Since d|m and
gcd(n,m)=1, gcd(n,m/d)=1. No Gauss lemma over R is used.

Second kind: P=f/cn is monic in K[X], v(P0)=m, and its other nonleading
coefficients have v(Pj)≥(n−j)m/n>0 when nonzero. Thus P belongs to
the valuation ring, reduces to X^n, and meets Theorem3.1 with height m/d.
It is irreducible even over the henselization, hence over K.

First kind: v(c0)=−m. Use instead the monic reciprocal
P=X^n f(1/X)/c0. Its coefficient at degree k is c_(n−k)/c0 and

    n v(Pk) ≥ (n−k)m  (0≤k<n),   v(Pn)=0.

Indeed n v(c_(n−k))≥k(−m), and subtracting n v(c0)=−nm gives the
displayed inequality. Its constant has value m. The same valuation-ring,
reduction and gcd checks now apply. Since c0 and cn are nonzero, a
positive-degree factorization of f over K reverses into positive-degree
factors of P: the factors have nonzero constant terms, so reversal preserves
their degrees. Thus irreducibility of P gives the required conclusion.
Finally a factorization in R[X] would remain one in K[X], with unchanged
positive degrees. This implication does not require R to be integrally closed,
a UFD, or a maximal order. This completes the classical exclusion bridge.

Garg–Singh arXiv:2511.21427v2 (12 June2026), Theorem1 with j=n,k=0,
also states a sufficient field theorem without valuation-ring restrictions.
Its actual weighted-valuation proof was read. It is a later companion to
the 2024 source but earlier than this lane; the 2023 theorem already suffices.
No assertion is made that either author explicitly resolved Širola by name.

## Strongest objections and falsifiers

* Arbitrary non-UFD domains: fraction-field extension is explicitly proved;
  descent only uses the easy direction R[X]→K[X], never converse Gauss.
* Negative first-kind values: the direct proof permits them; the published
  theorem comparison uses the explicit reciprocal to restore positive height.
* Cancellation: one extremal product is unique at each extreme; other
  tied products can cancel elsewhere without changing either extreme.
* General Γ-valuations: not claimed. For Γ=(1/2)N0, ω=deg_t/2,
  X²−t² has ω(c0)=1 coprime to2 but factors. The source Conjecture
  is specifically Γ=N0; Remark1.3's proposed extension needs a group-relative
  primitivity condition. This is a scope control, not a source refutation.
* Coprimality is essential: X⁴−t²=(X²−t)(X²+t), with height2.

Ordinary mathematics is complete, but eligibility is not cleared: the full
argument is a classical theorem plus the explicit bridges above. Proposed
disposition: exclude from discovery credit, subject to root's review. No
Lean, manuscript or independent-review PASS is claimed.
