# W001 — deterministic factoring: coverage and collision costs

Date: 2026-10-07 America/Los_Angeles. Bounded independent ideation pass.

**Verified improvement: NONE.** Evidence level: ideas plus algebraic cost screens; no implementation benchmark or new theorem. Read the project instructions, specification, and checkpoint; did not adopt H002 or inspect other researchers' proposals. Only this report was written. No harness, Lean, STATE, or infrastructure changes.

The most worthwhile remaining question in this pass is whether **the same useful quadratic certificate can cover several factor-size intervals**, reducing the number of giant steps. The other three cards expose concrete costs or correctness failures that prevent their advertised gains. None supports polynomial-time classical factoring.

## Baseline and literature checked

Throughout, `n = bit_length(N)`, `ell = max(1, log n)`, and `M(b)` is the bit cost of multiplying b-bit integers. Thus `N^a = 2^(a n + O(1))`. Soft-O below suppresses polynomial factors in n only; explicit logarithmic comparisons do not use soft-O.

Primary sources opened and checked:

- **[Hittmeir, 2021](https://arxiv.org/abs/2006.16729)**, *A time-space tradeoff for Lehman's deterministic integer factorization method*: deterministic `N^(2/9+o(1))` factoring, using Lehman-type linear combinations and a time-space tradeoff.
- **[Harvey, 2021](https://arxiv.org/pdf/2010.05450)**, Theorem 1.1: `O(N^(1/5) n^(16/5))`. Relevant ingredients are a joint collision search, polynomial products, and evaluation at geometric points. Section 2 gives bit costs, and Section 4 handles collision extraction.
- **[Harvey–Hittmeir, 2022](https://arxiv.org/pdf/2105.11105)**, Theorem 1.1 and Remark 4.5: the general deterministic bound is `O(N^(1/5) n^(16/5)/ell^(3/5))`. The product/collision stage remains a bottleneck even with faster lattice reduction.
- **[Gao–Feng–Hu–Pan, 2025 preprint](https://arxiv.org/html/2512.19076v1)**, Theorem 1.1 and Algorithms 4.3, 4.6, 4.8: a stated bound `O(N^(1/5) n^(13/5)/ell^(3/5))` for balanced semiprimes. Its search also handles a *given* constant-ratio interval for the smaller factor. Enumerating unknown factor sizes reintroduces an overhead. It uses a useful second lattice vector. This is a scoped preprint result, not a new general bound established here.
- **[Umans–Wang, 2025 preprint](https://arxiv.org/html/2511.10851v1)**, Conjecture 5.1 and Theorem 5.5: structured, efficiently prefactored divisibility covers would give `N^(1/6+o(1))` at parameters `(1/3,1/3)`. Coverage, efficient construction/evaluation, and extraction from a difference are distinct obligations. Merely citing the conjecture supplies none of them.
- **[Harvey–Hittmeir, 2026](https://arxiv.org/html/2601.11131v1)**, Theorem 1.1: for any `1 <= D < N-1`, find a factor or an element of order greater than D in `O(sqrt(D) n^2/sqrt(log log max(D,3)))` bit operations. The former minimum-D restriction is gone. This does not supply an exact order oracle, nor guarantee that raising the element to an arbitrary stride preserves its order.

These searches found no checked unconditional general-input exponent below 1/5. This is a bounded literature check, not an exhaustive novelty or priority claim.

### Shared accounting for the collision cards

For a splitter, test small factors through `N^(1/3)` using a product/multipoint method, at a conservative cost `O(N^(1/6) n^3)`. If no factor is found, a promised composite is a semiprime; handle squares directly. The remaining smaller factor lies between `N^(1/3)` and `sqrt(N)`. This charges the reduction from arbitrary composites instead of silently assuming balanced RSA inputs.

Write m for a publicly constructed, factored smooth modulus, with `gcd(m,N)=1` and density `phi(m)/m = O(1/ell)`. A gcd failure is handled by its known prime factors. Let G be the number of retained giant steps and K the baby-step range. A conservative common search cost is

`O(G n^3 + K n^2)`,

including modular polynomial products, geometric evaluation, sorting, gcds, and extraction. A polynomial multiplication at degree d uses packed integers of `O(d(n+log d))` bits: it is not an n-bit constant-time operation. Keeping product-tree levels gives a safe memory bound `O((G+K)n log(G+K))` bits; memory writes are charged. Coefficients, exponents, and fixed-dimensional lattice entries have `O(n)` bits, apart from those packed polynomial operands.

For the large stride `gamma = alpha^(m^2)`, use the **charged** order preparation from Gao et al., Proposition 4.7: `O(N^(1/6)n^2/sqrt(ell) + sqrt(K)n^3)`, followed by the needed gcd checks. Do not substitute an order-K element and assume its m²-th power still has order K. Alternatively, demanding order `m^2 K` directly costs roughly `m sqrt(K)n^2`, which can spoil the exponent. This distinction matters for every proposed rebalancing below.

When an entire product has gcd N, descend or perform the appropriate collision recovery; it is not a factor. Exact equality modulo N must retain the certificate needed to reconstruct a factor. All cards are deterministic attempts: no unpriced random-success assumption or unlimited restart loop is allowed. A baseline fallback restores correctness but gives only the baseline worst-case bound.

## Card A — merge factor-size intervals using reciprocal-quadratic certificates

**Status: conditional survivor, first priority for falsification.** Proposed gain: one further `ell^(3/5)` factor for arbitrary composites. The required coverage compression is unsupported.

**Primitive.** For each unit residue j modulo m, generate the usual useful fixed-dimensional lattice certificates over dyadic factor-size intervals. Express each certificate as integers `(u,v,t)` satisfying

`v + 2uj = 0 (mod m)` and `Nt + uj^2 + vj = 0 (mod m^2)`.

Then

`g(x) = [u(mx+j)^2 + v(mx+j) + Nt]/m^2`

has integer coefficients. If `p | N`, `p = mx+j`, and `q=N/p`, its integer quotient is

`g(x)/p = (up + v + tq)/m^2 =: i`.

Reject `u=t=0`: that gives a constant quotient and no factor information. For any retained certificate, compute the maximal real intervals on which

`|uz + v + Nt/z| <= K m^2`.

The endpoints follow from two quadratic inequalities. Endpoint and stationary-point comparisons can be certified with integer arithmetic. Cover `[N^(1/3), sqrt(N)]` using these certified intervals, selecting intervals by the usual furthest-right-endpoint rule. Count disconnected components separately; allowing the same certificate twice changes the count by at most a constant. Generate a modular giant step only after selection.

The collision identity is exact:

`alpha^(u+v+Nt) = gamma^i (mod p)`, where `gamma=alpha^(m^2)`.

An exact match modulo N supplies i; solve

`u p^2 + (v-i m^2)p + Nt = 0`

and verify any integral factor. This is linear if u=0 and t is nonzero. Negative i are handled with a shifted signed baby range, a constant-factor cost. Partial modular matches use polynomial/gcd extraction.

**Distinction.** The lattice relation and collision identity are existing machinery. The proposed additional operation is *cross-interval reuse certified by the exact reciprocal envelope*, followed by an interval cover. It seeks fewer necessary certificates, rather than faster reduction of the same number of lattices. No novelty is claimed for interval covering or for the existing factoring identities. Closest factoring sources: [Harvey–Hittmeir](https://arxiv.org/pdf/2105.11105) and [Gao et al.](https://arxiv.org/html/2512.19076v1).

**Full conditional scaling.** Suppose the selected cover has at most C(n) certificates per residue, with `K = O(sqrt(N)/m^(3/2))`. Then `G = O(phi(m) C(n))`, and the dominant search cost is

`T = O(m C(n)n^3/ell + sqrt(N)n^2/m^(3/2))`.

Balancing gives

`m ~ N^(1/5) [ell/(C(n)n)]^(2/5)`

and

`T = O(2^(n/5) n^(13/5) [C(n)/ell]^(3/5))`.

The ordinary `C(n)=O(n)` recovers the general baseline. The concrete target `C(n)=O(n/ell)` would give

`O(2^(n/5) n^(16/5)/ell^(6/5))`.

This target includes the small-factor stage and the order preparation above, both asymptotically smaller. It requires uniform constants and a constructive smooth-m choice, not advice about the factor's size.

**Generation must also fit.** There are `O(phi(m)n)` original dyadic candidates. Producing these with a fixed-dimensional reduction routine costing `n^(2+o(1))` each costs `phi(m)n^(3+o(1))`, below the proposed dominant term. Quadratic lattice reduction is available in fixed dimension; see [Nguyen–Stehlé, *An LLL Algorithm with Quadratic Complexity*](https://epubs.siam.org/doi/10.1137/070705702). Sorting/certifying the interval endpoints and selecting the cover must fit the same budget. A cubic-per-candidate implementation can erase the logarithmic gain. Stream candidates residue by residue; selected certificates plus the final collision trees dominate memory.

**Why it may fail.** Let `R=Q/P`, `s=sqrt(R)`, and `H=K m^2`. If a certificate works throughout `[P,Q]`, evaluations at `P,sP,Q` imply the necessary bounds

`|u| <= 2H/[P(s-1)^2]`,

`|t| <= 2s^2 H P/[N(s-1)^2]`.

The pair also satisfies `u j^2 = Nt (mod m)`, an index-m lattice constraint. For large R, the rectangle of these necessary coefficient bounds has area/determinant on the order of `K^2 m^3/(NR)`, or `O(1/R)` at the proposed K, up to the fixed constant in K. Thus broad useful intervals are not supplied by a generic volume argument. The excluded constant-quotient line cannot be counted as coverage. This is a warning about this construction, not an impossibility theorem for factoring.

**Cheapest decisive falsifier.** First inspect that two-dimensional congruence lattice, not a factoring harness. An explicit infinite family forcing every nontrivial candidate certificate in this pool to cover only a bounded number of dyadic cells would refute the proposed `n/ell` compression. A finite uncovered interval refutes a specific claimed cover immediately. A finite low reuse ratio only rejects the sampled implementation's promise; it does not prove an asymptotic lower bound.

## Card B — reverse the product tree and build the geometric-root polynomial

**Status: rejected as a logarithmic improvement in this form.** Intended target: replace `G n^3 + K n^2` by `(G+K)n^2`, which would improve the general rebalanced bound to approximately `2^(n/5)n^(13/5)/ell^(3/5)`.

**Algorithm.** Instead of multiplying `(X-v_h)` over arbitrary giant steps, construct

`B(X) = product_{i=0}^{K-1}(X-gamma^i)`.

Its coefficients can be generated through Gaussian-binomial recurrences and batch inversion of `1-gamma^i`. A nonunit denominator must produce a checked factor or trigger proper order handling. Evaluate B at every giant step, gcd the values with N, and descend to a useful collision if necessary. Geometric-root products and geometric evaluation are established primitives; primary prior art is [Bostan–Schost, 2005](https://mathexp.eu/bostan/publications/BoSc05.pdf). The idea tested here is applying the opposite orientation to this particular asymmetric factoring search.

**Cost screen.** Fast construction of B does not make its evaluation at arbitrary `v_h` geometric. Building their point tree and doing remainder-tree evaluation costs

`O(M_N(K) + M_N(G) log G)`

for K at least G, where `M_N(d)=O(M(d(n+log d)))`. In the exponential parameter range this is again bounded by `O(Kn^2+Gn^3)`. List generation, gcds, sorting, extraction, and order preparation still apply. At the usual balance, `K/G` is of order n, so merely swapping the sizes is not a win. Safe memory is `O((G+K)n log(G+K))` bits. Any modular inversions are charged; there are no restarts or assumptions that the ring is a field.

**Decisive falsifier already obtained.** The missing logarithm reappears in the arbitrary-point tree. This does not rule out a better evaluation primitive exploiting *additional structure in the giant points*. Such a primitive is not supplied by reversing the existing algorithm. Compared with the correct known method, there is no proved total-cost reduction and no new coverage theorem.

## Card C — lift approximate-divisor certificates from p to p²

**Status: rejected as an exponent improvement in the specified form.** This is a different lattice mechanism from interval reuse: change the divisibility power and polynomial degree, hoping a smaller quotient will outweigh the larger lattice.

**Algorithm.** For a fixed j and public bound `X ~ P/m` on `(p-j)/m`, put `f(x)=x+j*m^(-1) mod N`. Use the rank-5 coefficient lattice generated by

`N^2, Nf, f^2, f^3, f^4`,

with coefficient k scaled by `X^k`. Every polynomial h in this lattice satisfies `p^2 | h((p-j)/m)`. Seek a short useful h, write its value as `i p^2`, and search for i using

`alpha^[m^4 h((1-j)/m)] = alpha^(i m^4) (mod p)`.

An exact collision leads to the degree-at-most-four equation `h(x)=i(mx+j)^2`; isolate integral roots and verify factors. Exclude an identically zero recovery equation. For partial collisions, use the same product/evaluation machinery. The general small-root lattice idea is due to [Coppersmith, 1997](https://research.ibm.com/publications/small-solutions-to-polynomial-equations-and-low-exponent-rsa-vulnerabilities); useful versus trivial relations are particularly relevant in [Gao et al.](https://arxiv.org/html/2512.19076v1).

**Complete optimistic cost test.** The determinant is `N^3 X^10`. Even granting an informative vector at the geometric-mean scale, in the balanced case `P ~ sqrt(N)` its quotient bound is

`K ~ (N^3 X^10)^(1/5)/P^2 = N^(3/5)/m^2`.

There are about `phi(m)` residue candidates per size interval. The already optimistic one-interval total is

`O(phi(m)n^3 + N^(3/5)n^2/m^2)`,

plus lattice generation, extraction, and stride-order preparation. Balancing exponents gives `m=N^(1/5+o(1))` and **the same exponent 1/5**, not 1/6. The explicit optimistic balance gives `N^(1/5)n^(8/3)/ell^(2/3)`, worse asymptotically than the checked known-interval `n^(13/5)/ell^(3/5)` result. Unknown factor-size enumeration adds cost. Fixed dimension keeps individual entries and exact root-isolation operands to `O(n)` bits; collision memory remains exponential as above.

This was generous: the short vector can encode `(mx+j)^2`, whose quotient is the constant 1 and supplies no factor. Avoiding that subspace can only require another argument; it is not licensed by the determinant bound. Also, order preparation for stride m⁴ must be proved and charged separately; transferring a statement for m² without checking it is invalid.

**Distinction and falsifier.** The specific candidate is a p² quotient collision search, not ordinary zero-root recovery. Its cheapest falsifier is the displayed determinant balance, before running LLL. Even an ideal informative shortest vector does not improve the total exponent in this rank-5 construction. This is not a lower bound for all higher-degree or higher-power variants.

## Card D — an explicit factorial-shift divisibility grid

**Status: explicit construction rejected; no cover conjecture solved.** This tests an actual family of structured sets instead of assuming that suitable sets exist.

**Construction.** For `B=floor(sqrt(N))` and `y=ceil(B^(1/3))`, compute `b=y!` by a product tree. Choose `L=y^2+1` and

`S={b+L+i : 0<=i<y}`, `T={L-jy : 0<=j<y}`.

Their differences are exactly `b,b+1,...,b+y^2-1`. Form the degree-y block polynomial and evaluate it at y arithmetic offsets, then gcd with N. All generation is uniform and uses N alone. This is a factorial-seeded candidate for the arithmetic-progression direction discussed by [Umans–Wang](https://arxiv.org/html/2511.10851v1), not a new consequence of their conjecture.

**Desired gain and full obligations.** If these differences covered every prime at most B, and a leaf divisible by N could be resolved efficiently, the main arithmetic would take `B^(1/3) poly(n) = 2^(n/6) poly(n)`. Building b is not free: it has `O(y log y)` bits and costs `O(M(y log y)log y)`. Modular polynomial construction/evaluation and descent conservatively cost `O(y n^3)`. This is still `2^(n/6) poly(n)`, with `O(y n log y)` bits a safe memory allowance. Extraction from a difference of `O(y log y)` bits must be charged separately.

**Two failures.** First, factorial divisibility covers small primes but not all primes through B: for `N=17*19=323`, `B=17`, `y=3`, the interval is `[6,14]` and misses both factors. The proposed universal coverage statement is false. Second, even a covered prime does not ensure a proper factor: a difference may be divisible by both factors of N. Factoring that large difference for free is precisely the kind of oracle this pass must not introduce. Polling more shifts without a coverage bound would be an unbounded restart scheme.

Selecting a shift by enumerating and assigning every prime through B is not a repair within the target budget: just listing them costs at least `Omega(B/log B)` records, versus the target `B^(1/3) poly(log B)`. One would need a different implicit construction *and* an extraction/separation theorem. Those are missing, not consequences of product trees.

**Cheapest decisive falsifier already obtained.** The explicit missed prime refutes the stated all-input cover. A finite counterexample alone does not exclude an eventual coverage theorem with finite exceptions; none is supplied here. It also does not refute the Umans–Wang conjecture, other shifts, or other structured covers. This card has no claimed general-input success probability and no accepted asymptotic improvement.

## Ranking and bounded next action

1. **A: only conditional survivor.** It has an exact recovery identity, a costed logarithmic target, and a small mathematical object to test. Its coverage-compression premise has significant negative geometric evidence.
2. **B: rejected as proposed.** Revisit only if giant-point structure yields an independently specified faster evaluation procedure.
3. **C: rejected at the optimistic cost screen.** Higher powers alone do not earn a smaller exponent here.
4. **D: rejected by explicit coverage failure.** It is a useful guard against turning a divisibility conjecture into a free construction oracle.

**Recommended next step: one 60-second certificate-reuse screen, then stop.** In a named `W001-deterministic-...` scratch file, use exact arithmetic to generate the dyadic rank-3 certificate pool for a fixed, published list of odd N at bit lengths 64, 128, and 256; use only N in generation. Test a bounded selection of unit residues for smooth m, retain the actual m values, and certify each envelope by endpoints and stationary points. These are primitive tests, not factoring benchmarks; arbitrary odd N need not be asserted prime or semiprime. Record all attempted residues and timeouts. Count original dyadic cells, distinct certificates, certified interval lengths, and the selected covering count. Separately record generation work so savings in the collision list cannot hide extra reduction work.

Freeze `K=16*ceil(sqrt(N)/m^(3/2))`, using a safe exact integer rounding implementation. The finite continuation criterion is at least a twofold reduction of the retained list in the largest completed cases without increasing K; failure rejects this pool as the immediate experimental lead. Passing only warrants investigating the precise asymptotic lemma: **a uniformly constructible pool and cover with `C(n)=O(n/log n)` for every residual semiprime**, with the displayed generation budget. Search first for congruence lattices with no useful coefficient pair in the necessary rectangle. One certified counterexample defeats a stated universal finite coverage bound; a family requiring `Omega(n)` certificates defeats the asymptotic compression claim for this construction.

No such screen was executed in this pass. No claim is promoted above idea/cost-screen level. Best supported general deterministic comparison remains the checked baseline; verified new improvement remains **NONE**.
