# W001 — Hidden-factor collisions and group dynamics

Date: 2026-10-07, America/Los_Angeles. Bounded independent ideation pass.

**Verified factoring improvement: NONE.** Four mechanisms are specified below. None currently gives a new general-input complexity bound. The most consequential unresolved primitive is simultaneous ECM annihilator evaluation with its setup charged (Card 4). Card 2 yields a precise negative screen for one proposed collision amplifier, not an impossibility result for factoring or for other walks.

I read AGENTS.md, README.md, RESEARCH_LOOP.md, docs/SPECIFICATION.md, and research/STATE.md. The assigned independent lens supersedes the checkpoint's proposed next hypothesis; I did not read H002 or other researchers' proposals. Only this report and the permitted adjacent scratch checker were written. No shared solver, harness, Lean file, STATE, commit, or external publication was changed.

## Accounting and comparison rules

Let `n = bitlength(N)`. Analyze odd squarefree `N = pq`, `p ≤ q`, first; this is an explicitly scoped test class, not the all-composites contract. Even inputs and perfect powers can be handled separately with charged polynomial-time arithmetic, but that does not complete any missing general-input success proof here. Neither `p` nor an order is an algorithm input. Bounds depending on `p` describe performance; an implementation must search public size/budget guesses and charge that search.

Write `M(n)` for multiplication cost and `G(n) = O(M(n) log n)` for a fast gcd bound. All residues and curve coordinates are reduced modulo N. Write `P(m,n) = Õ(m M(n + log m))` for a conservative fast polynomial multiplication/evaluation budget; the soft notation hides logarithmic factors, **so it cannot certify a claimed logarithmic improvement**. Packed integer/FFT operands can be much wider than n: charge the degree, temporary coefficient width, and exact reconstruction. Memory below is in bits.

For m supplied residues, hidden-factor collisions can be detected in `Õ(P(m,n))` bit work, rather than explicitly doing m² gcds. Deduplicate exact residues modulo N, recursively divide the list, form monic product polynomials for one half, and evaluate them at the other half. Gcds of the resulting products detect cross-collisions. Retain/recompute the product tree to isolate a proper factor when a batched gcd is N. Monic polynomial operations need no inverse of an unknown nonunit. Exact-duplicate removal prevents an individual surviving difference from being zero modulo N. Allow `Õ(mn)` storage and the tree/replay cost. This is an application of established product/evaluation techniques, not a new factoring primitive; fast table matching and FFT extensions already occur in [Montgomery (1987)](https://wstein.org/edu/124/misc/montgomery.pdf) and [Montgomery–Silverman (1990)](https://cr.yp.to/bib/1990/montgomery.pdf).

Use **proper-factor probability**, not collision count: a collision at every prime factor can give only N. If one fresh attempt costs C and splits with probability s, repeated independent attempts cost C/s in expectation. A bounded-error claim additionally needs an explicit attempt cap and a per-input lower bound on s. None is supplied for arbitrary inputs here. Random seeds, map coefficients, parameter rejection, duplicate curves, and exhausted attempts belong in C or s.

The relevant benchmarks are Brent-style rho's heuristic `Õ(sqrt(p) M(n))`, ECM's heuristic `L_p[1/2,sqrt(2)] poly(n)`, and the general number field sieve's standard heuristic `L_N[1/3,(64/9)^(1/3)]`, where `L_x[a,c] = exp((c+o(1))(log x)^a(log log x)^(1-a))`. For balanced semiprimes rho is approximately `2^(n/4)` times arithmetic factors. These are different baselines; a smaller rho exponent need not beat ECM or NFS. Sources: [Brent (1980)](https://maths-people.anu.edu.au/~brent/pub/pub051.html), [Lenstra (1987)](https://annals.math.princeton.edu/1987/126-3/p09), and [Buhler–Lenstra–Pomerance, original NFS analysis](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf). Brent's cycle-finding improvement is a constant-factor gain, not a changed birthday exponent.

## Card 1 — Power-image compression with an explicitly priced exponent menu

**Primitive and algorithm.** Choose a public exponent K, for example `lcm(1,...,B)` or a power of two. Generate independent uniform units `a_i mod N`, checking nonunits for factors. Set `y_i = a_i^K mod N`; batch-search their differences as above. Try public K values in a specified budgeted schedule, not an exponent chosen using a hidden factor. Check the usual intermediate p−1 gcds during exponentiation as well, to avoid overlooking a cheaper success.

For a prime p, define `d_p = gcd(K,p−1)` and `s_p = (p−1)/d_p`. The K-th power map sends uniform units exactly uniformly onto an image of size s_p. Thus

`Pr[y_i = y_j mod p] = 1/s_p = d_p/(p−1)`.

The CRT components are independent for these independently sampled units. For a single pair, the exact proper-factor probability is

`(1/s_p)(1−1/s_q) + (1/s_q)(1−1/s_p)`.

The special case `s_p = s_q = 1` produces only identical outputs; endpoint collision counting would falsely report maximal progress. Intermediate exponent checks can sometimes still split such an N and must be included in the p−1 comparison.

**Complete proposed cost and gain.** Let k be K's bit length and let `C_K` include constructing K. A batch of m independent images costs

`C_K + O(m k M(n) + m G(n)) + Õ(P(m,n))`,

with `O(k) + Õ(mn)` storage and `O(mn)` expected random bits for unit generation on this scope. A sieve/product construction for `K = lcm(1,...,B)` has `k = Θ(B)` and approximately `Õ(B)` bit setup; writing down a prime table is not free. The useful birthday scale, away from the degenerate case, is m on the order of the square root of the smaller image size. Generation therefore gives the target `Õ(k sqrt(p/d_p) M(n))` when p is the easier component; gcd/evaluation costs must still be added.

Relative to rho, compression must exceed the squared per-sample overhead: roughly `d_p >> k²`, before logarithmic overheads. If `p ≈ 2^(n/2)`, `d_p = 2^(δn)`, and k is polynomial in n, the conditional scale is `2^((1/4−δ/2)n) poly(n)`. A polynomial d_p gives only a polynomial-factor saving over an exponential rho cost. There is no argument that the required d_p occurs for arbitrary p, or that a short exponent menu covers arbitrary p−1. Menu construction and unsuccessful members multiply/add real work.

**Scope, prior art, distinction.** Large known divisibility of p−1 can make power-map rho attractive on special input families. Structured rho was already used by [Brent–Pollard to factor the eighth Fermat number (1981)](https://maths-people.anu.edu.au/~brent/pub/pub061.html); [Montgomery's primary paper](https://wstein.org/edu/124/misc/montgomery.pdf) discusses power-map choices together with p−1, p+1, and ECM improvements. The independent-image version makes the collision law auditable and avoids assuming a high-degree walk mixes, but is not evidence of a new technique. Any smooth-order win must also beat p−1 with its second stage, not just vanilla rho. When the image is trivial at one prime, ordinary p−1 often extracts that prime directly.

**Unsupported step and falsifier.** The missing general-purpose primitive is an N-only, cheaply generated exponent menu with large d_p for at least one hidden prime, without already paying comparable smoothness/order-search work. Cheapest screen: for a preregistered menu, audit `d_p/k²` on evaluator-known prime factors, including factors whose p−1 has a large prime outside the menu. The solver receives only N; factor-based labels are diagnostic only. A win confined to large smooth divisors of p−1 is scoped. Fixed-menu misses refute the menu's coverage, not all possible menus.

**Disposition:** survives only as a known special-family mechanism and a comparison/control for compression experiments. No general asymptotic improvement claimed.

## Card 2 — Coalescing shifted-square layers, followed by endpoint batch gcd

**Primitive and algorithm.** Choose h independent uniform shifts `b_1,...,b_h mod N`. Draw m independent uniform seeds. Apply the same layer sequence to each seed:

`x_{j} = (x_{j−1}+b_j)² mod N`.

Compare final endpoints with the monic-product collision extractor. The tempting claim is that repeated many-to-one maps shrink the hidden state space, so endpoints collide sooner than raw samples. The maps respect reduction modulo every factor; a walk selected by arbitrary low bits of the integer representative generally would not have this property.

**Exact collision calculation (derived here).** For two trajectories over an odd prime p, equality persists once reached. Conditional on distinct current values u,v, the next values coincide precisely when `2b = −(u+v) mod p`, which has one solution. Hence, including the probability that initial seeds coincide,

`C_h(p) = 1 − (1−1/p)^(h+1) ≤ (h+1)/p`.

No random-map or mixing heuristic is used in this pair calculation. It also follows from

`x_h−y_h = (x_0−y_0) ∏_{j=1}^h (x_{j−1}+y_{j−1}+2b_j) mod N`.

Every new factor in that product is uniform modulo N conditional on the past. Coalescence is therefore accumulation of charged opportunities for a zero divisor, not free entropy reduction. CRT independence gives the exact useful-pair probability

`C_h(p)(1−C_h(q)) + C_h(q)(1−C_h(p))`.

When h approaches or exceeds both primes, simultaneous collisions increasingly consume extraction probability. Across more than two seeds the collision events are correlated, so a large expected number of collisions alone is not a constant-success theorem.

**Complete proposed cost and gain.** Straight evaluation costs

`O(mh M(n) + (m+h)n) + Õ(P(m,n))`,

uses `Õ((m+h)n)` memory if shifts and a collision tree are retained, and samples `O((m+h)n)` random bits in expectation. A necessary scale for constant success is `m²(h+1) = Ω(p)`, by the union bound (up to a factor two for either p or q). At the optimistic birthday threshold, the direct-generation cost is therefore `Ω(sqrt(ph) M(n))` for h≥1. This is worse than uncompressed birthday work. At a fixed generation budget W≈mh, the collision upper bound is proportional to `W²/(hp)`, rather than `W²/p` for W independent raw samples. The improvement in collision frequency has been purchased more expensively than it is worth.

There are two concrete attempts to evade that accounting:

* Expand the composed polynomial and multipoint-evaluate it. Its degree is exactly `D = 2^h`. Construction plus evaluation costs approximately `Õ(P(D+m,n))` and comparable coefficient storage, not `poly(h)+Õ(m)`. Keeping D manageable restricts h to logarithmic size in m and supplies no exponent change. Logarithmic gains require explicit costs, not soft-O notation.
* Postulate a batch circuit evaluator costing `Õ(h+m)` operations without expansion or hidden evaluations. This is the **unsupported new primitive**. Even granting it, generating the h independent shifts costs Ω(hn) bits. Minimizing `h + sqrt(p/h)` gives the optimistic scale `p^(1/3)`, or `2^(n/6)` on balanced inputs, still asymptotically slower than ECM/NFS. Replacing the independent shifts with a short seed changes the mathematical model and requires a new collision proof.

Orbit-prefix reuse is not automatically an escape: paths that merge only modulo p cannot be recognized and cached as identical residues modulo N. Exact mergers modulo N are observable but create redundant paths, not distinct factor opportunities. Recycling h highly correlated layers is not h independent attempts.

**Prior art and distinction.** Rho cycle extraction and gcd batching are established [Brent (1980)](https://maths-people.anu.edu.au/~brent/pub/pub051.html). The need to price correlations rather than assert independent birthdays is also explicit in [Kim–Montenegro–Peres–Tetali's Markov-chain birthday analysis](https://www.microsoft.com/en-us/research/publication/birthday-paradox-markov-chains-optimal-bound-collision-pollard-rho-algorithm-discrete-logarithm/); that paper concerns a discrete-log random-oracle walk and is **not** a theorem about this factoring walk. The present proposal is a specific layered circuit whose pair law can be proved exactly. No novelty claim follows from this limited search.

**Cheapest decisive falsifier.** Prove the recurrence and multiply by the actual number of layer evaluations. That already rejects the straightforward amplifier's claimed time improvement. The permitted scratch checker independently enumerated 12 prime/depth cases and four CRT useful-pair cases, all matching the formulas. It did not establish a new factoring performance result.

**Disposition:** direct algorithm rejected for speed; exact cost/collision lemma retained. A genuinely faster batch evaluator is a separate, unprovided algorithm.

## Card 3 — Isogeny chains to strip residual ECM orders

**Primitive and algorithm.** Start with an explicit curve/point modulo N, checking its discriminant and every necessary denominator for factors. Compute `Q = [K_B]P`, `K_B = lcm(1,...,B)`. Rather than abandon a failed curve, generate a chain of small-degree isogenies, push Q through each map, and gcd-test projective denominators. The hoped-for gain is to remove residual point-order factors or cheaply obtain many new group-order trials while reusing most work.

A concrete cheap starting edge is the rational 2-isogeny of `y² = x³ + A x² + C x`, using `(0,0)` as kernel generator. Its usual quotient model has coefficients `−2A` and `A²−4C`; subsequent known-kernel edges can be similarly evaluated. Reusing only the distinguished `(0,0)` kernel immediately gives the dual edge: two steps return coefficients `4A,16C`, an isomorphic curve, and the composition is multiplication by 2 up to that isomorphism. A productive new branch needs additional kernel information. Require good reduction and checked units. An edge requiring an unknown root is not a free continuation.

**Decisive algebraic obstruction.** For a homomorphism φ and a point Q of order m,

`ord(φ(Q)) = m / |<Q> ∩ ker φ|`.

For a separable isogeny of degree R, the denominator divides R. Consequently, for any prime ℓ not dividing R, the ℓ-primary part of Q's order is unchanged. Composing isogenies whose degrees have prime factors at most B cannot remove a residual prime ℓ>B. Additional small-prime valuations can instead be tested by further ordinary scalar multiplication and need comparison with that inexpensive option.

Nor does a chain provide fresh curve-order trials: curves isogenous over the same finite field have the same number of rational points. This fact is stated and used in the primary research paper [Jao–Miller–Venkatesan, “Do All Elliptic Curves of the Same Order Have the Same Difficulty of Discrete Log?”](https://djao.math.uwaterloo.ca/wiki/images/9/91/Asiacrypt-2005.pdf). A long isogeny orbit must not be counted as many independent ECM smoothness samples. Changing to a nonisogenous curve abandons this specific work-sharing argument.

**Complete conditional cost and proposed gain.** Small-degree edges have constant-size coordinates and cheap arithmetic, but t such edges still cost `O(t M(n))` plus kernel construction/checking, on top of `O(B M(n))` stage 1. They supply no gain for the rough-prime obstruction just proved. Memory can stay polynomial in n for a streamed chain of bounded-degree edges.

If a residual prime ℓ is deliberately targeted instead, the optimistic price is

`O(B M(n)) + C_kernel + Õ(sqrt(ℓ) M(n)) + unit/gcd checks`,

before division by the actual split probability. [Bernstein–De Feo–Leroux–Smith (2020)](https://arxiv.org/abs/2003.10118) gives the square-root isogeny evaluation improvement **given a point of prime order ℓ over a known finite field**. It does not construct that kernel over an unknown factor, identify ℓ, or guarantee that its map is usable modulo N. Explicit kernel-polynomial storage may be Θ(ℓn). With a supplied point generator, allow `Õ(sqrt(ℓ)n)` workspace for a square-root evaluation, plus the entire storage `S_kernel` of the still-unspecified kernel construction. Neither `C_kernel` nor `S_kernel` has a favorable bound in this proposal. Field algorithms adapted to the composite ring must charge failures and extract factors from nonunits when possible.

For `ℓ ≈ 2^(αn)`, even the optimistic evaluation term is `2^(αn/2) poly(n)` with kernel generation still outstanding. If ℓ and Q are already known and `[ℓ]Q` is zero at one component only, that scalar multiplication directly yields an ECM factor in O(log ℓ) group operations; constructing an isogeny to annihilate the same Q is unnecessary. For unknown residual ℓ in an interval, the proper comparison is an optimized ECM second stage, not restarting elementary rho.

**Assumption, distinction, falsifier.** The unsupported step is a cheap N-only source of rough-prime kernel information that improves extraction rather than merely supplying the answer to an ordinary scalar test. A two-line finite-group proof of the displayed order formula decisively kills the bounded-smooth-degree version. This pass proposes that reuse mechanism and rejects it; it does not claim the known isogeny algorithms are new or exclude other uses of endomorphisms.

**Disposition:** bounded-degree smoothness amplification rejected. The large-degree version has no supplied kernel-generation advantage.

## Card 4 — Batch ECM over a curve parameter without materializing the annihilator

**Primitive and algorithm.** Use `E_a: y² = x³ + a x + 1`, with the explicit point `P=(0,1)`. For r independently generated parameters a_i, gcd-check `4a_i³+27` for singular reductions. Construct `K_B = lcm(1,...,B)`. The annihilation condition is encoded by the division polynomial

`F_K(a) = ψ_K(0,1; a,1)`.

Evaluate `F_K(a_i) mod N`, multiply the values modulo N, and gcd with N. Split/replay the product tree if the gcd is N. This searches r different curve orders. Independent parameters avoid assuming that a short multiplicative orbit such as `a_i=2^i` produces r distinct useful curves modulo a hidden prime. All randomness, rejected singular curves, and repeated parameters are charged.

The desired new primitive is **compute the product, or the vector of values, in roughly additive cost in B and r, without constructing all coefficients of F_K**. It has precise inputs `(N,K,a_1,...,a_r)` and output residues or their product. It cannot call order finding, point counting over the unknown factor, modular square-root oracles, or precomputed size-dependent tables.

**Why a genuine primitive would matter.** Under the usual ECM smoothness model, set `X=log p` and `log B = b sqrt(X log X)`. A curve's success probability s has the heuristic inverse scale

`1/s = exp((1/(2b)+o(1)) sqrt(X log X))`.

Assume, additionally, this particular curve/point family has that useful split probability and r fresh parameters give the expected independent-trial amplification. Ordinary evaluation costs `r B poly(n)` with `r≈1/s`, whose optimized leading constant is `min_b (b+1/(2b)) = sqrt(2)`.

A uniform `Õ((B+r) M(n))` batch primitive with `Õ((B+r)n)` storage would instead give leading constant `min_b max(b,1/(2b)) = 1/sqrt(2)`. That is a substantial **conditional** ECM improvement, `L_p[1/2,1/sqrt(2)] poly(n)`. For balanced N it still has the L exponent 1/2 and does not beat the standard NFS exponent 1/3. The cost includes generating K and all r inputs; r is not free advice. The smoothness model, usefulness at exactly one CRT component, and the batch primitive are all unproved assumptions here.

**What the concrete implementations actually cost.** Three implementations can be specified now:

1. Evaluate the division-polynomial/scalar recurrence separately at each a_i: `O(r B M(n))` plus parameter generation, `O(r)` gcd/product work, and tree storage/replay. This is ordinary ECM-stage work, with different representation/constants.
2. Materialize F_K and multipoint-evaluate it. For this family, over the integers,
   `deg F_K = (K²−1)/4` for odd K and `K²/4−1` for even K. Dense storage/evaluation therefore has degree `D = Θ(K²)`. Since `log K_B = Θ(B)`, D is `exp(Θ(B))`, not B². A dense plan budgets at least D coefficient slots and about `Õ(P(D+r,n))` arithmetic/evaluation work (with the recurrence-generation work included). Reduction modulo N does not license assuming all these coefficients disappear. This is prohibitive at ECM smoothness bounds.
3. Set `A(T)=∏(T−a_i)` and compute the division-polynomial recurrence in `(Z/NZ)[T]/A(T)`, keeping degree below r. Since `P=(0,1)`, the recurrence's scalar divisions use only powers of 2, which are units for odd N. This avoids the enormous dense degree, but uses `O(log K)=O(B)` polynomial-ring steps of cost approximately P(r,n): `Õ(B P(r,n))`, followed by value extraction or a product/norm calculation. It does not establish the required additive B+r cost. Forming A, its coefficients, and any resultant is included.

Small blocks, batch inversion, or choosing a faster curve model can improve constants; eliminating the multiplicative B×r contribution needs an actual further algorithm. A compressed circuit of length O(B) is not automatically cheap to evaluate at r inputs.

**Primary prior art and distinction.** This exact broad direction is already present in [Zhihong Li's dissertation, “Elliptic curve factoring method via FFTs with division polynomials”](https://docs.lib.purdue.edu/dissertations/AAI3263600/), including a univariate polynomial in the curve coefficient. The [Li–Wagstaff primary poster](https://www.cerias.purdue.edu/news_and_events/events/symposium/2004/posters/pdfs/FFT-ECM.pdf) explicitly combines division polynomials, simultaneous evaluations, and batched gcds. Its optimistic performance discussion is not adopted as a verified complexity result. The proposed research distinction would have to be the specified **nonmaterializing additive-cost primitive**, not the use of FFTs or many curves. Existing curve arithmetic/torsion improvements are documented by the authors of [ECM using Edwards curves](https://eecm.cr.yp.to/); none may be relabeled here as a changed L constant without analysis.

**Cheapest decisive falsifier.** Substitute `K=lcm(1,...,B)` into the polynomial degree before implementing a large batch. This decisively rejects the dense-polynomial shortcut. The adjacent checker verified exact integer coefficients/degrees for 32 indices, including degrees 3, 15, 63, and 255 at K=4,8,16,32; these are finite sanity checks, not the general degree proof. For the reduced-ring shortcut, count full polynomial products/reductions across the scalar recurrence rather than counting one whole recurrence as one operation.

**Disposition:** highest-upside unresolved primitive, but **not a surviving complete factoring algorithm**. Dense and straightforward reduced-ring realizations do not deliver the proposed gain, and the broad batching direction has direct prior art.

## Ranking and bounded recommendation

There is **no survivor supporting a new general factoring bound**. Rank the remaining research questions, rather than presenting unsupported primitives as working algorithms:

1. **Card 4:** retain only the clearly defined nonmaterializing batch primitive. It is the one mechanism here whose success would change an ECM leading constant under explicit heuristics. Direct prior art and the B×r barrier make the evidentiary bar high.
2. **Card 1:** retain as a scoped compression control; any useful result must beat optimized p−1/stage 2 on the same family and must charge exponent selection.
3. **Card 2:** retain the exact collision/extraction accounting lemma. Straightforward dynamics loses; even its idealized explicit-layer batch model remains exponential in n.
4. **Card 3:** close the proposed small-degree stripping/order-resampling mechanism because the group-order and point-order invariants directly contradict it.

**Recommended next step, narrowly falsifiable:** give Card 4's reduced-ring implementation one focused mathematical audit. For the fixed doubling/division-polynomial recurrence with `K=2^h`, reduce after each step modulo a generic monic polynomial of degree r. Prove or refute that, once the intermediate degrees reach r, each remaining doubling has a generic degree-Θ(r) operand, so the summed operand-degree volume is `Θ(r(h−O(log r)))` when h≫log r. Check the generic claim with independently chosen parameters, not specially cancelling coefficients. If it holds, reject this specific “reduce modulo A after every step” construction as the route to additive cost, unless a new recurrence is supplied that provably bypasses those dense stages. This is an audit of an explicit construction, not a lower bound on all possible batch evaluators. No shared harness or Lean expansion is needed for that decision.

## Recorded finite check and limitations

The only scratch execution was:

`timeout 60s python3 research/hypotheses/W001-dynamics-check.py`

It exited successfully in under one second and wrote no files. It checked 12 shifted-square collision laws, four CRT useful-pair laws, 30 power-image laws, and 32 exact integer division-polynomial degrees. The source is retained as [W001-dynamics-check.py](W001-dynamics-check.py). These computations use public small primes as mathematical test parameters; they are not solver trials, timing evidence for a factoring improvement, or claims about arbitrary composites. General probability formulas above have explicit derivations; no Lean proof or independently reviewed full complexity theorem was produced.

Links cited above were checked through web retrieval/search during this pass. Some publisher/author PDF endpoints intermittently returned access errors; claims use accessible author/institutional copies or indexed primary-paper text. This is a bounded prior-art check, not an exhaustive novelty search. Failure of these four proposals says nothing about the impossibility of other classical factoring improvements.
