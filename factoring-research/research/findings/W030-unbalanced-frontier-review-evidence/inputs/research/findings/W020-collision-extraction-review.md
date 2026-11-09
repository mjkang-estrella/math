**W020 independent review: collision-to-annihilator extraction**

2026-10-08 local / 2026-10-09 UTC. **Accept the failure-set theorem and its replacement of W019 global-match recovery. Accept the explicit expected one-fifth composition. Clarify the localization depth and full-trial cost contracts below. No counterexample to the correctly stated theorem was found. Verified new complete factoring improvement: NONE.**

The change removes a real recovery obligation: one may keep every giant, localize any nonunit difference, and use a full-modulus equality as an annihilator of the original uniformly sampled alpha. High order, componentwise baby uniqueness, global-match deletion, and quadratic recovery of every globally matching tag are unnecessary for this randomized consumer. This does not supply a faster product evaluator or reduce the explicit pair/acquisition budget.

**Frozen scope.** The entire 140-line parent construction is frozen at SHA-256 `e176abf256524bc0a7480446798edfa4a7e12bf591ffe73a0c2c0f22eaf4ba73`. The [full brief](W020-collision-extraction-review-evidence/task-brief.md) and [input manifest](W020-collision-extraction-review-evidence/input-manifest.json) preserve hashes and exact read scope. All three requested mathematical findings were read completely; the completed W018 and W019 reviews are the local mathematical authorities. The five mandatory guidance/specification files were read, and STATE was consulted only for recorded operating-context ranges. W020-annihilator-amortization and its live review, conic identities, solver code, and Lean code were not audited. The parent remains principal researcher. Only this report and its assigned evidence directory were written.

**Accepted extractor and algebra.** Let N be odd composite with at least two distinct prime factors. Draw alpha exactly uniformly from 1,...,N−1. Its nonunit gcd is automatically proper. On the unit branch, require a finite, uniformly computable family, possibly implicit and adaptively selected, satisfying these conditions for every such alpha:

1. Some leaf difference is a nonunit modulo N.
2. Every reachable leaf has known integer exponents A,B with E=A−B nonzero; obtaining the leaf and its actual binary exponent is paid.
3. The evaluator returns a proper factor or correctly localizes a nonunit leaf, with a stated finite cost. Any internal randomness preserves these guarantees, or has a separately analyzed failure contract.

Unit multiples of `alpha^A−alpha^B` are equally valid leaves. A proper leaf gcd already succeeds. For a full leaf gcd, cancellation by the unit alpha^B gives alpha^E=1 modulo N. If E<0, taking the inverse gives alpha^(−E)=1; hence H=|E| is a **positive** annihilator. This is an integer exponent, not a residue modulo N or m². No local equality at only one prime, or full gcd at an internal product node, permits this inference for an arbitrarily selected exponent.

Write H=2^s h with h odd. For proof only, write `N=product p_i^e_i` and `ord_(p_i^e_i)(alpha)=2^v_i d_i`, with d_i odd. Divisibility of every local order into H implies d_i|h and v_i<=s. Thus for the complete chain

```
x_k = alpha^(h*2^k),  0<=k<=s,
x_k = 1 modulo p_i^e_i  iff  k>=v_i.
```

If the v_i differ, k=min_i v_i gives a proper gcd(x_k−1,N). It includes at least one whole prime-power component and excludes at least one whole component. Extra odd factors in H do not change this argument; extra powers of two only append identity stages. Inspect from x_0 onward, including its gcd. Stopping at the first global identity is safe after all earlier checks. Checking only H/2 is unsafe: N=15, alpha=2, H=8 gives alpha^4=1, but the chain 2,4,1 already gives gcd(4−1,15)=3. Negative E is harmless: for these same N,alpha, the equality alpha^(−3)=alpha gives E=−4 and the useful positive annihilator 4.

**No selection-bias defect.** Condition only on alpha being a unit. CRT then gives independent uniform original components. Set a_i=v2(p_i−1)>=1. Counting in the cyclic 2-primary component gives

```
Pr(v_i=0 | unit)=2^(-a_i),
Pr(v_i=t | unit)=2^(t-1-a_i),  1<=t<=a_i.
```

In particular every atom has probability at most 1/2. For any two components, with b=min(a_1,a_2),

```
Pr(v_1=v_2 | unit)=(4^b+2)/(3*2^(a_1+a_2)) <= 1/2.
```

For **every** selection rule satisfying the extractor contract, pointwise failure implies that all v_i agree. Consequently

```
Pr(trial fails) <= phi(N)/(N−1) * Pr(all v_i equal | unit)
                <= phi(N)/(2(N−1)) <= 1/2.
```

Neither the selected leaf nor H needs to be independent of alpha. Conditional on selecting a particular full collision, failure can have probability one: the leaf alpha−1 is full only at alpha=1, where every chain fails. This does not change the unconditional inclusion. Sampling a powered image in place of the original alpha, conditioning alpha on a prefilter, or resampling until an unspecified collision occurs would need a different argument. Uniform binary rejection sampling of 1,...,N−1 avoids this issue; its expected bit cost is O(log N).

Fresh independent trials have expected count at most two and `Pr(more than k trials)<=2^(−k)`. The same conditional-on-history argument allows adaptive family choices across trials if every new alpha is fresh uniform and all contracts still hold. This is an expected Las Vegas claim, not a deterministic time bound. Coverage without a usable finite algorithm gives no complexity theorem. With setup cost P and a uniform per-trial cost bound T (or a conditional expected bound valid at every restart), expected total cost is at most P+2T. A randomized detector that can miss collisions adds a failure event; the half bound cannot simply ignore it.

**Necessary exclusions and symbolic negative controls.** With E=0, alpha^0=1 provides no positive annihilator. For N=15, the singleton family `alpha^0−alpha^0` has complete nonunit coverage but causes every unit trial to retry, including alpha=2 with unequal local valuations. Its unconditional failure probability is 8/14=4/7, and success only from the initial nonunit gcd has expected 7/3 trials. Thus nonunit coverage alone does not imply the claimed bound. Merely skipping E=0 leaves is insufficient without re-proving coverage/localization on the remaining family.

Prime powers also need the stated exclusion. Reduction from units modulo p^e to units modulo odd p has a p-group kernel; a 2-power-order chain element is 1 modulo p exactly when it is 1 modulo p^e. Thus equal local valuations yield only gcds 1 or N in this chain, without a hidden partial-p-adic split. For N=9, the singleton `alpha^6−1` is full for every unit, yet its chain never splits a unit trial. Only alpha=3,6 succeed at the initial gcd, so expected trials are four. More generally N=p² gives initial-nonunit success probability 1/(p+1) for this style of construction. Exact perfect-power preprocessing returns a proper base in polynomial bit time, and even N is handled by 2. A prime-input termination contract is separate. These examples are hand-derived checks, not additional numerical runs.

**Localization is sufficient, with an explicit depth bound.** For a nonempty occurrence domain D, let P(D) be its exact product modulo N. Use finite recursive disjoint partitions `D=D0 disjoint-union D1`, preserving multiplicities, with `P(D)=P(D0)P(D1)`. Empty domains have product 1. The algorithm must construct the restrictions and identify a singleton leaf at the charged cost; the domain's description alone is not an oracle.

At the root, gcd 1 excludes this domain and a proper gcd returns a factor. At a node with full gcd N, compute P(D0). If its gcd is proper, return it; if full, descend into D0; if unit, descend into D1. In the last case P(D1) necessarily has full gcd, because multiplication by P(D0) is invertible. No nonunit division is used. A zero product is just a full-gcd node. Factors supported at different primes, or accumulated valuations at repeated primes, do not invalidate the rule. For example, modulo 45 the leaves 3,3,5 have product zero although no leaf is zero; a split can immediately expose gcd 9 or 5. At a singleton, and only there, a full zero difference invokes its known nonzero exponent.

If the maximum productive depth is d, each restricted product costs at most C, each restriction costs R, each gcd costs Q, and leaf decoding/exponent extraction costs L, the safe bound including initialization is

```
O((d+1)*(C+R+Q) + L + chain_cost).
```

For q=|D|, **O(C(1+log q))** follows when d=O(1+log q) and C also covers restriction construction, operand widths, and gcds; leaf/chain costs remain additive unless already included. This handles q=1. The parent's reference to merely poly(log N) depth is insufficient by itself to imply O(C log q): charge the actual depth or explicitly require logarithmic-depth partitions. Repeatedly peeling one leaf can take q−1 levels. Empty-child partitions must not allow nontermination. With many children, their search/evaluation count must also be paid. These are contract completions, not an obstruction to a balanced binary implicit family.

For n=bitlen(N) and ell=bitlen(H), the chain uses O(ell+1) modular powering/squaring steps and gcds, plus an exponent scan. A conservative bound is O((ell+1)n³+ell), in addition to obtaining and reading A,B and their difference. A small difference does not erase the cost of two huge input exponents. No factorization of H, order oracle, or factorization of N is required by the algorithm.

**W019 transfer, repeated values, and padded boundaries.** Use the accepted signed cover with `1<=u<=U<m`, `1<=|v|<=V<m`, root representative `0<=s<m²`, and interval endpoints

```
a_s=ceil((-W−s)/m²), b_s=floor((W−s)/m²),
ell_s=max(0,b_s−a_s+1).
```

For a nonempty interval, take `t0=a_s+kB`, `0<=k<ceil(ell_s/B)`, and all `0<=j<B`, including the last block's padding. Every block start is valid: a_s<=t0<=b_s. Setting `S'=s+m²(t0+j)` therefore gives exactly the sufficient enclosure

```
−W <= S' <= W+P_B,   P_B=m²(B−1).
```

Only the upper endpoint grows; negative t0 requires mathematical floor/ceiling, not truncation toward zero. Empty intervals contribute no giants. The lower enclosure is unaffected by padding, and B=1 gives P_B=0.

With beta=alpha^(m²) and `gamma=alpha^(u+vN−s)*beta^(−t0)`,

```
alpha^(s+m²t0) * (beta^j−gamma)
    = alpha^S' − alpha^(u+vN).
```

The multiplier is a unit, so gcds agree and a full leaf gives the annihilator from `E=u+vN−S'`. For the covered S=up+vq, `u+vN−S=(p−1)(vq−u)`, so the difference vanishes modulo p for every unit alpha. This requires neither q prime nor distinct baby residues. The true integer t has its covered block and baby index even if every residue in both lists is 1.

The exact sign-specific bounds from these enclosures are

```
v>=1:   N+1−W−P_B <= E <= VN+U+W,
v<=−1: −VN+1−W−P_B <= E <= −N+U+W.
```

Thus the computable guard `U+W+m²B<N` is sufficient for **every padded leaf**: E>0 for positive v and E<0 for negative v. It is conservative, not necessary. Without padding, U+W<N suffices. One may also use the two separate inequalities `W+P_B<N+1` and `U+W<N`. This proves the parent's guard without assuming random avoidance of E=0 or deleting padded matches. Deleting a giant merely because it matches a padded baby would be unsafe when babies repeat; keeping the padded leaf and applying this guard avoids that issue.

**Explicit evaluation and complete cost.** Form `F(Y)=product_g(Y−gamma_g)` over all G giant occurrences, and evaluate at all B babies. Monic product/remainder trees work over Z/NZ with repeated roots and repeated points: they use no inverses of point differences and need no squarefreeness. The outputs are B separate evaluated products, each with its multiplicities. Scan these B gcds; at the first full one, localize a nonunit giant for that fixed baby. A simple scan of at most G leaf differences already costs O(G), so the bound does not rely on a free tree descent. Alternatively evaluate cached polynomial nodes along one balanced path; their degrees sum to O(G). Stop at the first nonunit leaf, run its chain if needed, and restart on failure. There is no BG enumeration and no recovery of all global matches.

Given the residues and tags, polynomial construction/evaluation plus this one localization costs O~(B+G) modular work with the corresponding paid bit factors. Actual degrees, coefficient widths, table generation, tag storage, and initial giant exponentiations are still charged. Here `|t0|<W/m²+1`, `|E|<=VN+U+W+P_B`, and `|u+vN−s|<=U+VN+m²`; these and all list indices have O(log N) bits in both displayed parameter regimes. Signed powers use a checked modular inverse. Large numerical exponents require binary powering, not numerical-length loops.

Retain W019's `K<8m`, `T=sum ell_s<=8m+96sqrt(N/m)`, and

```
G=sum_s ceil(ell_s/B) <= K+T/B.
```

Prime acquisition, the Theta(UV)=Theta(m) signed pair loop, roots, intervals, ceilings, and giant setup therefore give per-range cost

```
O~(m+B+sqrt(N/m)/B).
```

Reuse alpha across the complete O(log N) dyadic schedule. **A trial is this covered schedule**, stopped earlier by any factor or failed full-collision chain, not a single possibly uncovered range. A range whose products are all units simply continues to the next range. Coverage of the full schedule and the pointwise chain argument give the half-failure bound even when an earlier range supplies the chosen collision. Alpha-independent prime/root/interval acquisition can be performed once and reused across restarts, with its expected or deterministic cost paid separately.

For `m=Theta(N^(1/5))`, `B=ceil((N/m)^(1/4))`, the reviewed `U<m` and `W<=6sqrt(mN)` yield `U+W+m²B=O(N^(3/5))`. Test the strict guard exactly across the ranges. For the specified parameter choice it holds beyond a fixed finite threshold, so a correctly priced finite-small-N fallback is sufficient. The accepted small-factor screen costs O~(1+(N/m)^(1/4)); even/perfect-power preprocessing, auxiliary-prime acquisition, and all dyadic ranges remain included. The resulting splitter still has expected `N^(1/5) poly(log N)` bit cost. This is a mathematical composition of imported primitives, not an installed implementation or an improvement over known bounds.

For the hypothetical `m=Theta(N^(1/3))`, `B=Theta(N^(1/6))`, the same guard's left side is O(N^(5/6)). That proves eventual nonzero exponents only. It does not lower the explicit Theta(m) pair work, prime sieve, or unbalanced coordinate-root acquisition. In particular the reviewed `U+V=O(1+sqrt(mN)/X+sqrt(m)X/sqrt(N))` can be Theta(m) near `X=Theta(sqrt(N/m))`. No N^(1/6) end-to-end cost follows.

**Primary context and scope limits.** The classical order-to-factor reduction and original-component 2-valuation argument are established; Shor's §5, printed pp. 15–16, gives that context. This review proves the arbitrary-positive-annihilator and adaptively selected collision composition above, using the completed W018 proof as its local source. No quantum step or novelty claim is involved. [Shor, primary paper](https://arxiv.org/pdf/quant-ph/9508027v2).

Harvey's Lemmas 2.3–2.4 supply fast product construction and evaluation at powers; Algorithm 4.1 uses a product gcd followed by a single leaf scan, and Algorithm 4.2 removes global matches under its different consumer contract. W020 changes that terminal recovery rule. Those old preconditions do not prohibit this new randomized composition. [Harvey, polynomial arithmetic and collision algorithm](https://arxiv.org/html/2010.05450#S4). The primary read scope and retained tool extracts are in the evidence directory; this was a bounded context check, not a priority survey. The brief's W008 additive-collision comparison supplies no known nonzero same-alpha exponent, so this theorem does not automatically apply to it; W008 itself was not re-audited.

**Exactly what remains.** For a proposed implicit improvement, supply:

1. A uniform public domain representation with all signs, pair roots, carries, intervals, and covered occurrences retained, plus a paid nonzero-exponent guard for every reachable leaf.
2. A concrete exact product/collision evaluator at its claimed cost, including actual polynomial degrees and widths; no supplied root/carry oracle or unpriced Theta(UV) expansion.
3. Computable product-conserving restrictions with the promised depth and cost, singleton decoding, and the signed leaf exponent. A scalar full product gcd without these operations is insufficient.
4. All acquisition, coordinate-root, small-factor, fallback, and dyadic costs, including the unbalanced ranges; uniformly paid trial costs and any detector misses or randomized preprocessing.

These obligations **replace** the old need for tag-sensitive quadratic recovery at every global match; they do not include high-order preparation, componentwise uniqueness, or removal of all global matches. Reject only claims that drop these remaining costs, extend the half bound to E=0/prime powers/biased original bases, or claim an achieved implicit exponent. The next decisive object is the missing evaluator satisfying this reduced interface.

No numerical certificate, parameter sweep, solver run, or Lean build was performed; the optional experiment was unnecessary for the symbolic verdict. No installations, delegation, commits, or shared solver/Lean/STATE/registry/task edits occurred. [Method/read scope](W020-collision-extraction-review-evidence/method-and-read-scope.json), [integrity check](W020-collision-extraction-review-evidence/verification.json), and [delivery inventory](W020-collision-extraction-review-evidence/delivery-manifest.json) preserve the audit boundary and evidence hashes.

At handoff all frozen hashes matched. Of the live inputs, only STATE differed; its new content was not substituted into this frozen review. The parent construction and both completed mathematical reviews were unchanged.
