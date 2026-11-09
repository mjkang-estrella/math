# W033 separating-cover review

**Disposition: accept A's scoped construction and rejection; accept B's conditional integer collision consumer. B substantially repeats existing machinery, including the exact W006 derivative repair. No separating generator or complete factoring improvement is established. Verified complete factoring improvement: NONE.**

This is a symbolic correctness, cost and focused primary-source review. No numerical experiment, parameter search, factoring run, Lean edit, shared-code change, task-registry change, installation, commit or delegation was performed. The full task message and parent W033 brief are frozen in [the evidence directory](W033-separating-cover-review-evidence/). The [delivery manifest](W033-separating-cover-review-evidence/manifest.json) records all payloads; its external checksum is in [manifest.sha256](W033-separating-cover-review-evidence/manifest.sha256). The [read-scope record](W033-separating-cover-review-evidence/read-scope.json) distinguishes frozen files from audited portions. No W032 review or assay was repeated.

**Notation correction.** Write `ell = bit_length(N)` for the research contract's input length. Write `x` for the *divisor-cover cutoff* denoted `n` in the cited papers and in W033 A. These are different parameters. Below `h` is the grid side length, while `Y` is its maximum integer value. No all-input factoring claim follows from choosing `x=ell`.

**A: the CRT grid is correct.** Fix `0<a<1`, let `P` contain every prime in `[a sqrt(x),sqrt(x)]`, and assume `|P|>=2`. For a nonempty bipartition `P=A disjoint-union B`, define

```text
C = product(q in B) q,     D = product(p in A) p,     Q = CD.
```

All these primes are distinct. Thus `gcd(C,D)=1`, `C` is a unit modulo every `p in A`, and `D` is a unit modulo every `q in B`. Choose integer indices `0<=i_p,j_q<h`, with `h>=1`. The congruences

```text
b = -C i_p (mod p),        b = -D j_q (mod q)
```

have exactly one solution modulo `Q`. At `F(i,j)=b+Ci+Dj`, the first congruence annihilates `F(i_p,j)` modulo `p` for every `j`; the second annihilates `F(i,j_q)` modulo `q` for every `i`. Consequently `pq | F(i_p,j_q)`. The construction needs no injectivity among the chosen indices or among the grid values. It is a generalized progression of rank at most two; no proper-GAP assertion is needed.

Choose the CRT representative `b0 in [0,Q)`. Taking `b=b0` if positive, and `b=Q` otherwise, makes every entry strictly positive. Equivalently, always taking `b0+Q` is safe. Neither construction uses the vacuous witness zero.

Label the primes by distinct binary strings of length `k=ceil(log2|P|)`. Each nonconstant bit defines a bipartition and its own independently constructed grid. Every distinct pair differs in some bit, and hence occurs across some partition. The union of at most `k` grids covers every `pq` with distinct `p,q in P`. This neither covers prime squares nor proves the full `x`-divisor property. A union of grids is not automatically one rank-two grid. Its explicit size is at most `k h^2`, with repeated values counted only once if desired.

**A: the height and acquisition costs really fail.** The prime-number-theorem band estimate gives

```text
log Q = sum(p in P) log p = (1-a+o(1)) sqrt(x),
max(log C, log D) >= (1/2) log Q = Theta(sqrt(x)).
```

Here the last `Theta` applies to the displayed lower-bound quantity, and `max(log C,log D)` is itself `Theta(sqrt(x))` since it is at most `log Q`. With `h>=2`, positivity and the presence of adjacent grid indices imply `Y>=max(C,D)`, so `log Y=Omega(sqrt(x))`. This contradicts the target `log Y<=x^(1/3+o(1))`. At `h=1` all prescribed indices are zero, so the sole positive entry is a multiple of `Q` and has the same obstruction. A larger choice of `b` cannot repair it.

The explicit prime table has `Theta(sqrt(x)/log x)` records and `Theta(sqrt(x))` bits. Prime generation, the products, CRT, coefficient storage, partition labels and any emitted grid values all require payment. A sieve through `sqrt(x)` already gives a concrete construction with at least this scale of output. One must not replace the `Theta(sqrt(x))` coefficient widths by `O(log x)` arithmetic. This rejects the specified axis-aligned template, not other rank-two grids, oblique lines, or factoring algorithms.

There is an additional useful diagnostic: on an actual input `N=pq` with `p in A,q in B`, `gcd(N,C)=q` immediately. The constructed grid is unnecessary for splitting this scoped input after the prime products have been acquired. For `h>=2`, it also has a separating grid edge: retain `j=j_q` and move from `i_p` to an adjacent valid index. The difference of one in `i` preserves divisibility by `q` and destroys divisibility by `p`. Thus A can separate this band family, but already paid for a prime table and coefficients that directly expose its factors. It does not acquire cheap separating lists. If one adopts the integer-factoring substitution `x=floor(sqrt(N))`, the table and coefficient scale is `N^(1/4)` up to logarithms, rather than the intended `N^(1/6)` scale.

**Primary-source audit, kept at scope.** He–Sahai Theorem 1.1 applies to positive one-dimensional `x`-divisor progressions of height `Y` with `log Y=o(sqrt(x))`. It proves

```text
L >= (sqrt(8/27)-o(1)) x^(3/4)/sqrt(log x).
```

Hence length `x^(2/3+o(1))` and logarithmic height `x^(1/3+o(1))` cannot coexist, even along an unbounded subsequence. Remark 4.1 excludes zero. Remark 4.2 explicitly limits the conclusion to the one-dimensional version: the proof's two-block intersection argument uses a single step coefficient. It supplies no rank-two lower bound and no obstruction to arbitrary input-dependent separating lists. I checked the statement, the incidence argument's applicability, and the stated scope; the parent's W032 work is unrelated. [He–Sahai, Theorem 1.1 and Remarks 4.1–4.3](https://arxiv.org/html/2608.06681v1).

Umans–Wang's §3 conjectures require positive difference covers, short lists and bounded height; the strong form adds GAP structure. They assert existence only infinitely often. Conjecture 5.1 adds efficient leaf factorization. Theorem 5.2 assumes total-product coverage, interval evaluation and prefactored leaves. Theorem 5.5's exponent `max(alpha,beta)/2+o(1)` remains conditional. These statements do not supply uniformly acquired lists at every needed scale.

Appendix A needs explicit accounting/boundary repairs: A.1 uses `product(d_i+1)=|S|`; charge tuple count unless injectivity or efficient distinct-sum enumeration is proved. Lemmas 5.3–5.4 state `d<=n`, whereas the framework needs `d<=N`; the modular arithmetic extends with its actual `log d` cost. A.2's inclusive endpoints overlap the final row. For `h=|S|`, `[a,b]=[u h+r,v h+s]`, use one row slice if `u=v`; otherwise initial columns `r..h-1`, full rows `u+1..v-1`, and final columns `0..s`. Evaluate `product(j=u+1..v-1)(X-t_j)` on `S`; an empty interior contributes 1. This is an indexing repair, not a speedup. [Umans–Wang, §3, §5 and Appendix A](https://arxiv.org/html/2511.10851v1).

**B: exact contract and completeness.** For any integer `N>1`, suppose two acquired integer lists have at most `m` entries each. The sufficient promise is

```text
there exist original entries s,t with 1 < gcd(s-t,N) < N.       (B1)
```

Generation must use only the authorized input `N` (and explicitly charged public parameters/randomness if applicable). The consumer itself is deterministic. A prime input cannot satisfy (B1); a failure result is not a primality certificate.

Reduce each entry to `[0,N)`, then deduplicate *within* each list. Let the resulting sets be `S,T`, and put `R=Z/NZ`. Reduction preserves every difference gcd; deduplication preserves existence of a proper edge. It need not preserve multiplicities, valuations of aggregate products, or probability laws on list occurrences. None is required by (B1).

Build

```text
F(X) = product(t in T)(X-t) in R[X].
H(s) = F(s)   if s is not in T,
       F'(s)  if s is in T.
```

If `s in T`, it occurs exactly once. Write `F=(X-s)G`. Formal differentiation gives `F'=G+(X-s)G'`, hence `F'(s)=G(s)` over every commutative ring. Therefore in both cases

```text
H(s) = product(t in T, t != s in R)(s-t).                     (B2)
```

There is no division by `s-t`, an integer index, or a factorial. Distinct residues may coincide modulo individual unknown primes; they remain present. The proof is valid even when the derivative's leading coefficient vanishes or its degree drops in `R`.

Every edge surviving in (B2) is nonzero in `R`. Its gcd with `N` is consequently either 1 or a proper divisor. A product is a unit exactly when all its factors are units: if a product has an inverse, each factor obtains an inverse by multiplying that inverse by the other factors. Thus a row gcd exceeds 1 exactly when that row has a proper surviving edge. In particular, (B1) survives normalization and forces a successful row. Every earlier nonunit row also succeeds. Conversely, if all row gcds equal 1, no original cross-edge had proper gcd. This is an exact consumer criterion, not an assumption that a supplied prime cover separates.

For `S` empty there are no rows. For `T` empty, `F=1` and all row values are 1. For `T={s}`, the excluded row value is `F'(s)=1`. These cases cannot satisfy (B1) for the relevant rows.

**B: one full-row descent always terminates properly.** Retain a balanced `T` product tree with node polynomial `F_U=product(t in U)(X-t)`. Sorting and merging the two residue lists marks the unique `T` leaf index for each shared value. For the selected row define

```text
E_U(s) = F_U(s)    if U does not contain that exact residue,
         F_U'(s)   if U contains that exact residue.
```

Membership is decided by the stored leaf index and node index interval, never by `F_U(s)=0`, which could also reflect unknown prime-component collisions. Identity (B2) applies to every node, so `E_U=E_left E_right`, including nodes containing the excluded leaf.

At a row gcd equal to `N`, evaluate child exclusion values. If either child gcd is proper, return it. Otherwise at least one child gcd is `N`, since two units cannot multiply to a nonunit. Descend into that child. Equivalently one may follow any child with gcd greater than 1 until returning a factor. No backtracking is needed. At an excluded singleton the value is 1; at any other singleton it is `s-t != 0 mod N`, whose nonunit gcd is proper. A full-gcd leaf is impossible. This proves termination at or before leaf depth.

With retained polynomials, evaluating both children by Horner and computing a derivative when needed costs linear work in their total degree. The degrees along one balanced path form a geometric sum, giving `O(|T|)` residue operations, plus `O(log(2|T|))` gcds. A one-time scan of the nonmatching leaves is also valid, using `O(|T|)` gcds. Starting either localization guarantees success, so the scan is not repeated for every row. Tree layout and coefficient access must still be charged in bit work.

Repeated prime factors do not break this argument. For `N=p^e`, several leaves with `0<v_p(s-t)<e` may combine into a full row gcd. Every such leaf individually yields a proper factor. For arbitrary `N=product p^e_p`, the same unit/product argument applies. The descent need not preserve every prime or the full valuation of its parent; it needs just one nonunit leaf.

**B: monic evaluation, precision and full cost.** Construct `F,F'` and evaluate both at all queries by product/remainder trees. These are evaluations, not interpolation: point differences need not be units or even distinct modulo a prime. Every remainder divisor is monic. Its reversed polynomial `U` has constant term 1 and admits an inverse power series using

```text
G_new = G(2-U G) mod X^(2k),
1-U G_new = (1-U G)^2 mod X^(2k).
```

Starting at `G=1`, this uses no inverse of 2 or other nonunit. Reverse, multiply to the required quotient precision and subtract to perform monic division. Store coefficients modulo `N` throughout. Coefficient reduction modulo `N` commutes with formal differentiation.

Crucial precision guard: compute `F'` before evaluation, or retain enough local polynomial information. Differentiating the constant remainder of `F` modulo `(X-s)` gives zero and is wrong. Reduction modulo `(X-s)^2` would retain the needed linear coefficient, but is not required by the two-tree algorithm. Arbitrary truncation of `F` in powers of `X`, or differentiation of a previously evaluated value, is not licensed. The omitted product is used locally; it is not computed by attempting to divide a zero residue by zero.

Here is an explicit conservative bit envelope, after handling empty lists. Let `u` be the total number of raw input records, `r=|S|+|T|<=2 min(m,N)`, `w=ell+ceil(log2(r+2))+O(1)`, and let `M_Z(L)` be a regular fast integer multiplication bound. Packing two length-`d` coefficient arrays in radix `2^b` with `b>=2 ell+ceil(log2(d+1))+1` bounds each convolution coefficient below the radix. This uses `O(d(ell+log(d+1)))`-bit temporary integers, not constant-width integer products. Unpack and reduce the coefficients; a safe envelope is

```text
P_N(r) = O(M_Z(r w) + r w^2).
T_batch = O(P_N(r) log(2r)) + r poly(ell+log(2r)).
```

This includes a constant number of product/remainder trees, differentiation, query gcds, one localization and final divisor verification. Since the deduplicated sets are subsets of `R`, `log(2r)=O(ell)`. With fast multiplication this yields the claimed soft-linear list dependence and polynomial bit-width cost. Ordinary schoolbook polynomial multiplication would not establish it.

Add separately: (i) the actual list/coefficient acquisition algorithm; (ii) reading and reducing every original integer at its full bit length; (iii) deterministic sorting/deduplication, conservatively `O(u log(2u)(ell+log(2u)))` bit work; (iv) tags, schedules, membership indices and all storage traffic. Explicit raw integers of total bit length `B_data` already require `Omega(B_data)` input work. A compact circuit can avoid emitting huge integers only if it actually computes the required residues within a proved paid bound. GAP collisions can make representation tuple count exceed distinct cardinality; deduplication cannot refund generation. These are costs, not an assumed cheap oracle.

Retained coefficient trees use `O(r ell log(2r))` bits, plus records, indices and multiplication scratch; a conservative soft-`O(r poly(ell))` batch-space bound suffices. No list of `m^2` differences is produced, and no huge integer leaf is factored. The algorithm returns one proper divisor. Full factorization requires repeated valid acquisition on the remaining composite cofactors and a charged primality/recursion procedure; those guarantees are absent here.

**Existing machinery and what is resolved.** W001's original [collision accounting](../hypotheses/W001-dynamics.md) already deduplicates one global residue list, splits it recursively, evaluates product polynomials and localizes nonunit products. Applying that detector to the deduplicated union `S union T` preserves any promised proper cross-pair and has the same soft-linear bound; finding a useful within-list pair would also be a valid split. It need not preserve the bipartite witness. Thus B supplies no new factoring reduction at the asymptotic level.

More decisively, [W006 §4–5](W006-batch-review.md) already gives the exact `P/P'` rule, stored membership index, omitted-self child product, one descent, monic Newton division and packed arithmetic. Its [accepted disposition](W006-map-batch-disposition.md) restricts its *norm-based* recovery theorem to distinct odd semiprimes. B is the integer-residue specialization, with the direct nonzero-leaf argument above justifying general composites. This does not retroactively extend the quadratic-norm theorem to prime powers.

The accepted [W013 consumer](W013-hidden-period-consumer.md) and [W019 review](W019-public-cover-review.md) use component-order uniqueness and tagged integer-root recovery to justify deleting entire globally matching giant values. Arbitrary W033 lists lack that justification. Symbolically, let `N=pq`, `S={0,p}`, `T={0}` as residue sets. Deleting the shared value `0` from `T` loses the proper cross-edge `p-0`; deleting only the edge `(0,0)` preserves it. Positive integer lifts can be used, so this is not relying on a forbidden zero integer witness. This is a symbolic counterexample to whole-value deletion, not a numerical experiment.

For external primary antecedents, Harvey's Lemmas 2.1/2.3 give packed polynomial multiplication and product trees. Algorithm 4.1/Proposition 4.1 batch-evaluate a polynomial on geometric baby values, compute gcds, and perform one linear recovery when a product gcd is full; its precondition excludes exact modular cross-matches. Algorithm 4.2 checks tagged global matches before removing them. Its published consumer is scoped to prime/semiprime inputs and geometric queries, so it is not itself a citation for B's arbitrary-list/general-composite theorem. B's broader correctness is proved above. No exhaustive historical priority claim is made. [Harvey, §2.2 and Algorithms 4.1–4.2](https://arxiv.org/html/2010.05450v1).

The resolved bottleneck is full-gcd localization *conditional on a proper cross-edge*, including exact equalities and repeated prime factors. The unresolved work is acquisition of such an edge within a better total budget. Replacing a prefactored-leaf condition by a separating-edge condition changes the sufficient input promise; it does not eliminate the original promise without a generator.

**Precise obligation for an oblique construction.** Suppose a proposed finite, `N`-only routine produces coefficients and domains for grids

```text
Delta(i,j) = b + C i + D j = (b+C i) - (-D j),
```

or produces other explicit lists with a comparably priced residue evaluator. For each prime divisor `p|N`, let `L_p` be its zero incidence set on the *same tagged edge domain*. For `N=pq`, `p!=q`, B's promise is exactly

```text
L_p symmetric-difference L_q is nonempty.                    (C1)
```

Requiring each `L_p` to be nonempty is weaker. Even putting a witness in `L_p intersection L_q` supplies only a full equality. An ordinary positive prime cover for `N` can fail completely: `S={2N}`, `T={N}` covers every prime divisor of `N`, yet its only difference has gcd `N`, and normalization leaves only the excluded equality. This symbolic family establishes nonimplication, not a complexity lower bound.

For general `N=product p^e_p`, the exact condition is

```text
(union over p|N of L_p) \ (intersection over p|N of L_(p^e_p))
is nonempty.                                               (C2)
```

This captures partial valuations even when `N` is a prime power. These incidence sets are proof objects, not values the algorithm is allowed to acquire from hidden factors. The generator must prove (C1)/(C2) through its explicit coefficients and domain, or provide a separately justified and paid treatment of excluded input families.

A reviewable next proposal must supply the actual coefficient-generation computation; its output widths, tuple count and residue-evaluation cost; a proof that its nonzero modular lines have the required unequal incidence (including coefficient degeneracies); and an all-input deterministic guarantee or a quantified per-input randomized guarantee with paid failures/restarts. Multiple grids add their generation and list costs. A short symbolic description or favorable infinite sequence of cover sizes is not uniform acquisition. To claim an improvement, compare the full acquisition-plus-consumer cost with a named baseline in the same deterministic, expected-time, or heuristic model. This report establishes no such improvement.

**Next decisive work.** The parent can retain B as an already available consumer and reject A at its coefficient/table cost gate. The next useful artifact is a specific oblique coefficient routine with a symbolic separation proof and full bit budget. A proof that its entire selected edge domain consists only of units and exact zeros would immediately reject that routine. No numerical experiment is selected, and no general rank-two or factoring lower bound follows from this review.
