# W030 review: digit-cut product recursion and aggregate evaluators

2026-10-08 local / 2026-10-09 UTC. **Accept the integer digit-cut identity, the label absorption, and the fixed-carry terminal product algorithm, with the implementation prices below. On the imported short rectangle this recursion reproduces the explicit pair count. No aggregate evaluator was found that beats that count for the residual digit kernel. Verified complete factoring improvement: NONE.** The conditional balanced one-sixth bookkeeping target is not an algorithm.

## Provenance and boundary

Two earlier delegated rounds produced no mathematics. Both terminated with the provider summary "Claude gave up after repeated API errors":

- `node:delegated-task:command%3Amcp%3A662deaf0-7cd2-44c1-ba36-11987049a724%3Adelegate-task%3Afactoring-w030-digit-kernel-opus-r1`
- `node:delegated-task:command%3Amcp%3A662deaf0-7cd2-44c1-ba36-11987049a724%3Adelegate-task%3Afactoring-w030-digit-kernel-opus-r2`

No assigned report or evidence directory existed from either round. Nothing from them is adopted. This round does not retry a provider and does not delegate.

The frozen continuation is `research/findings/W030-digit-cut-consumer.md`, SHA-256 `2966f47629b57e38bd890e47d7bd1380a33af818d4ad99dbc01c7626412f7c51`. The kernel statement is `research/hypotheses/W030.md`, SHA-256 `7d854fd882fab97e173e0bdcd9a48e20030cd1f402e87258fd9d714c9c55f3d8`, sections 1–5. Lines 172–180 of that file are a later status banner. They name a root-table disposition and an unbalanced-cost note. The unbalanced note was not opened. This review does not use it and does not confirm it.

Square-class coverage, Hensel acquisition, the uncarried height bound, and the W024 low-digit filter remain the live root-representation audit's responsibility. They are imported only as the supplied lists and the congruence interface below. If that interface fails, the injectivity step fails with it. The convolution identity itself is a statement about digit strings.

The [full brief](W030-digit-kernel-review-evidence/full-brief.txt), [input manifest](W030-digit-kernel-review-evidence/input-manifest.json), [read scope](W030-digit-kernel-review-evidence/method-and-read-scope.json), and [prior-art scope](W030-digit-kernel-review-evidence/prior-art-scope.md) delimit the round. The parent remains the principal researcher.

## 1. The cut identity is exact

Let \(\ell\ge 2\) be an integer, \(L\ge 0\), and let \(a,b\) be integers whose canonical base-\(\ell\) digits \(a_i,b_j\in\{0,\ldots,\ell-1\}\) vanish for all indices \(\ge L\). Define

\[
R_L(a,b)=\sum_{i\ge 0,\,j\ge 0,\,i+j<L}a_ib_j\,\ell^{i+j},
\]

and \(R_0=0\). Missing digits are zero. Digits of index \(\ge L\) never enter \(R_L\).

Fix an integer \(h\) with \(0\le 2h\le L\) and set \(B=\ell^h\). Write \(a=a_0+Ba_1\) and \(b=b_0+Bb_1\) with \(0\le a_0,b_0<B\). Thus \(a_0,b_0\) are exactly the low \(h\) digits, and \(a_1,b_1\) are the remaining digits, of which there are at most \(L-h\).

**Proposition.** Over \(\mathbb Z\),

\[
R_L(a,b)=a_0b_0+B\,R_{L-h}(a_1,b_0)+B\,R_{L-h}(a_0,b_1)+B^2\,R_{L-2h}(a_1,b_1).
\]

The inputs of each \(R\) on the right are zero-padded to the indicated precision. If an input has more than that many digits, only pairs whose indices sum to less than the precision occur.

**Proof.** Partition the pairs \((i,j)\) with \(i+j<L\).

- Low/low: \(0\le i<h\) and \(0\le j<h\). Then \(i+j\le 2h-2<L\), so every such pair survives in \(R_L\). Their contribution is \(\sum_{i<h,\,j<h}a_ib_j\ell^{i+j}=a_0b_0\), the full integer product. This is not \(R_h(a_0,b_0)\). The truncated sum \(R_h\) drops pairs with \(i+j\ge h\), and those pairs still satisfy \(i+j<L\). Replacing \(a_0b_0\) by \(R_h(a_0,b_0)\) is a different integer whenever \(h\ge 2\) and both low blocks use a digit at least \(1\) in positions that add to at least \(h\).
- High/low: \(i\ge h\), \(j<h\), and \(i+j<L\). Set \(t=i-h\). The contribution is \(B\sum a_{h+t}b_j\ell^{t+j}\), summed over \(t+j<L-h\) and \(j<h\). Zero-padding \(b_0\) to precision \(L-h\) makes this exactly \(B\,R_{L-h}(a_1,b_0)\). Every digit of \(a_1\), including those of index \(\ge L-2h\), is eligible here: the top original digit \(i=L-1\) pairs with \(j=0\).
- Low/high: symmetric, equal to \(B\,R_{L-h}(a_0,b_1)\).
- High/high: \(i\ge h\), \(j\ge h\), and \(i+j<L\). Set \(t=i-h\) and \(s=j-h\). Then \(t+s<L-2h\), and the contribution is \(B^2 R_{L-2h}(a_1,b_1)\). When \(L=2h\) this region is empty, since \(i+j\ge L\), and \(R_0=0\).

The four regions are disjoint and cover every surviving pair. Pairs with \(i+j\ge L\) appear in none of them. Each surviving pair appears once. \(\square\)

Two truncation facts follow from the same partition.

The residual \(R_{L-2h}(a_1,b_1)\) uses only digits \(t,s<L-2h\) of \(a_1,b_1\). Those are the original digits in the half-open index interval \([h,L-h)\). Digits in \([L-h,L)\) are absent from the residual. They are present in the row-only or column-only term: original index \(L-1\) survives against the other factor's digit \(0\). Deleting them before the label stage changes \(R_L\) by a non-multiple of a general \(Q=\ell^L\). The continuation's phrase "high inputs truncated to those \(L-2h\) digits" is exact for the residual kernel and false if applied to the stored inputs of the two middle terms.

The middle terms are truncated convolutions, not full products \(a_1b_0\) and \(a_0b_1\), except in special cases such as \(h=1\), where the short factor has one digit and every index pair inside \(R_{L-1}\) survives. Substituting the full integer \(a_1b_1\) for \(R_{L-2h}(a_1,b_1)\) restores pairs with original index sum \(\ge L\).

The identity is for canonical digits in \(\{0,\ldots,\ell-1\}\). Unnormalized digits make the four-term split a different sum from \(R_L\). The case \(h=0\) is the identity \(R_L=R_L\) and is not a split. The case \(L=0\) is \(0=0\).

## 2. Labels, signs, and the changed base

Let \(Q=\ell^L\), let \(\sigma\in\{+1,-1\}\) be constant on the family being split, and let \(u,v,\tau\in\mathbb Z\). The leaf exponent is the imported integer

\[
E=u+Nv-\sigma R_L(a,b)-Q\tau.
\]

Substitute the proposition:

\[
\begin{aligned}
E&=u-\sigma B\,R_{L-h}(a_1,b_0)\\
&\quad+Nv-\sigma a_0b_0-\sigma B\,R_{L-h}(a_0,b_1)-Q\tau\\
&\quad-\sigma B^2 R_{L-2h}(a_1,b_1).
\end{aligned}
\]

Inside one Cartesian bucket of fixed \((a_0,b_0)\), the first line depends on the row and on the column prefix \(b_0\); the second depends on the column, the carry, and the row prefix \(a_0\); the constant \(-\sigma a_0b_0\) may sit in either line. The third line is the residual. Therefore, in \((\mathbb Z/N\mathbb Z)[\alpha^{\pm 1}]\) after \(\alpha\) has been inverted,

\[
\alpha^E=\alpha^{\rho(u;b_0)}\,\alpha^{\kappa(v,\tau;a_0)}\,(\alpha^{B^2})^{-\sigma R_{L-2h}(a_1',b_1')},
\]

where \(a_1',b_1'\) are the truncations of the previous paragraph and \(\rho,\kappa\) are the two displayed integer lines. The integer radix remains \(\ell\). The new exponential base is the power \(\alpha^{B^2}\).

If \(\gcd(\alpha,N)=1\), then \(\alpha^{B^2}\) is a unit. One binary exponentiation computes it: the exponent \(B^2=\ell^{2h}\) has \(O(h\log\ell)\) bits. A later power that shares a nontrivial factor with \(N\) is a gcd exit, which is a factor witness, or is \(0\bmod N\), which is the zero-label case in §4. Negative \(v\), negative \(\tau\), and \(\sigma=-1\) change only the integer exponents. Each negative exponent is a positive power of the already inverted unit \(\alpha^{-1}\).

The sign has to be constant on the product being split. The two root signs are two instances of the same recursion. Mixing them inside one bucket makes \(-\sigma R_L\) fail to factor through a single residual base. Signed \(v\) never enters the digit convolution; it enters through the column integer \(Nv\).

Every pair \((u,v)\) has one prefix pair \((a_0,b_0)\). The buckets partition the product. Empty buckets contribute the empty product \(1\). The product of the bucket products is the original product, including the external carry list. Public work that copies list indices is paid separately and does not change the factors.

The carry factor \(\alpha^{-Q\tau}\) stays in \(\kappa\). For \(2h<L\), \(Q/B^2=\ell^{L-2h}>1\), so \(-Q\tau\) is a multiple of \(B^2\) but it is not the value of a residual digit convolution. At \(L=2h\), \(B^2=Q\) and the residual region is empty, so the carry remains a column scalar rather than a revived digit kernel.

## 3. Full-prefix buckets on a short rectangle

Now take \(L\) even, \(h=L/2\), and \(B=\ell^{L/2}\). For the imported top stratum this \(B\) is the stratum modulus \(M_t\), because \(Q=M_t^2\). The residual is \(0\), and

\[
\alpha^E=\alpha^{\rho(u;b_0)}\,\alpha^{\kappa(v,\tau;a_0)}.
\]

**Imported interface, not re-proved here.** In one square class the stored root satisfies \(A_u^2\equiv c u\pmod Q\) with \(c=4N\delta^\epsilon\) a unit modulo \(\ell\), hence modulo \(B\), and \(B_v^2\equiv \delta^{-\epsilon} v\pmod Q\) with the column scale likewise a unit. The root-table audit owns the construction of \(A_u\), \(B_v\), \(c\), and \(\delta\).

**Injectivity.** The same low block \(A_u\bmod B\) forces \(A_u^2\bmod B\) and therefore \(u\bmod B\). An integer interval of cardinality at most \(B\) contains at most one integer in each residue class: the difference of two elements is at most \(B-1\). The same statement holds for \(v\). On a domain that is a union of \(s\) such intervals, each prefix contains at most \(s\) rows or columns. Positive and negative \(v\), split into two intervals of cardinality at most \(B\), contribute at most two columns per prefix, or one per piece after the split.

The continuation's balanced hypothesis is this regime: \(U\) and \(V\) are on the scale \(\sqrt M\), while \(B=M\), so both unsplit intervals eventually have cardinality less than \(B\). The imported rectangle stated in the root review under way, \(U<M\) and \(V<M\), already gives cardinality \(<B\) at the top stratum. Under that hypothesis every occupied terminal prefix contains one coordinate. A Cartesian pair of occupied prefixes contains one pair \((u,v)\).

The low-digit filter deletes some residue blocks. Deletion preserves injectivity. It does not identify two distinct coordinates that share a long prefix. After the filter, the nonempty terminal buckets are in bijection with the surviving pairs. Their number is the filtered explicit-pair count. No sublinear bound on that count is supplied or assumed.

Earlier prefixes, with \(B=\ell^h\) still dividing \(Q\), have the same congruence and a weaker count. An interval of cardinality \(U\) meets one residue class modulo \(B\) in at most \(\lfloor(U-1)/B\rfloor+1\) points. The number of occupied row prefixes is at most \(\min(U_c,B)\), and likewise for columns. The number of nonempty Cartesian bucket pairs is therefore at most \(\min(U_c,B)\min(V_c,B)\), times the constant number of square and sign classes. Writing one row label into each paired column bucket, and one column label into each paired row bucket, performs at most

\[
O\bigl(U_c\min(V_c,B)+V_c\min(U_c,B)\bigr)
\]

label formations, times the bit cost of a length-\(O(L)\) digit convolution and one exponentiation. These are upper bounds on this indexing. They do not assert that every prefix pair is occupied, and they are not a lower bound on every algorithm that might use the same cut.

At the terminal value \(B\ge\max(U_c,V_c)\) the same upper bound equals the pair count already obtained by injectivity. Inside that rectangle the bound does not improve on explicit pairs.

## 4. The terminal product, priced in \(\mathbb Z/N\mathbb Z\)

Fix one bucket, one sign, and one carry, and suppose the residual vanishes. The bucket product is the scalar

\[
\Pi=\prod_{i=1}^{n}\prod_{j=1}^{m}(1-r_is_j)\in\mathbb Z/N\mathbb Z,
\]

with the labels \(r_i,s_j\) already reduced modulo \(N\).

**Algorithm.** Compute \(g_j=\gcd(s_j,N)\). If \(1<g_j<N\), emit \(g_j\) and stop; that is a factor. If \(g_j=N\), then \(s_j\equiv 0\) and every factor on that column is \(1\). If \(g_j=1\), invert \(s_j\) by the extended gcd. Build the monic polynomial \(P(Y)=\prod_i(Y-r_i)\) by a subproduct tree, evaluate it at the inverted units by a remainder tree, and return

\[
\Pi=\prod_{s_j\in(\mathbb Z/N\mathbb Z)^\times} s_j^{\,n}\,P(s_j^{-1}).
\]

The symmetric form inverts the row labels instead. Zero columns are omitted. A nonunit on the inverted side has already exited through the gcd.

**Ring hypothesis.** Division by a monic polynomial uses no coefficient inverse: the leading term of the divisor is \(1\), and the usual remainder recurrence stays inside the coefficient ring. Every node polynomial \(\prod(Y-s)\) is monic. Repeated evaluation points are allowed, because the tree never inverts a difference of nodes. The algorithm uses the composite ring \(\mathbb Z/N\mathbb Z\) directly. It does not pass to a field, does not invert an arbitrary element, and does not approximate.

**Cost, fixed carry.** The product tree and the remainder tree use \(\widetilde O(n+m)\) additions and multiplications in \(\mathbb Z/N\mathbb Z\), in the sense that hides only logarithmic factors in \(n+m\). Each multiplication modulo \(N\) is paid at ordinary integer-multiplication cost. The extended gcds are \(O(n+m)\) additional integer gcds of \(O(\log N)\)-bit inputs. The output is one residue modulo \(N\), not the list of \(nm\) factors.

**Localization.** The remainder stage already holds the column aggregates \(C_j=\prod_i(1-r_is_j)\). One nontrivial \(\gcd(C_j,N)\) selects a column. The row product tree, or a direct scan of that column, selects one row. The stored row, column, and carry indices then recover the integer exponent from the defining formula. The extra work is the same \(\widetilde O(n+m)\) order for one leaf, plus the tags. Tags are one index per list entry, not one record per pair. This localization is paid. It is not a second hidden pass over all pairs.

**Several carries.** Let the carries form a progression of length \(T\) with unit stride \(\gamma=\alpha^{-Q}\), and absorb a fixed offset into the column label. Here \(m\) counts the columns that survived the gcd screen. The scalar is \(\prod_{t<T}\prod_{i,j}(1-r_i(s_j\gamma^t))\). If \(\gcd(\gamma,N)\) is nontrivial, stop with that factor. Otherwise the explicit prefactor \(\bigl(\prod_j s_j\bigr)^{nT}\gamma^{nmT(T-1)/2}\) is \(O(m)\) multiplications and one exponentiation.

The remaining product is \(\prod_{j,t}P(s_j^{-1}\gamma^{-t})\). For an integer block length \(b\in[1,T]\), write each complete index as \(t=qb+r\). For each unit \(c\), the scaled polynomial \(P_c(w)=\prod_i(w-r_ic)\) is monic of degree \(n\), and

\[
\prod_{r<b}P(w\gamma^{-r})=\gamma^{\mu}\prod_{r<b}P_{\gamma^{r}}(w)
\]

with an explicit integer \(\mu\). The inner product \(F=\prod_{r<b}P_{\gamma^{r}}\) is monic of degree \(nb\). Building the linear factors and the product tree costs \(\widetilde O(nb)\) ring operations. A remainder tree evaluates this same \(F\) at the \(m\lfloor T/b\rfloor\) points of the complete giant steps. The final block, of length \(T\bmod b\), has its own monic product of that length and \(m\) further evaluations. Every divisor in these trees is monic. The point count is \(m\lceil T/b\rceil\), so the block cost is

\[
\min_{1\le b\le T}\widetilde O\bigl(nb+m\lceil T/b\rceil\bigr),
\]

which is \(\widetilde O(\sqrt{nmT}+n+m)\). The endpoint \(b=1\) is ordinary multipoint at all \(mT\) points, \(\widetilde O(n+mT)\). A \(T\)-fold call to the fixed-carry routine is the same order as that endpoint. This is not \(\widetilde O(n+m+T)\): a single degree-\(n\) polynomial at one geometric orbit of length \(T\) still has the baby-step cost above, and no source in §6 removes the remaining square root.

One bad leaf is recovered from the retained giant-block values by a gcd screen and one descent through \(F\) and \(P\). That descent is inside the same soft bound. Column, block, and row indices are the tags.

On a bucket with large \(n\) and \(m\), this is cheaper than materializing \(nm\) anchors and invoking the imported consumer, whose envelope is \(\widetilde O(nm+\sqrt{nmT})\). On singleton buckets, \(n=m=1\), the same bound is \(\widetilde O(\sqrt T)\) per pair. Applied independently to \(K\) pairs, that is \(\widetilde O(K\sqrt T)\). Forming the \(K\) anchors and using the imported consumer instead costs \(\widetilde O(K+\sqrt{KT})\), which is the better of the two singleton compositions. The continuation's fixed-carry claim does not include this \(T\)-dependence, and the fixed-carry restriction is the right reading of the sentence that was checked.

The square-root carry bound uses separability of \(r_is_j\) in an essential way. It does not evaluate a residual digit convolution. The digit-kernel bottleneck begins when that convolution is still present.

## 5. What the balanced recursion costs

Combine §3 and §4. On a rectangle with interval cardinality at most \(B=\ell^{L/2}\), each terminal bucket is a single pair. The monic evaluator then does constant work per surviving pair per fixed carry. Summed, that is explicit pair processing. The \(\widetilde O(|I|+|J|)\) bound is real and, on these buckets, has both lengths equal to \(1\).

A direct recursion that stops only when the residual vanishes therefore has one terminal call per surviving pair. The continuation's rejection of this full-prefix route is accepted. The rejection is a cost account for this recursion. It is not a lower bound for an algorithm that processes many buckets together, uses further structure of the root tables, or stops at positive residual precision and evaluates the residual by a different method.

A one-digit recursion makes the same point with an explicit branching upper bound. Take \(h=1\) and \(B=\ell\). One step creates at most \(\ell^2\) residual instances of precision \(L-2\). Under full occupancy the list lengths are about \(U/\ell\) and \(V/\ell\); occupancy is not proved, so this is only a shape of the §3 upper bound. Label formation at that step is \(O(\ell(U+V)L)\) short digit operations. After \(t\) steps, while \(\ell^t\le V\), full occupancy charges on the order of \(U\ell^t\) row labels, which is the §3 bound at prefix modulus \(\ell^t\). The lists reach size \(1\) near \(t=\log_\ell U\), while the residual precision is still \(L-2\log_\ell U\). In the balanced scaling \(U\asymp V\asymp\ell^{L/4}\) this happens with about \(L/2\) digits left and with \(UV\) singleton instances. Independent bucket calls do not cancel that branching. Shared residual digit vectors across different prefixes do not by themselves merge the calls: the row sets of distinct prefixes are disjoint, and the labels depend on both prefixes.

## 6. Prior art checked, and the priced weaker bound

The operation asked for is one scalar in \(\mathbb Z/N\mathbb Z\),

\[
\prod_{i,j}\Bigl(1-r_is_j\prod_{k=0}^{L-1}X_{j,k}^{\,a_{i,k}}\Bigr),
\]

optionally also multiplied over a carry progression. The row digits satisfy \(0\le a_{i,k}<\ell\). The column coordinates are not an arbitrary grid. They are the triangular family

\[
X_{j,0}=\alpha^{-\sigma B_j},\qquad
X_{j,k+1}=X_{j,k}^{\,\ell}\,(\alpha^{\sigma Q})^{b_{j,L-k-1}},
\]

equivalently \(X_{j,k}=\alpha^{-\sigma s_{j,k}}\) with \(s_{j,k}=\ell^k(B_j\bmod \ell^{L-k})\). The output is the scalar, localization is paid, inverses are only extended gcds against \(N\), and a theorem that receives a dense coefficient tensor as an oracle is not applied until that tensor has been built and paid for.

The sources actually opened, and the hypothesis that fails, are listed in the [prior-art scope](W030-digit-kernel-review-evidence/prior-art-scope.md). The conclusions are these.

**Separable product, priced.** Section 4 is the standard monic remainder tree, plus a block decomposition of the carry orbit. Van der Hoeven and Lecerf, in the introduction of "Fast multivariate multi-point evaluation revisited" (Journal of Complexity, 2020), attribute the univariate \(\widetilde O\) bound to remainder trees as in von zur Gathen–Gerhard, Modern Computer Algebra, Chapter 10. The ring proof in §4 was checked directly and does not depend on reopening that book. Geometric-progression evaluation (Bostan–Schost, Journal of Complexity 2005, as cited there) improves a logarithm inside one progression; the square-root carry bound in §4 is a coarser block decomposition of that orbit, not a citation of a faster closed form. The resulting theorem beats \(nm\) pair operations when one bucket has many rows and many columns. It also beats an explicit-anchor carry search on that same single bucket when the anchor count \(nm\) dominates \(\sqrt{nmT}\). On the balanced terminal split the buckets are singletons, and the imported anchor consumer is then the better carry composition.

**Dense multivariate multipoint.** Kedlaya–Umans, SIAM J. Comput. 2011, Corollary 4.3, as quoted by van der Hoeven–Lecerf §1.1, evaluates an \(m\)-variate polynomial of partial degree \(<d\), given as input, at \(N\) points over \(\mathbb Z/r\mathbb Z\), in \((d^m+N)^{1+\delta}\) bit operations, for \(m\le d^{o(1)}\) and \(d\) large, in the RAM model. Van der Hoeven–Lecerf carry related bounds onto a multitape Turing machine and take the polynomial in recursive dense representation. Bhargava–Ghosh–Guo–Kumar–Umans (arXiv:2205.00342) state the finite-field version for every \(m\), still from a coefficient vector, in \((d^m+N)^{1+o(1)}\operatorname{poly}(m,d,\log|\mathbb F|)\). Bhargava–Ghosh–Kumar–Mohapatra (arXiv:2111.07572) likewise take a list of coefficients, over fields of small characteristic. Nüsken–Ziegler (arXiv:cs/0403022) take the \(n^2\) coefficients of one bivariate polynomial.

For a block of \(b\) rows the expanded block polynomial has \(L+1\) variables and partial degrees up to \(b(\ell-1)\) and \(b\). Supplying its dense box writes

\[
(b+1)\bigl((\ell-1)b+1\bigr)^L
\]

coefficients. For \(b=N^\eta\) with \(\eta>0\), \(Q=\ell^L=M^2\), and \(\ell\) polylogarithmic in \(N\), the logarithm of this box is superpolynomial in \(\log N\). The theorems then charge at least that box. They do not read the product-of-binomials circuit of size \(O(bL)\) in place of the coefficients. The arbitrary-coefficient gate is exactly the expansion this kernel is trying to avoid. The same gate disqualifies an appeal to those theorems at residual precision \(\lambda=L-2h\) until the residual box of size about \((( \ell-1)n_b)^{\lambda}\) has been built.

**Cartesian-grid norms and resultants.** If the evaluation points are a full Cartesian product and the polynomial is already dense, univariate evaluation can proceed one coordinate at a time. Van der Hoeven–Lecerf record that reduction. The column set here is a set of \(V\) points on the triangular curve above, not a grid of cardinality \(\ell^L=Q\). Evaluating on that full grid would be larger than the pair count. A univariate resultant computes the separable scalar of §4 and has the same soft-linear price; it is not a second algorithm. A multivariate resultant whose Bézout bound is the dense box recreates that box. No low-degree grid norm was found whose hypotheses are the digit lists, the triangular coordinates, the ring \(\mathbb Z/N\mathbb Z\), and a scalar output cheaper than explicit pairs.

**Sparse multipoint.** A \(t\)-term expansion can be evaluated at one column by \(O(tL)\) arithmetic, and at \(V\) columns by \(O(VtL)\) arithmetic, once the terms are known. The subset expansion is an algorithm that visits \(2^b\) subsets even if later terms coalesce. Its polynomial range is \(b=O(\log N)\), which removes only a logarithmic factor in the number of blocks. Coalescence over \(\mathbb Z/N\mathbb Z\) is not guaranteed, and the checked sparse-interpolation theorems (van der Hoeven–Lecerf, arXiv:2312.17664, modular black box to sparse output) recover terms rather than evaluate this product. No theorem in the scope supplies a support \(t=o(b)\) for these root digits. The quantities \(2^b\) and the dense-box cardinality price those two implementations. They are not support-size lower bounds, and they are not circuit lower bounds.

**Low rank.** The exponent matrix \(C_{ij}=\ell^{i+j}\) for \(i+j<L\), and \(0\) otherwise, is triangular of rank \(L\) after reversing columns, with diagonal \(\ell^{L-1}\). A sum of \(r\) separable exponent features produces an \(r\)-variable monomial. For arbitrary digit vectors, \(r\ge L\). That linear-algebra fact is the statement already in W030 §5. It does not price a product circuit, and the root tables need not realize arbitrary vectors. A rank-\(1\) exponent is the separable product of §4, which is priced and which the terminal cut reaches only by creating singleton buckets. Rank-\(L\) tensor arithmetic speeds one convolution. It does not multiply the leaf factors together.

One algebraic rewriting was checked and does not reduce the dimension. The recurrence gives \(X_k=X_0^{\ell^k}\delta_k(v)\) with a column-digit correction \(\delta_k\). The product of powers is \(X_0^{A_u}\) times \(\alpha\) to a second bilinear form in the high digits of the column and the digits of the row. That second form is the carried complement of \(R_L\). It is another truncated digit convolution of the same kind. Substituting the single group element \(X_0\) does not produce a univariate polynomial of degree \(\operatorname{poly}(\log N)\).

**Neighbor in this project, different input.** The W021 quadratic-interval product, reviewed in `W021-quadratic-product-review.md`, builds a dense polynomial of size \(\Theta(b^3)\) for \(\prod_i(1-\alpha^{Ai^2+Di+C})\) and evaluates it by the same dense multipoint theorems. Its input is one quadratic along an interval. It is not a product over two digit tables, and its \(L^{3/4+\varepsilon}\) bound does not apply to the kernel in this review. The linear case of that review, a \(q\)-Pochhammer along a geometric progression, is likewise one sequence.

**Approximate and numerical multipoint.** Bhargava–Ghosh–Guo–Kumar–Umans and Moroz, as described in arXiv:2304.01191, give numerical or rational-reconstruction algorithms. They are outside the exact composite-ring requirement and were not used.

**Scope limit.** The search covered the remainder-tree product, geometric evaluation, the dense multipoint theorems named above, Cartesian and resultant formulations, sparse evaluation and sparse interpolation, and low-rank bilinear factorizations of the exponent. It did not survey factoring algorithms at large, and it did not attempt a new construction. Absence from this list is not an impossibility proof.

## 7. Column setup and the block polynomial

The continuation's column recurrence is the same identity as the kernel's coordinate definition. With \(s_i=\ell^i(B_v\bmod\ell^{L-i})\) and \(X_i=\alpha^{-\sigma s_i}\),

\[
\ell s_i=s_{i+1}+Q\,b_{v,L-i-1},
\]

because \(B_v\bmod\ell^{L-i}\) splits off the digit \(b_{v,L-i-1}\). Therefore

\[
X_i^{\,\ell}\,(\alpha^{\sigma Q})^{b_{v,L-i-1}}=\alpha^{-\sigma s_{i+1}}=X_{i+1}.
\]

The base case \(X_0=\alpha^{-\sigma B_v}\) is one modular exponentiation, \(O(L\log\ell)\) multiplications, or a Horner sweep after \(\alpha^{-\sigma}\) is known. Each of the \(L-1\) recurrence steps is an \(\ell\)-th power and one multiplication by a precomputed digit power. Precomputing \(\alpha^{\sigma Q}\) and its \(\ell\) small powers is global. The per-column cost is \(O(L\log\ell)\) multiplications in \(\mathbb Z/N\mathbb Z\). Both signs are two passes. No \(\ell\)-th root modulo \(N\) is required. This builds coordinates. It does not evaluate the product. Relative to a pair loop, the coordinate stage is the smaller term, as the continuation says.

The block identity

\[
F_I(Y,X_0,\ldots,X_{L-1})=\prod_{u\in I}\Bigl(1-\alpha^u Y\prod_i X_i^{a_{u,i}}\Bigr)
\]

is the product of the leaf factors after substituting \(X_i=X_i(v)\) and \(Y=\alpha^{Nv-Q\tau}\). It holds in \(\mathbb Z/N\mathbb Z\) because evaluation is a ring homomorphism and only \(\alpha\) is inverted. It is the definition of the product, not an algorithm for building the coefficients.

If a block fixes the lowest row digit, the common power of \(X_0\) moves into \(Y\) and one variable disappears. The resulting dense box still has \(L\) growing variables and the same superpolynomial logarithm. Removing one coordinate does not change that implementation's cost class. No asymptotic saving follows.

## 8. Disposition

The checked deliverable is an exact cut of \(R_L\), exact separation of the three nonresidual terms when the other side's prefix is fixed, a unit base \(\alpha^{B^2}\), and a terminal monic evaluator whose fixed-carry cost is soft-linear in the two bucket lengths. On one separable bucket, a carry progression of length \(T\) costs \(\min_b\widetilde O(nb+m\lceil T/b\rceil)=\widetilde O(\sqrt{nmT}+n+m)\). After the balanced cut has produced \(K\) singleton anchors, the imported envelope \(\widetilde O(K+\sqrt{KT})\) is the better carry composition. Full-prefix terminal buckets on the short balanced rectangle are singletons, so this recursion pays the surviving pair count. The earlier-prefix counts are upper bounds only. Dense-box and subset-enumeration figures price those implementations only.

No theorem in the searched scope evaluates the residual product

\[
\prod_{p,q}\prod_{u\in I_p}\prod_{v\in J_q}
\Bigl(1-r_u^{(q)}s_v^{(p)}(\alpha^{B^2})^{-\sigma R_{\lambda}(a'(u),b'(v))}\Bigr)
\]

as one scalar in \(\mathbb Z/N\mathbb Z\), with localization paid, in \(o(U_cV_c)\) ring operations on this rectangle. Here \(\lambda>0\), the labels depend on both bucket indices, and the digit vectors are the supplied root digits. That joint product is the unsolved operation. A construction that computes it, or a different consumer with a proved cost below the explicit pair count, would change this disposition. Another certificate of the cut identity would not.

The existing explicit consumer remains \(\widetilde O(K+\sqrt{KT})\) with \(K\) the number of materialized anchors. This review supplies no replacement. The balanced substitution that would turn \(\widetilde O(U+V+\sqrt{UVT})\) into an exponent \(1/6\) stays bookkeeping. It is not claimed, and the unbalanced-cost note was not part of this audit.

**Disposition: rejected as a route past the explicit pair term. The residual aggregate product is unsolved, not impossible.**

**Verified complete factoring improvement: NONE.**

This was a symbolic audit. No numerical certificate, solver run, Lean build, installation, commit, or delegation was performed. Only this report and its evidence directory were written.
