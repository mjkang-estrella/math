# Unaccepted independent Grok constraint proposals

Raw initial report preserved; coordinator and independent mathematical review
are required. Tuple testing is not relation generation; finite degree/MI tests
are not universal lower bounds. No experiment or claimed cost accepted.

Four coordinate-aware hypotheses follow. No experiment was run. The baseline for one full scalar on an ordinary prime-field curve of prime order \(q\neq p\), with only the negation automorphism, is negation-rho: about \(\sqrt{\pi q/2}/\sqrt{2}\) group operations. Shoup’s generic bound does not rule these out. Naive Semaev point-decomposition should be treated as already losing to that baseline.

## Baseline and scope

Single target, scalar uniform in \(\{0,\ldots,q-1\}\), preprocessing counted in full. Negation-rho is the reference: Pollard’s walk has expectation \(\sqrt{\pi q/2}\) on a set of size \(q\), and a branchless negation quotient cuts the iteration count by a factor extremely close to \(\sqrt{2}\) (Bernstein–Lange–Schwabe, ePrint 2011/003). Two-grumpy-giants changes the leading constant only (Bernstein–Lange, ANTS X, Open Book Series 1, 2013). Shoup’s generic-group bound is \(\Omega(\sqrt{q})\) group operations for constant success probability (Eurocrypt 1997, https://www.shoup.net/papers/dlbounds1.pdf); it does not apply to coordinate algorithms.

Prime-field index calculus has no demonstrated win over that reference. Galbraith–Gaudry (ePrint 2015/1022; Galbraith, ellipticnews, 7 Apr 2016) record that Gaudry–Diem sub-square-root results need an extension degree, and that Petit–Kosters–Messeng (PKC 2016) solved a 22-bit prime-field instance in about 5000 seconds against baby-step/giant-step in 0.01 seconds. Yokoyama–Yasuda–Takahashi–Kogure (J. Math. Cryptol. 14, 2020, doi:10.1515/jmc-2019-0029) show that Gröbner solution of the naive summation-polynomial point-decomposition ideal cannot beat generic methods, under a statistical model of that ideal. McGuire–Mueller (ePrint 2017/1262) reach the same practical conclusion for their fastest prime-field variant, which avoids both Gröbner bases and summation polynomials. Delaplace–May (J. Math. Cryptol. 2020, doi:10.1515/jmc-2019-0025) is an \(\mathbb{F}_{p^2}\) result (\(p^{1.314}\) against a square-root of size \(p\)), not a prime-field baseline.

Assumptions for every card: \(E/\mathbb{F}_p\) ordinary, \(\#E(\mathbb{F}_p)=q\) prime, \(q\neq p\), \(\gcd(q,p-1)=1\), no usable endomorphism beyond \(\{\pm 1\}\). One target. Costs below are field operations, elimination, memory, failed branches, and a final scalar multiplication check. Finite widths do not prove asymptotics.

These are closed for this scope, and are not proposed as cards: bit-peeling into a smaller discrete log (multiplication by 2 is bijective on a prime-order group); \(\mathbb{Q}_p\)-valued heights or formal logarithms of prime-to-\(p\) torsion (a torsion-free quadratic height vanishes); an additive projection \(\pi(P+Q)=\pi(P)+\pi(Q)\) into \((\mathbb{F}_p,+)\) (that is the anomalous case \(q=p\)); rational small-degree isogenies (a prime-order group has no rational kernel); Ritt/Pakovich commutation with the Lattès doubling map (no extra rational symmetry); Q-independent SAT clauses on a proper subset of scalar bits (every prefix extends for some target, and backward ladder width is exactly 2, so \(2^n\) leaves).

## Card 1 — Preimage degree of Shipsey’s net block

**Mechanism.** For \(\gcd(q,p-1)=1\), Lauter–Stange (arXiv:0803.0728, Theorem 3.1) give a perfectly periodic net value \(\widetilde{W}(n)=\phi([n]G)\) computable from the point alone. The eight-term block centered at the unknown scalar is therefore public: it is \(\phi(Q+[j]G)\) for \(j\in\{-3,\ldots,4\}\), each \(\phi\) one net evaluation at a known index (their Theorem 4.1). Shipsey’s block step, as quoted there, is the explicit rational map
\[
\begin{aligned}
W(2i-1)&=W(i+1)W(i-1)^3-W(i-2)W(i)^3,\\
W(2i)&=\bigl(W(i)W(i+2)W(i-1)^2-W(i)W(i-2)W(i+1)^2\bigr)/W(2).
\end{aligned}
\]
The discrete log is the unknown addition-chain index taking the public block at 1 to the public block at \(k\). Theorem 4.4 reduces non-periodic width-3 net discrete log to one \(\mathbb{F}_p^\*\) discrete log, but only when the non-periodic terms are given. The periodic terms are the ones we can compute; the missing scale is \(\phi(G)^{k^2-1}\).

**Structural saving.** Invert one block-doubling as a constant-size elimination (8 coordinates, degree 3), then compose. If the eliminant degree in a block coordinate stays bounded, or grows as \(2^{ct}\) with \(c<1\), a depth-\(t\) inversion is cheaper than enumerating bits. Unique rational preimages (\(d<\sqrt{2}\) on average) would be polynomial time. Degree exactly \(2^t\) reproduces brute force on the bits and loses to negation-rho.

**Accounting.** Circuit construction: \(O(1)\) rational operations per doubling, composed \(t\) times symbolically. Width: monomial count of the eliminant after eliminating the intermediate block. Branching: number of \(\mathbb{F}_p\)-preimages of one doubling on random blocks. Preprocessing: the eight public \(\phi\)-values, \(O(\log p)\) net operations, independent of any factor base. Verification: one scalar multiplication.

**Gain.** Open. Only \(c<1\) changes the exponent. Degree \(2^t\) is a loss.

**Prior art.** Shipsey’s double-and-add, Stange’s nets, and Lauter–Stange’s subexponential equivalence are known. They do not record the degree of the composed preimage. Summation polynomials are the eliminants of a different chain and have per-variable degree \(2^{m-2}\); this system may be equivalent to those through \(\bigl(W(n-1)W(n+1)\bigr)/W(n)^2=x(G)-x([n]G)\). Novelty is unresolved until the degrees are compared.

**Unsupported assumption.** Composed preimage degree grows strictly slower than \(2^t\).

**Cheapest falsifier.** Over a 20-bit prime, eliminate intermediate blocks for \(t=1,2,3,4\) unknown bits and list total degree and monomial count. Degree sequence \(2,4,8,16\) kills the card. A flat degree through \(t=4\) is the first observation that would justify a larger \(t\).

## Card 2 — Sparse interpolation of one coordinate bit

**Mechanism.** Fix one output bit of \(x([k]G)\), or the Legendre symbol \(\bigl(x([k]G)/p\bigr)\), as a boolean function of the \(n=\lceil\log_2 q\rceil\) scalar bits. Query it on chosen scalars (public group operations) and build the algebraic normal form by the Möbius transform on a subspace, or by sparse interpolation if a term bound \(T\) is guessed.

**Structural saving.** The forward map is an arithmetic circuit with carries, so the ANF is expected to be dense of degree near \(n\). The saving exists only if some fixed coordinate functional has at most \(T\) nonzero monomials with \(T\ll\sqrt{q}\). Preprocessing then costs \(\mathrm{poly}(n,T)\) queries rather than \(2^n\). Online, the stored polynomial is a constraint system in the unknown bits with \(T\) terms; that system still has to be inverted. A linear ANF would invert by linear algebra. A degree-\(d\) ANF with \(d\ge n/2\) does not beat rho even before inversion.

There is no public tweak separate from the scalar, so a Dinur–Shamir cube split (public variables versus secret variables) does not apply. This card is interpolation of a fully secret input, not a cube attack.

**Accounting.** Circuit construction: none beyond the ladder used as a black-box query. Width: \(T\), the number of nonzero Möbius coefficients, and the maximum degree. Branching: \(2^d\) additions inside each cube sum, or one scalar multiplication per interpolation query. Preprocessing: all queries; for one target it counts in full. Verification: evaluate the candidate scalar.

**Gain.** None unless some coordinate bit has \(T\ll q^{1/2}\) on an infinite family. A single \(n=16\) sparse example would not establish that.

**Prior art.** I did not find a prime-field ECDLP paper that measures this ANF. Cube attacks (Dinur–Shamir, ePrint 2008/385) are the neighboring technique and need a tweak/secret split this problem does not have. Folklore algebraic modeling of scalar multiplication is older and usually targets summation polynomials, which is a different system.

**Unsupported assumption.** Some poly-time coordinate functional has ANF support \(T=q^{1/2-\varepsilon}\) with degree \(o(n)\), uniformly in the family.

**Cheapest falsifier.** Full Möbius transform of the least bit of \(x([k]G)\) and of \(\bigl(x([k]G)/p\bigr)\) for every scalar on one curve of order about \(2^{12}\) and one of order about \(2^{16}\). More than \(\sqrt{q}\) terms, or degree \(\ge n-2\), kills the card for those curves. Two sizes are required so a single small-\(n\) accident is not mistaken for a pattern.

## Card 3 — Four-list merge by univariate multipoint evaluation

**Mechanism.** Write the unknown scalar as a sum of four window scalars, each drawn from a list of size \(L\). Merge lists by a Wagner-style tree whose partial test is membership of a field element in a list, batched with the product polynomial \(\prod(X-x_i)\) and univariate multipoint evaluation. Delaplace–May’s \(p^{3/4}\) conditional result over \(\mathbb{F}_{p^2}\) is the shape: their loss comes from bivariate evaluation. Over a prime field the analogous polynomial is univariate, and univariate multipoint evaluation is quasi-linear in the list length.

**Structural saving.** Generic 4-sum in a prime-order group does not beat Shoup, because partial sums still cost group operations and there is no prefix homomorphism. The only coordinate opening is a projection \(\pi\) for which a match on \(\pi(A+B)\) restricts \(\pi\bigl((A+B)+(C+D)\bigr)\). Bit-prefixes of \(x\) do that for integer addition and for XOR. They do it for elliptic addition only if the low bits of \(x(P)\), \(x(Q)\), and \(x(P+Q)\) share mutual information. If they do, list size \(L=q^{1/3}\) and a quasi-linear merge are a \(q^{1/3+o(1)}\) candidate. If they do not, every partial match is a false filter and the tree falls back to a 4-dimensional baby-step search, which is larger than \(\sqrt{q}\).

**Accounting.** Circuit construction: the product tree, \(O(L\log^2 L)\) field operations per list. Width: \(L\), plus the bit-width \(b\) of the partial tag. Branching: candidates surviving each merge level; this is the quantity that must stay near \(L\) rather than \(L^2\). Preprocessing: building four lists, counted once for one target. Verification: one group-law check of the surviving 4-tuple, not an \(x\)-prefix check.

**Gain.** \(q^{1/3+o(1)}\) group-equivalent work only under a prefix law that elliptic addition has given no evidence of. Otherwise a loss against negation-rho.

**Prior art.** Wagner’s 4-list algorithm (CRYPTO 2002) needs an XOR/integer prefix law. Delaplace–May is the elliptic representation attempt and is stated for \(\mathbb{F}_{p^2}\). This card is the prime-field univariate special case of their bottleneck, not a new factor base.

**Unsupported assumption.** The lowest \(b\) bits of \(x(P+Q)\) are determined by the lowest \(b\) bits of \(x(P)\) and \(x(Q)\) often enough that a merge level retains a \(q^{-\varepsilon}\) fraction of pairs.

**Cheapest falsifier.** On one 32-bit prime curve, draw \(10^4\) uniform pairs and estimate mutual information of the lowest 4 and 8 bits of \(x(P)\), \(x(Q)\), and \(x(P+Q)\). Mutual information within sampling error of 0 kills the merge. A large value is only a license to time the product-tree merge at \(L=2^{10}\) and \(L=2^{12}\), not an asymptotic claim.

## Card 4 — Schema search for a unary decomposition tester

**Mechanism.** Keep the relation skeleton fixed and search only the tester. Factor base \(F\) of size \(f\), relations of weight \(m\), linear algebra modulo \(q\). The tester \(T(x_1,\ldots,x_m,x_R)\) must accept exactly when points with those \(x\)-coordinates and some choice of signs sum to \(R\). Its straight-line programs are built from field arithmetic, univariate resultants, and univariate gcds. No Gröbner oracle and no summation-polynomial oracle.

**Structural saving.** Balancing relation search against an \(f\times f\) sparse solve gives work \(q^{2/(m+1)}\) when a trial costs \(q^{o(1)}\). For \(m=2\) that is \(q^{2/3}\), a loss. For \(m=3\) it matches \(q^{1/2}\). For \(m=4\) it is \(q^{2/5}\), and for \(m=5\) it is \(q^{1/3}\), provided \(f=q^{1/(m+1)}\) and the tester really is \(q^{o(1)}\). Yokoyama et al. close this budget when the tester is a Gröbner basis of the naive summation system. McGuire–Mueller close it when the “tester” is enumeration of factor-base tuples. A univariate-gcd straight-line program of length \(O(1)\) would sit in the open cell of that budget.

**Accounting.** Circuit construction: the enumerated straight-line programs, length \(\le 5\), basis size about 8. Width: degree of every univariate resultant the program builds (must stay \(q^{o(1)}\), so degree \(2^{m}\) is already suspicious at \(m=5\)). Branching: number of candidate roots retained by each gcd. Preprocessing: constructing \(F\), counted in full for one target. Verification: \(m\) point additions and a sum check, plus the cost of the sparse solve \(O(m f^2)\) field operations modulo \(q\).

**Gain.** \(q^{2/5}\) at \(m=4\) if such a tester exists. No gain from a tester whose cost itself exceeds \(q^{2/5-1/(m+1)}\).

**Prior art.** The skeleton is classical index calculus. The \(q^{2/(m+1)}\) balance is the standard one and is not new. The restricted grammar is the claim under test. Petit–Kosters–Messeng already vary the factor-base equation and still lose on 22-bit fields; a tester that secretly reconstructs their system or Semaev’s \(S_{m+1}\) is not a new mechanism.

**Unsupported assumption.** Some straight-line program in that grammar decides 4-point decomposition in \((\log q)^{O(1)}\) operations on every ordinary prime-order curve, with resultant degrees bounded by a constant.

**Cheapest falsifier.** On one curve of order about \(2^{16}\), label random 4-tuples as relations or non-relations by direct addition (the group is small enough). Enumerate programs of length \(\le 3\), then \(\le 5\). Zero precision against that list kills the grammar at that length. A program that fits must then be timed on a curve of order about \(2^{20}\), where \(\sqrt{q}\) group operations are still a feasible comparison and a hidden exponential degree will show up.

## Unresolved

The degree in Card 1 and the term count in Card 2 are finite-checkable and likely fatal; neither finite check proves a family-wide exponent. Card 3 is a one-line mutual-information kill unless elliptic addition has a prefix law nobody uses. Card 4 is the only one with a clean exponent slot below \(1/2\), and it is empty until a tester is exhibited that stays inside the univariate grammar on two successive sizes. I did not treat a failed literature search after 2018 as a proof that no prime-field exponent below \(1/2\) exists.
