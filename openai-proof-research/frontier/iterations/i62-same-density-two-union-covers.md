# I62 — Same-density two-union integral covers

Date: 2026-10-09. Accepted upstream premise: all statements and lower proof operations at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Disposition: D remains unproved and unrefuted. No substantial finding is nominated.** This report gives a complete bounded-rank integral theorem, a graph refinement, a random-order integral construction with a concrete failure of its uncompressed cost estimate, and a connected uniform-hypergraph counterexample to enlarged-density control of the actual two-row coefficients. The last counterexample has probability tending to one and nonempty exceptional family, but its *optimal integral cover cost tends to zero*: it refutes a proposed proof interface, not D. All positive structural results below have explicit classical reductions and are classified as technical.

The [current and historical assignment](../sources/i62_same_density_two_union_covers/full-brief.txt), [frozen inputs](../sources/i62_same_density_two_union_covers/inputs.json), [source contracts](../sources/i62_same_density_two_union_covers/source-contracts.json), [objections](../sources/i62_same_density_two_union_covers/objections.json), and [exact computations](../experiments/i62_same_density_two_union_covers/exact-results.json) are separate evidence. Only this report and the two assigned I62 directories were written. No agents, shared edits, staging, commits, or publication were used; I61's entropy work was not used.

## 1. Input audit, source scope, and exact target

I read the full I60 report, its historical brief and objections, and the actual complete proofs of both pinned September 23 discrete-convexity and integral–fractional manuscripts, including the full selector construction, rounding argument, two-union consequences, signed weights, elementary pair cover, and dependent-row restoration. The sixteen cached files belonging to these two manuscripts are individually pinned. Nine additional I60 graph/hypergraph influence and decomposition proof files were read and pinned to check their inherited scope; none of those routes is reopened. The complete tree has 13,223 entries and 749 manuscript directories; all 9,340 ignored corpus files were independently checked against its Git blob identities. Searching these files is not represented as reading every manuscript.

I retain I60's disposition, including the technical slice transfer and Hall slack and its three scoped counterexamples. I do not renominate them. The frozen parent I60 replay is evidence reproduction, not an independent analytic verdict on every I60 theorem. My independent analytic input check here concerns the two-row certificate and the precise operations used below. The four shared ledgers are informational/mutable; their frozen bytes and current differences are reported separately. Historical seals are not refreshed.

Write
\[
 \kappa_p(\mathcal F)=\min\left\{\sum_{I\in\mathcal G}p^{|I|}:
   \forall S\in\mathcal F\ \exists I\in\mathcal G, I\subseteq S\right\}.
\]
The minimum is over **families**, with duplicates removed. The empty *family* covers the empty exceptional family at cost zero. The family consisting of the empty *set* covers everything at cost one.

D asks whether some absolute \(0<\varepsilon<1/2\) makes
\[
 \mu_p(\mathcal D)\ge1-\varepsilon
 \quad\Longrightarrow\quad \kappa_p(E_2(\mathcal D))\le\tfrac12
 \tag{D}
\]
for every nonempty finite ground set and every \(0<p<1\), with no monotonicity assumption and repeated members allowed in the two unions. The unresolved range is \(p<1/2\). For \(p\ge1/2\), independently across coordinates choose row pairs with probabilities \(1-p,1-p,2p-1\) on \((1,0),(0,1),(1,1)\). Both rows have marginal \(\mu_p\), their union is the ground set surely, and when \(\mu_p(\mathcal D)>1/2\) both are good with positive probability. Thus \(E_2=\varnothing\).

The available pinned conclusions are stronger than their titles suggest but do not assert D: same density with \(2^{75}\) unions at mass \(1-2^{-75}\), two unions at \(p/(50\cdot512^4)\) from mass greater than one half, and generic fractional-to-integral rounding with loss \(25\cdot512^4\). The positive-selector consequence is also available. None is treated as a new result here.

Current primary comparisons were made against fresh responses, not search snippets:

* [Li, arXiv:2609.08967v2](https://arxiv.org/abs/2609.08967v2), revised October 6, 2026: Theorem 1.15 and its spectral/LP proof give the precise fractional two-union bound; Theorem 1.19 and Section 3 give a coupling with two possibly dependent Bernoulli marginals. They do not give an integral cover at unchanged density.
* [Park, arXiv:2609.14681v1](https://arxiv.org/abs/2609.14681v1), Theorem 3.4 and Corollary 3.5: fractional coverage at \(p/2\), then integral coverage with a double-logarithmic density loss. The pinned companion already removes that extra loss.
* [Ascoli–He–Park–Talagrand, arXiv:2608.11183v1](https://arxiv.org/abs/2608.11183v1), Section 8: Question 8.2 concerns two-thresholds of graph-*containment* families. It does not solve the arbitrary hypergraph-*independence* problem here.
* [Talagrand's 2010 author text](https://michel.talagrand.net/preprints/small.pdf), Sections 5–7: the downward-closure observation is already explicit at the end of the discussion introducing \(\mathcal A^{(q)}\). The singleton prefix construction and fractional duality are also earlier operations. His [2021 second edition](https://michel.talagrand.net/ULBSPRINGER.pdf), Section 13.3, Research Problem 13.3.2 and Proposition 13.3.3, was retrieved and read directly. Equations (13.11)–(13.14) already discuss the cardinality downset and its large-number-of-unions cover.
* [Frankston–Kahn–Park](https://arxiv.org/abs/2105.10905), Proposition 2.1 and its proof, give the attributed singleton prefix cover for a sufficiently large multiple of the mean. [Fischer–Person](https://arxiv.org/abs/2505.21782), Definition 3, Theorems 4–5, and their overlap/union-cover operations retain a density loss. Their pair-union mechanism is not an uncredited new construction here.
* [Ferber–Shapira](https://arxiv.org/abs/1903.04968), Section 2, give the random-order greedy-coloring proof used in Section 4 below, attributing it to Pluhár and the simple-pair criterion to Lovász. Its relevant argument is reconstructed rather than assuming an external theorem.

Yang's official current page again reports withdrawal and its current PDF again returns 404; it is not used. An initially guessed Talagrand book URL returned 404; the author's actual homepage link subsequently supplied the 727-page 2021 book. Both responses are preserved. No search silence, absence theorem, MathDB score, or worldwide-priority claim is inferred.

## 2. Exact hypergraph reformulation

Let \(\mathcal D^\downarrow=\{A:A\subseteq D\text{ for some }D\in\mathcal D\}\). Then
\[
 \mu_p(\mathcal D^\downarrow)\ge\mu_p(\mathcal D),\qquad
 E_2(\mathcal D^\downarrow)=E_2(\mathcal D).                 \tag{2.1}
\]
One direction follows from inclusion. For the other, witnesses \(A_j\subseteq D_j\in\mathcal D\) turn \(S\subseteq A_1\cup A_2\) into \(S\subseteq D_1\cup D_2\). Hence we may assume \(\mathcal D\) is nonempty and downward closed; it then contains \(\varnothing\).

Let \(\mathcal H\) be its inclusion-minimal excluded sets. They are nonempty and form an antichain. Its independent sets are precisely \(\mathcal D\). A set \(S\) is covered by two independent sets if and only if \(S=T\sqcup(S\setminus T)\) for two independent color classes: from two covering sets assign shared vertices arbitrarily, and use downward closure. Thus
\[
 E_2(\mathcal D)=\{S:\mathcal H[S]\text{ is not two-colorable}\}. \tag{2.2}
\]
Here \(\mathcal H[S]=\{e\in\mathcal H:e\subseteq S\}\); edges are **not** intersected with \(S\). The minimal members of this exceptional family will be called critical cores. Generators need not themselves be critical cores, or even be exceptional. Compressing many cores by a common proper subset can be essential.

For ordinary graphs without loops, a graph is two-colorable exactly when it has no odd cycle: alternating colors along paths from one root are consistent unless there is an odd closed walk, which contains an odd cycle by deleting repeated-vertex subwalks. The minimal induced nonbipartite vertex sets are chordless odd cycles. This classical equivalence is the graph test, not a discovery.

## 3. Construction A: dual weights, second moments, and actual same-density rounding

This construction proves an integral theorem for every bounded rank. It pays its rounding step at the same density and identifies exactly where rank dependence enters. It uses finite LP duality and elementary estimates, not an unproved same-density rounding principle.

**Theorem A.** Suppose every minimal excluded set of a nonempty downset \(\mathcal D\) has size at most \(r\ge1\). Put \(a=\mu_p(\mathcal D)>0\) and \(\delta=1-a\). Then
\[
 \kappa_p(\mathcal D^c)
 \le (2^r-1)\big((2-p)^r-1\big)\frac\delta{1-\delta}
 \le (2^r-1)^2\frac\delta{1-\delta}.                         \tag{A}
\]
In particular D holds in this class with
\(\varepsilon_r=[1+2(2^r-1)^2]^{-1}\). The bound applies to the **whole complement**, hence to \(E_2\subseteq\mathcal D^c\). If \(\mathcal H=\varnothing\), the conclusion holds with the empty cover without choosing a rank.

**Proof.** Consider the finite fractional cover problem for \(\mathcal H\), using nonempty generators \(I\) contained in at least one edge:
\[
 t=\min\left\{\sum_I p^{|I|}x_I:x_I\ge0,
                  \ \sum_{\varnothing\ne I\subseteq e}x_I\ge1
                  \quad(e\in\mathcal H)\right\}.
\]
Its dual is
\[
 t=\max\left\{\sum_e\lambda_e:\lambda_e\ge0,
       \ \sum_{e\supseteq I}\lambda_e\le p^{|I|}
       \quad(\varnothing\ne I\subseteq X)\right\}.             \tag{3.1}
\]
Constraints for useless \(I\) are automatic. Feasibility, finite attainment, and equality follow from finite linear programming; no empty-set dual constraint is imposed. Let \(\lambda\) be optimal and set
\(Z=\sum_e\lambda_e p^{-|e|}\mathbf1_{e\subseteq X_p}\).
Then \(\mathbb EZ=t\), and \(Z>0\) implies \(X_p\notin\mathcal D\).

For any finite \(K\),
\(p^{-|K|}=\sum_{I\subseteq K}(p^{-1}-1)^{|I|}\).
Therefore, writing \(L_I=\sum_{e\supseteq I}\lambda_e\),
\[
 \mathbb EZ^2
 =t^2+\sum_{I\ne\varnothing}(p^{-1}-1)^{|I|}L_I^2
 \le t^2+\sum_e\lambda_e
             \sum_{\varnothing\ne I\subseteq e}(1-p)^{|I|}
 \le t^2+t\big((2-p)^r-1\big).                              \tag{3.2}
\]
The first inequality uses \(L_I\le p^{|I|}\) in one factor. Cauchy–Schwarz on \(\{Z>0\}\) gives
\(\delta\ge t/[t+(2-p)^r-1]\) when \(t>0\), whence
\(t\le((2-p)^r-1)\delta/(1-\delta)\). The zero case is immediate.

Choose every nonempty \(I\) with \(x_I\ge1/(2^r-1)\). Each edge has at most \(2^r-1\) eligible subsets, so some chosen generator lies in it. The selected family has cost at most \((2^r-1)t\). It covers every set containing an edge, proving A. All constants and inequalities hold for every finite size and every \(0<p<1\). ∎

**Graph refinement A2.** When \(r\le2\),
\[
 \kappa_p(\mathcal D^c)
 \le2\big((2-p)^2-1\big)\frac\delta{1-\delta}
 \le6\frac\delta{1-\delta}.                                \tag{A2}
\]
Thus \(a\ge12/13\) suffices uniformly over all graphs and all densities.

To prove the sharper rounding, write the fractional weights as \(x_v\) and \(y_{uv}\). Choose one common threshold \(T\) uniformly from \((0,1/2)\). Select vertices with \(x_v\ge T\), then select every edge neither of whose endpoints was selected. Singleton constraints have \(x_v\ge1\), so they are covered. The expected vertex cost is at most \(2p\sum_v x_v\). An edge is selected with probability
\[
 (1-2\max(x_u,x_v))_+\le(1-x_u-x_v)_+\le y_{uv}.
\]
Consequently the expected total cost is at most \(2\sum_vpx_v+\sum_{uv}p^2y_{uv}\le2t\). Every outcome covers all edges; one has cost at most this expectation. Combining with (3.2) proves A2.

**Contribution and precise limitation.** A and A2 are complete author proofs but are entirely classical: LP duality → the displayed second moment → a bounded-number-of-subsets rounding, or the one-threshold graph rounding. They do not need the newly assumed corpus. For unbounded rank, both the expansion \((2-p)^r\) and the rounding factor grow; high probability of independence supplies no rank bound. A graph result cannot therefore be promoted to D by calling the minimal forbidden objects “edges.”

## 4. Construction B: random-order coloring yields integral generators

Remove singleton forbidden vertices first, selecting their singleton generators. Remaining edges have size at least two. Fix an ordering \(\pi\) of the remaining vertices. For each ordered pair \((e,f)\) with \(e\cap f=\{v\}\), select \(e\cup f\) if all vertices of \(e\setminus\{v\}\) precede \(v\) and all vertices of \(f\setminus\{v\}\) follow it. Remove repeated selected unions.

This is an **integral cover for every ordering**, not fractional weights from the outset. Indeed, on an exceptional \(S\) avoiding the singleton generators, run the following greedy coloring using \(\pi|_S\). Color a vertex blue unless that completes a blue edge, in which case color it red. No blue edge is produced. If the resulting coloring has a red edge \(f\), let \(v\) be its earliest vertex. The reason \(v\) was red was an edge \(e\) whose other vertices were already blue. Thus \(e\cap f=\{v\}\) and \(\pi\) separates the pair as required; its selected union lies in \(S\). Non-two-colorability forces a red edge. This reconstructs Ferber–Shapira's Section 2 argument, including its Pluhár/Lovász attribution.

If \(|e|=k\), \(|f|=\ell\), the separation probability under a uniform ordering is
\[
 \alpha_{k,\ell}=\frac{(k-1)!(\ell-1)!}{(k+\ell-1)!}.
\]
Counting unions with multiplicity only increases cost. Hence some ordering supplies a cover of cost at most
\[
 p\,|\mathcal H_1|
 +\sum_{\substack{(e,f)\in\mathcal H_{\ge2}^2\\|e\cap f|=1}}
       \alpha_{|e|,|f|}\,p^{|e\cup f|},                     \tag{B}
\]
where edges meeting a singleton forbidden vertex may be omitted. For an \(r\)-uniform hypergraph without singletons this is
\[
 \frac{m_2(\mathcal H)}{r\binom{2r-1}{r}}p^{2r-1}.           \tag{4.1}
\]
Thus (B) is a directly computable sufficient condition, valid also for nonuniform hypergraphs. It is not claimed to follow from high independence probability.

### 4.1 The unpaid cost estimate is actually false, even after pruning to cores

Let \(H_m\) have vertices \(u,v,w_1,\ldots,w_m\), edge \(uv\), and edges \(uw_i,vw_i\). Its only critical cores are the \(m\) triangles \(\{u,v,w_i\}\). Its independence probability is exactly
\[
 a_m=(1-p)^2+2p(1-p)^{m+1}\ge(1-p)^2.                       \tag{4.2}
\]
For every ordering, each triangle has a separated simple pair, so construction B selects **all** its critical triangles. Even if pairs whose unions are not contained in a critical core are discarded, its cost is exactly \(mp^3\). Selecting all minimal cores has the same cost.

But a single generator \(\{u,v\}\) covers every critical core. In fact
\[
 \kappa_p(E_2(\mathcal D_m))=\min\{p^2,mp^3\}.              \tag{4.3}
\]
To justify optimality, a useful nonempty generator contained in more than one core must be contained in \(\{u,v\}\), and therefore costs at least \(p^2\). If no such generator is selected, every core needs a separate generator, each costing at least \(p^3\). The two displayed choices attain the lower bound. An empty generator costs one and cannot improve it.

Take \(p\downarrow0\), \(m=\lceil p^{-4}\rceil\). Then \(a_m\to1\), while \(mp^3\to\infty\) and the optimum is \(p^2\to0\). Consequently neither raw critical-core summation nor the separated-pair budget is bounded by a universal function tending to zero with \(1-a\). Pruning to pairs lying in actual critical cores does not repair this. A successful general construction must compress overlaps; its missing estimate cannot simply be (B) \(\le C(1-a)\).

A star of hyperedges with one common center and otherwise disjoint petals is an even simpler warning: it is two-colorable, so its exceptional family is empty, but the number of simple pairs can be arbitrarily large while the failure probability is at most \(p\). Pairwise intersection alone is therefore not a non-two-colorability certificate.

### 4.2 An unbounded-rank case that is already elementary

Suppose the ground set is partitioned into blocks, the forbidden hypergraph has no cross-block edge, and each block has at most one critical core \(C_j\). Let \(a_j\) be its independence probability and \(a=\prod_j a_j\). Every exceptional set contains one \(C_j\), so select these cores. Since \(C_j\) contains some forbidden edge, \(p^{|C_j|}\le1-a_j\). Thus
\[
 \kappa_p(E_2)\le\sum_jp^{|C_j|}
 \le\sum_j(1-a_j)\le-\log a.                               \tag{4.4}
\]
If \(a\ge e^{-1/2}\), the budget is at most one half, uniformly in ranks and the number of blocks. Blocks with no core contribute nothing. This handles disjoint odd cycles, complete uniform hypergraphs on \(2r-1\) vertices, and Fano-plane blocks. It is just product independence and the elementary logarithm inequality, not a substantial new mechanism. The overlapping triangle book explains why this calculation is not a general component decomposition.

## 5. Independent two-row audit and a false spectral bridge

For \(f=\mathbf1_{\mathcal D}\), \(a=\mu_p(\mathcal D)>0\), define the I60 coefficients
\[
 b(U)=(1-p)^{|U|}\sum_{z\in\{0,1\}^U}(-1)^{|z|}
                  \mathbb E f(z,Y),\qquad w(U)=b(U)^2.
\]
In a coordinate of \(S\in E_2\), the signed two-row column masses are
\(p^{x+y}(1-p)^{2-x-y}-(1-p)^2(-1)^{x+y}\).
Their \((0,0)\) mass is zero. Hence every array with nonzero mass has row union covering \(S\), and the product of its two \(f\)-values is zero. Expanding the finite product by corrected columns and separating the two rows proves
\[
 0=\sum_{U\subseteq S}(-1)^{|U|}b(U)^2.                     \tag{5.1}
\]
In particular the sum over **odd** subsets equals \(a^2\) plus the sum over nonempty even subsets. The odd-only coefficients
\[
 c_U=\mathbf1_{|U|\text{ odd}}\min\{1,b(U)^2/a^2\}           \tag{5.2}
\]
already give a fractional cover. Using all nonempty subsets, as in I60, also works. Capping preserves coverage because either one capped term covers alone or no term changes.

For the orthonormal biased basis \(\chi_U=\prod_{i\in U}(p-x_i)/[p(1-p)]^{|U|/2}\), direct summation yields
\(p^{|U|}b(U)^2=(1-p)^{|U|}\widehat f(U)^2\).
Parseval and \(f^2=f\) now give
\[
 \sum_U p^{|U|}c_U\le\frac{(1-p)(1-a)}a.                    \tag{5.3}
\]
The bound also holds with I60's all-nonempty coefficients. Solving its budget inequality gives \(a\ge(2-2p)/(3-2p)\). **Input verdict: the I60 certificate is valid without repairs, and its theorem is Li v2 Theorem 1.15, not a new finding.** Keeping only odd terms is already implicit in Li's spectral proof and does not close integrality.

The existing rounding proof requires product-variable mean at most its *fractional* density divided by five. At target \(p\), it only bounds that mean by \(5\cdot512^4p\), not by \(p\). Smallness of (5.3) cannot simply absorb this factor in unbounded degree. The following actual downsets make that failure quantitative, even with the extra Boolean and downward-closure structure.

### 5.1 Connected, uniform, high-mass examples with divergent enlarged coefficient cost

**Proposition C (counterexample to a proposed bridge, not to D).** For every fixed \(C>1\), there is a fixed \(p\in(0,1/2)\) with \(Cp<1\), and nonempty downsets \(\mathcal D_r\), whose minimal forbidden hypergraphs are connected and \((r+1)\)-uniform, such that
\[
 \mu_p(\mathcal D_r)\to1,\qquad
 \kappa_p(E_2(\mathcal D_r))=p^{2r+1}\to0,\qquad
 \sum_{U\ne\varnothing}(Cp)^{|U|}\min\{1,b_r(U)^2/a_r^2\}\to\infty.
 \tag{C}
\]
The divergence persists if only odd \(|U|\) are retained.

**Construction and proof.** Choose, for example,
\[
 p=\min\{1/8,\,1/(4C),\,(1-1/C)/2\},\quad
 B=p^2+Cp(1-p)^2.
\]
Then \(0<p<B<1\): indeed
\(B-p=p(1-p)[C(1-p)-1]>0\), and \(B\le1/64+1/4<1\).
Let \(M_r=\lceil rB^{-r}\rceil\). Take a core \(A\) of size \(2r+1\), a distinguished vertex \(v\in A\), and pairwise disjoint petals \(P_1,\ldots,P_{M_r}\), each of size \(r\), outside \(A\). The forbidden edges are every \((r+1)\)-subset of \(A\), together with \(\{v\}\cup P_j\) for every \(j\). They have equal size and connect through \(v\); hence they are the minimal excluded sets of a connected uniform hypergraph.

A set is independent precisely when it has at most \(r\) core vertices and does not contain \(v\) together with an entire petal. A union bound gives
\[
 1-a_r\le\binom{2r+1}{r+1}p^{r+1}+M_rp^{r+1}
 \le2p(4p)^r+M_rp^{r+1}\longrightarrow0,                    \tag{5.4}
\]
since \(4p<1\) and \(M_rp^r\le r(p/B)^r+p^r\to0\).

The **only** critical core is \(A\). All of \(A\) cannot be two-colored with both color classes of size at most \(r\). Conversely, if \(S\) omits some core vertex, partition \(S\cap A\) into two classes of size at most \(r\). If \(v\in S\), give at least one vertex of each fully present petal the opposite color to \(v\); there are no other petal constraints. All partially present petals are harmless. This extends the coloring, so \(S\) is not exceptional. Therefore \(E_2=\{S:A\subseteq S\}\), and its exact optimal cost is \(p^{|A|}\): any cover must cover \(A\) itself and thus contains a generator of cost at least \(p^{|A|}\); selecting \(A\) attains it.

It remains to calculate the actual coefficients. Let
\[
 t_r=\Pr\{\operatorname{Bin}(2r,p)\le r-1\}\to1,
 \quad h_r(x)=1-\prod_{i=1}^r x_i.
\]
For one petal,
\[
 b_{h_r}(\varnothing)=1-p^r,\qquad
 b_{h_r}(U)=(-1)^{|U|+1}(1-p)^{|U|}p^{r-|U|}
       \quad(U\ne\varnothing).                            \tag{5.5}
\]
For a nonempty \(U\) supported entirely on petals, the contribution with \(v=0\) is constant in petal coordinates and vanishes in the alternating difference. The contribution with \(v=1\) factors, giving exactly
\[
 b_r(U)=p\,t_r\prod_{j=1}^{M_r}b_{h_r}(U\cap P_j).           \tag{5.6}
\]
Every factor has absolute value at most one, so \(|b_r(U)|\le p\). Since \(a_r\to1\), no capping occurs on these coefficients for sufficiently large \(r\).

The one-petal generating polynomial evaluated at \(Cp\) is
\[
 (1-p^r)^2+\sum_{\varnothing\ne U\subseteq P_j}(Cp)^{|U|}b_{h_r}(U)^2
 =1-2p^r+B^r.
\]
Consequently the enlarged cost contributed by nonempty petal-supported sets alone is
\[
 \frac{p^2t_r^2}{a_r^2}
 \left[(1-2p^r+B^r)^{M_r}-(1-p^r)^{2M_r}\right].            \tag{5.7}
\]
The second power tends to one. Eventually \(B^r-2p^r\ge B^r/2\), while this quantity tends to zero; \(\log(1+x)\ge x/2\) for \(0\le x\le1\) gives a logarithm of the first power at least \(M_rB^r/4\ge r/4\). Thus (5.7) diverges.

For odd supports, put \(B_-=p^2-Cp(1-p)^2\), so \(|B_-|<B\). The corresponding sum is exactly
\[
 \frac{p^2t_r^2}{2a_r^2}
 \left[(1-2p^r+B^r)^{M_r}-(1-2p^r+B_-^r)^{M_r}\right].       \tag{5.8}
\]
The second base is positive for large \(r\), and its power tends to one because
\(M_rp^r\to0\) and \(M_r|B_-|^r\to0\). The first power diverges as before. This proves C, including the odd-only assertion. ∎

**What C rules out.** No estimate controlling these enlarged spectral costs solely by \(1-a\), uniformly in dimension and rank, can pay the generic rounding loss. Connectedness, uniformity, nonempty exceptionality, positivity of squared coefficients, Boolean idempotence, and deletion of even supports do not repair that estimate. This is stronger than displaying arbitrary fractional weights with a bad degree tail: the weights here are exactly those of the actual downset. C does **not** rule out selecting only strategically useful coefficients, restricting to critical supports, or an entirely different cover. In this construction such localization would discard the petal coefficients and immediately expose the cheap core. That localization, in general overlapping hypergraphs, is the unpaid step.

## 6. Adversarial cases, exact lower bounds, and additional failed interfaces

**Projective planes.** The independent computation constructs homogeneous-coordinate planes of orders two and three. For the Fano plane the independence counts by size are \((1,7,21,28,7,0,0,0)\); there is no two-coloring and the sole critical core is the whole seven-point set, with exact optimal cover cost \(p^7\). The order-three plane has 468 two-colorings, hence an empty exceptional family; no claim that all projective planes are non-two-colorable is made. These finite facts follow from complete enumeration of the displayed line masks, not from a secondary account. In particular pairwise intersecting line families do not by themselves supply counterexamples. Disjoint repetitions are covered by (4.4).

**Disjoint forbidden blocks.** If the forbidden edges are disjoint and all have size at least two, color each edge in both colors, so \(E_2=\varnothing\). If singleton forbidden blocks also occur, their singleton generators cost at most \(-\log a\), by the same product calculation. Large rank alone is not an obstruction.

**Cardinality downsets.** For \(\mathcal D=\{S:|S|\le k\}\), the exceptionality condition is exactly \(|S|\ge2k+1\), provided \(2k+1\le n\); otherwise it is empty. This is already Talagrand's example. The direct all-core cover costs \(\binom n{2k+1}p^{2k+1}\), and need not be inexpensive when \(np\) is just below \(k\). High probability of \(|X_p|\le k\) can coexist with \(np/k\to1\), so source bounds for a sufficiently large multiple of the mean do not automatically reach the factor two.

There is an exact fractional benchmark. For all \(t\)-sets, symmetry and averaging show that the minimum fractional cost (allowing the empty generator) is
\[
 \min_{0\le j\le t}\frac{\binom nj p^j}{\binom tj}.           \tag{6.1}
\]
Indeed a symmetrized fractional assignment has a common weight \(x_j\) at level \(j\), one constraint \(\sum_j\binom tjx_j\ge1\), and the displayed linear objective; choosing its cheapest ratio is optimal. Equivalently uniform dual mass on the \(t\)-sets certifies the same bound. Integral symmetry averaging is illegal: it replaces a family by fractional weights. Integral covers correspond to choosing a hypergraph with independence number less than \(t\), with cost charged by edge size. I do not claim that (6.1), the prefix construction, or an unspecified Turán bound solves this same-density integral instance.

**A genuine fractional/integral budget gap arising from an actual downset.** On five vertices take \(\mathcal D=\{S:|S|\le1\}\), \(p=5/13\). Then \(E_2\) consists of sets of size at least three and
\[
 a=135168/371293,\quad
 \kappa_p^{\rm frac}(E_2)=250/507<1/2,
 \quad \kappa_p(E_2)=1150/2197>1/2.                         \tag{6.2}
\]
For the fractional value put weight \(1/3\) on each pair. Uniform dual weight \(p^2/3\) on each of the ten triples is feasible: singleton, pair, triple and empty-generator constraints are respectively \(2p^2\le p\), equality, \(p^2/3\le p^3\), and \(10p^2/3\le1\). It certifies optimality. An optimal integral family consists of two disjoint pairs, and the four triples choosing one point from each pair together with the fifth vertex, with cost \(2p^2+4p^3=1150/2197\). The independent exact dynamic program in Section 7 certifies the lower bound against **all** useful generators and records its rational state values. This is not a counterexample to D: its mass is below one half. It does refute any claim that being a two-union exception of an actual downset makes fractional and integral smallness identical at every density and mass. Tensoring this example would decrease its mass, not amplify it toward one.

**Weighted cardinality and packing.** For \(\mathcal D=\{S:\sum_{i\in S}w_i\le1\}\), two-union coverage means actual packing into two capacity-one bins. The necessary total-weight condition is insufficient: three weights \(3/5\) form a critical core even though their total is \(9/5<2\). If every weight is at most one, total weight at most \(3/2\) does suffice. To see this, pack in decreasing order, putting each item into either bin where it fits. If an item of size \(x\le1/2\) first fails, both loads exceed \(1-x\), so the total exceeds \(2-x\ge3/2\). If the failing item exceeds one half, it is at least the third such item, again giving total greater than \(3/2\). Weights above one are separate singleton obstructions. This is a real packing argument, but converting the resulting \(3/2\)-tail to a cheap cover from high quantile information is unpaid. The positive-selector or singleton prefix theorem only supplies a larger fixed dilation; changing its numerical constant without proof is not a solution.

**Sprinkling and tensor products.** The source's exact density-restoration coupling groups more rows and therefore increases the number of unions. The source's selector conclusion dilates a threshold. Neither preserves the requested two unions automatically. Construction C uses block products to construct a counterexample to an estimate, with its mass computed explicitly; it is not an amplification proof of D.

## 7. Exact verification, evidence scope, and remaining task

The two diagnostics make **299,793 exact assertions**. The first diagnostic enumerates **all downsets for \(1\le n\le5\)**, including the empty downset in its counts \(3,6,20,168,7581\) and excluding it from the high-mass tests. For every nonempty downset it computes critical cores, checks the two-coloring equivalence on every subset, and finds the exact optimal integral cost at \(p=1/4,1/3,2/5\). It also checks the signed identity and fractional budget for every nonempty downset on at most four vertices at those biases; arbitrary families on at most three vertices check (2.1). Projective-plane line masks, colorings, independence counts, and cores are retained.

The cover computation uses no floating-point optimizer. A useful generator must be contained in a critical core. It enumerates these generators, represents their covered cores by a bit mask, and assigns the integer cost \(a^{|I|}b^{n-|I|}\) for \(p=a/b\), in units \(b^{-n}\). Equal-coverage options retain their cheapest generator; dominated options are discarded only when another covers a superset at no larger cost. For an uncovered mask \(M\), choose one uncovered core \(j\) and use the exact recurrence
\[
 V(M)=\min_{I\subseteq C_j}\bigl(\operatorname{cost}(I)+V(M\setminus\operatorname{covered}(I))\bigr),\quad V(0)=0.
\]
Every cover must choose some such \(I\), and every recursive choice is a cover, proving optimality by induction on the number of uncovered cores. All comparisons are integer or rational. The special case (6.2) is checked separately with all options retained and its rational state values saved.

At the three exhaustive biases, no tested downset with mass greater than one half had integral cost above one half. The largest mass among failures was \(243/512\): forbid two singleton vertices and allow at most one of the remaining three, at \(p=1/4\). Its critical cores are those two singletons and the remaining triple, and its exact optimum is \(1/4+1/4+1/64=33/64\). This is finite evidence only, not an extrapolation to D.

The second diagnostic independently checks the random-order cover for every nonempty downset on at most four vertices and every ordering; directly checks the connected example's coefficients from its full Boolean truth table in small cases; verifies both its all-degree and odd-degree polynomial identities; checks triangle-book probabilities and core structure; and records exact rational asymptotic control quantities for several \(C\), including the pinned rounding constant. The growing dimensions in Proposition C are covered by its written proof, not by evaluating enormous tensor powers numerically.

Reproduction from the project root:

```sh
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i62_same_density_two_union_covers/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i62_same_density_two_union_covers/construction_checks.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i62_same_density_two_union_covers/verify.py
```

The verifier is read-only. It checks the exact owned-file inventory and seal, frozen inputs, old immutable watches, all corpus Git identities, selected pinned sources, exact passage hashes, primary response bytes including failures, prior-search line **multisets** on a frozen finite domain, corpus-search line multisets, and fresh independent reruns of both diagnostics. It does not expand an old prior-report search domain, copy earlier evidence recursively, alter a historical seal, or write its own output. Source provenance and finite checks are separate from analytic and significance review.

The strongest proved general structural partial is A (and A2 for graphs). The unbounded-rank disjoint-core case (4.4) is also complete but elementary. The two developed nontrivial attempts reach explicit failures: random-order/critical-core summation loses overlap compression on the triangle book, while full spectral-budget amplification fails on connected uniform examples even after deleting even degrees. What remains is a method that localizes to genuinely useful critical obstructions and compresses their overlaps while charging original-density integral generators. No such method is supplied here, and no bound equivalent to D is asserted as a lemma. **There is no substantial nomination, no acceptance-count increment, and no claim of an independent proof-review PASS.**
