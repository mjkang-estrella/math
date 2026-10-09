# I22 — Combinatorial discovery: exact constructions and remaining gaps

Date: 2026-10-09. Corpus premise: every supplied proof in **openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** is true.

**Disposition: no substantial nonroutine finding is proposed for acceptance.** Four concrete targets were screened. Two complete deductions are retained: an exact, sharp subcubic matching-entropy bound at every even order, and a polynomial independence-oracle implementation of the supplied one-sample prophet rule for binary rational observations. Both reduce to elementary or standard machinery once the strongest source proofs are available, and are classified here as **technical only**, not as discoveries meeting the assignment's gate. The general coefficient-3/2 entropy target and linear correspondence Hadwiger target remain open in this report. An approximate-PSD-rank strengthening is false by an existing primary construction, without conflicting with the stipulated exact-rank theorem.

The full assignment is frozen in [full-brief.txt](../sources/i22_combinatorial_discovery/full-brief.txt). All work is confined to this report and the two assigned I22 directories. No agents were started; no shared index, staging area, commit, push, or other project was modified.

## 1. Premises, inventory, and significance gate

I read AGENTS.md and the I13/I19 screens before developing these targets. In particular, I do not identify a projection of common-base support with an intersection of separate projections, use inverse-fiber sampling to flatten an exponential multiplicity, extend the uniform switch-chain proof to arbitrary activities, or reuse signed Saxl work reserved for I21. The PDE/kinetic work reserved for I20 is separate.

The I07/I14/I15/I17 significance decisions require comparing a proposed bridge with **source proofs**, not only headline statements. A sharp new formulation or an implementation omitted by the source can still be technical. The accepted R006/R008/R009/R010 records supply the contrasting standard: an additional analytic or constructive step must survive the strongest available interfaces. Neither retained deduction below is represented as an independently reviewed finding.

[inputs.json](../sources/i22_combinatorial_discovery/inputs.json) freezes 14 task dependencies, including the complete preprint tree, upstream pin, ledger, negative screens, significance reviews, and accepted-result records. I traversed the complete inventory of 749 manuscript directories, not the truncated root-tree cache. A bounded text search of all 9,340 cached texts is retained in [corpus-search.json](../sources/i22_combinatorial_discovery/corpus-search.json). Search coverage is not a claim to have read every manuscript.

[pinned-manifest.json](../sources/i22_combinatorial_discovery/pinned-manifest.json) records 107 selected source texts, with immutable raw URLs, Git blob SHA-1, SHA-256, and byte length. They come from the prophet, correspondence coloring, linear list coloring, matching entropy, shifted PSD rank, and integer-polymatroid families, and the relevant matching-FPRAS, clique-free independence, and Hadwiger-counterexample companions. The polymatroid material was a discovery screen only; no theorem below relies on it. Only selected sources were copied; the shared cache remains read-only.

[source-contracts.json](../sources/i22_combinatorial_discovery/source-contracts.json) stores labelled statement blocks. [read-locators.json](../sources/i22_combinatorial_discovery/read-locators.json) identifies the source statements and proof passages actually used. Companion checks found no separate polynomial prophet implementation, no general coefficient-3/2 entropy theorem, and no linear DP Hadwiger interface in these inspected files. This is a scoped statement, not an exhaustive worldwide novelty claim.

Current literature was searched early and again after formulation. Raw query results, version pages, six primary PDFs and their extracted text are retained under the source directory; [literature/manifest.json](../sources/i22_combinatorial_discovery/literature/manifest.json) records exact versions, URLs and hashes. The current primary comparisons are stated below. Irrelevant search hits are retained as search evidence and are not used as mathematical premises.

## 2. Four concrete targets

### A. Uniform polynomial implementation of the one-sample almighty rule

**Target.** With an explicitly labelled n-element matroid given by an independence oracle and independent sample/value pairs supported on nonnegative binary rationals, implement the stipulated distribution-independent constant prophet guarantee in polynomial oracle and bit cost on every execution. The order may depend on every sample, value, and seed bit. The polynomial is measured in n and the total bit length of the observations supplied on that execution; it is not a bound on the support size or encoding of the unknown laws.

**Strong source interface.** In *One Sample Suffices for Matroid Prophet Inequalities against an Almighty Adversary*, `introduction.tex`, `thm:main`, the sample/value coordinates are mutually independent, each pair identically distributed, and the expected offline optimum is finite. The stated constant is 2^-310. `setup.tex`, `prop:hidden` and `lem:simulation`, give a fixed-vector expected-minimum-over-orders bound 2^-293 and an exact one-sample simulation. `algorithm.tex`, `lem:density`, `lem:paths`, and the actual decision list specify the rule completely. The only apparently expensive primitive is maximization over flats. There are at most n listed groups and only O(n) auxiliary times per group. The combinatorial enumeration of marked residual patterns in `transfer.tex` is **analysis**, not an executed subroutine.

**Primary comparison.** Iwata–Fleischer–Fujishige, [math/0004089v1](https://arxiv.org/abs/math/0004089v1), Theorem 4.2, supplies strongly polynomial submodular minimization with a value oracle. Abdi–Banihashem–Hajiaghayi–Mittal, [2609.19118v1](https://arxiv.org/abs/2609.19118v1), Theorem 1.3 and the paragraph immediately following it, supply a one-sample 1/2 guarantee using O(n²) independence queries for an order fixed independently of the observations. This is a different order interface. Feldman–Svensson–Zenklusen, [2507.09507v1](https://arxiv.org/abs/2507.09507v1), Theorem 1.1, supplies a polynomial sample-based OCRS against an almighty adversary, with a rank-dependent sample budget. Their introduction also accounts for extra samples in the prophet reduction. Neither comparison is silently substituted for the pinned full-seed guarantee.

**Outcome.** Section 3 implements the exact source rule. This is a routine submodular-minimization completion, so it does not satisfy the nonroutine gate even though the source expressly disclaims a running-time theorem.

### B. Improve the universal matching-entropy coefficient from 2 to 3/2

**Target.** For every finite loopless labelled multigraph G with a perfect matching, every feasible edge mean x, and natural-logarithm entropies, prove

`H_G(x) >= F_G(x) - (3/2) B_G(x)`,

where H is maximum entropy among matching laws of mean x, `F=-sum x_e log x_e`, and `B=-sum (1-x_e) log(1-x_e)`. This changes the actual prescribed-mean estimate, not only its counting formulation.

**Strong source interface.** *Entropy and Face Dimension of the Perfect-Matching Polytope*, `01-introduction.tex`, `ent:main`, proves `H>=F-(2-2/m)B` on 2m vertices, including boundary means and labelled parallel edges. `03-entropy.tex`, `ent:trace`, gives the exact necessary condition `0>=d-s+(c+1)m` at a fractional local maximum of `F-cB-H`. `02-polytope.tex`, `geom:lem-gluing`, already constructs conditional-independent gluing of laws across an odd cut; `geom:prop-rank` proves the sharp supported-face codimension bound. The componentwise refinement, weighted optimization, nonlinear appendix, and triangle-expansion examples were checked. The matching-FPRAS companion counts uniform perfect matchings and supplies uniform sampling; it is not an oracle for the maximum-entropy law at arbitrary prescribed marginals.

The source's `10-examples.tex`, `ex:cor-coefficient`, already requires any universal coefficient to be at least

`c3 = log(3)/(2 log(3/2)) = 1.3547556456...`.

Its simple eight-vertex counterexample already rules out coefficient one. Neither obstruction is claimed as new.

**Outcome.** Section 4 proves the exact optimal coefficient `(1-1/m)c3` for maximum degree at most three, including the sharp examples at every order. This is technically complete but follows from a scalar entropy inequality and the supplied extremizers. Section 5 develops exact tight-cut entropy gluing and a near-tight conditioning estimate, then identifies the separator term still missing for general degree. The universal 3/2 target is neither proved nor disproved.

### C. Linear correspondence coloring in the Hadwiger number

**Target.** An absolute C with `chi_DP(G)<=C h(G)` for every finite nonempty simple graph G, uniformly over all correspondence assignments. It would extend the supplied linear **list** bound to arbitrary edgewise matchings.

**Strong source interfaces.** The linear-list manuscript's `thm:main` has an absolute constant. Its `03-small-graphs.tex`, `prop:small-list` and `small:eligible-thinning`, use stable-set sampling and a **global partition of actual colors**. Its final coloring paragraph is essential: identical colors belong to the same bin, so a stable set per bin is enough. `04-list-transfer.tex`, `lem:additive-deletion`, also reserves colors globally. By contrast the correspondence manuscript's `thm:main` fixes r first and gives `C_r Delta/log Delta` for K_r-free graphs, with a threshold depending on r. Its stronger `lem:adjustment` already works on partitioned weighted cover graphs, controlling both radius and participation within a list. The one-round and completion proofs still use the base maximum degree Delta and r-dependent constants.

**Primary comparison.** Dvořák–Yepremyan, [2307.15048v1](https://arxiv.org/abs/2307.15048v1), Theorem 1.1, treats dense random graphs; Theorem 2.2 requires a specified independent-set-richness condition on neighborhood subgraphs of the cover and a maximum-degree parameter. This is a useful stronger interface than a bare coloring bound, but a generic minor-free instance has not been shown here to meet the needed quantitative condition. Their introduction explicitly separates linear correspondence Hadwiger from the list problem.

**Outcome.** Section 6 proves that a conflict-free global-bin replacement can collapse to one bin on C4 with arbitrarily large lists. The adjustment lemma does not repair that lost global property merely by citation, and substituting r=h(G)+1 leaves uncontrolled constants. No counterexample to linear DP Hadwiger is supplied.

### D. Robust exponential PSD rank for positively shifted matching slack

**Target.** Fix `0<rho<1`. Extend exponential real PSD rank of `A_n(rho)[U,M]=|delta(U) intersect M|-1+rho` to all nonnegative matrices with entrywise relative error at most a fixed epsilon, or even absolute error at most `2^-sqrt(n/2)`.

**Source interface.** *Exponential PSD rank of positively shifted matching matrices*, `introduction.tex`, `thm:main`, is an **exact** factorization theorem, with exponential rate independent of fixed rho and threshold allowed to depend on rho. Its proof and introduction explicitly distinguish exactness from approximation. The local averaging and product-smoothing interfaces do not assert this robust extension.

**Outcome: false.** Kaniewski–Lee–de Wolf, [1411.7280v1](https://arxiv.org/abs/1411.7280v1), Theorem 19, gives nonnegative underapproximations of matching slack with PSD rank `2^{O(n^{1/2+a}(log n)^2)}` and error at most `2^{-(n/2)^{2a}}`, exact at its specified small entries. Put a=1/4, restrict to odd-cut rows, and append a scalar rho block to each row factor and a scalar one block to each column factor. The resulting nonnegative matrix approximates A_n(rho) with the same absolute error and rank at most `2^{O(n^{3/4}(log n)^2)}+1=2^{o(n)}`. Since every target entry is at least rho, the relative error is at most `2^-sqrt(n/2)/rho`. This eventually meets every fixed positive relative tolerance. The proof is the standard scalar-block operation already used by the source. It rejects the target; it is not a new obstruction to count and does not contradict exact rank.

## 3. Complete polynomial implementation of the stipulated prophet construction

### 3.1 A single submodular minimization returns the exact largest flat

Let E have n elements, M be a matroid, D a known subset, P a known flat, and kappa a positive integer. The source uses the largest flat Q containing P that maximizes

`f(Z)=|D intersect Z|-kappa r(Z)`.

On subsets A of `E\P`, define

`g(A)=(n+1)[kappa r(P union A)-|D intersect (P union A)|]-|P union A|`.  (SM)

This is an integer-valued submodular function: restriction of rank to supersets of P is submodular, and both cardinality terms are modular. A constant may be subtracted to normalize `g(empty)=0` before applying a normalized SFM interface.

The primary quantity in square brackets is integral. Changing it by at least one outweighs every possible change, of magnitude at most n, in the last cardinality term. Thus minimizing g first minimizes the primary quantity and then maximizes cardinality among its minimizers.

Every minimizer is closed. If `Z=P union A` is not closed, adjoining its missing closure elements does not increase rank, cannot increase the primary quantity, and strictly reduces the negative-cardinality term. This contradicts minimality. So minimizing over all subsets yields a flat primary minimizer, not a relaxation requiring a rounding step.

The primary minimizers over subsets containing P are closed under union and intersection, by submodularity and equality of their optimal values. Their union is the unique inclusionwise largest one and the unique maximum-cardinality one. Equivalently, source `lem:density` gives this fact on the flat lattice. Consequently the unique minimizer of (SM), after adjoining P, is **exactly the source's Q**. Arbitrary tie-breaking by an SFM implementation cannot change the rule.

A rank evaluation uses at most n independence queries by greedy scanning. All values in (SM) have O(log n+log kappa) bits. With the source's fixed `kappa=2^100`, SFM therefore has polynomial independence-query and bit cost. This is the critical computational step; no enumeration of flats is needed.

### 3.2 Finite path computation and rational arithmetic

Retain every source constant and coin law: `B=2^32`, `kappa=2^100`, and guard/eligibility probability `t=2^-140`. Draw the branch coin, all masks, and parity initially, exactly as prescribed. Dyadic membership probabilities use a bounded number of unbiased bits per label, so the full seed has O(n) bits. Nothing is concealed from the order adversary.

For a positive binary rational p/q, compute the rounded level `floor(log_B(p/q))` using numerator/denominator bit lengths and exact shifted-integer comparisons. The relevant shifts have magnitude bounded by a constant times the observation's bit length. Zero has its separate source branch. At most n levels are listed; gaps between their integer exponents do **not** generate auxiliary path steps.

Perform the source's candidate tests on the revealed labels. Sort the listed groups by their rounded level. For each listed group h and each integer auxiliary time in `[-3m-2,0]`, where `m<=n` is the number of listed groups, compute the nominal density expansion by (SM), then the guarded closure from the source equation `eq:paths`. Compute nominal entries at k+1 before the corresponding guarded entry. Values above zero are E and sufficiently low values are the loop flat by `lem:paths`. Thus O(n²) density calls suffice. Standard greedy rank/closure tests perform the other work. Storing all paths as subsets uses O(n³) bits.

At arrival, compute the candidate test from revealed H, check its listed group, inspect the stored nominal birth and final layer endpoints, and use the source's single conditional-rank test. The unknown full true groups and the optimal comparison set I* never need to be computed. The source's marked-pivot patterns and residual certificates are never enumerated by the algorithm.

Hence preprocessing and all n online decisions together take polynomially many independence queries and polynomial bit operations in n and the total length of the rational samples/values read. Preprocessing uses only samples; later values are read only when their labels arrive. Every path and decision agrees with the source for every seed and every permutation. The one-sample simulation therefore preserves the stated `2^-310` expected guarantee against every measurable full-seed order rule, and prefix feasibility holds deterministically.

This theorem concerns rational observations. It does not provide a Turing encoding or a uniform finite-precision guarantee for arbitrary exact real observations. Approximate rank or erroneous independence answers are also outside its scope.

### 3.3 Significance and adversarial checks

The O(n²) path bound comes directly from the source's activation schedule; the only additional operation is a classical modular perturbation followed by SFM. I therefore classify the result as technical only. A materially new target would need, for example, an improved selection mechanism or a justified reduction in the oracle cost beyond this generic implementation, not an additional corollary of the same simulation.

The diagnostic compares (SM) with exhaustive flat optimization on 2,688 binary representable matroid instances, including loops, parallel columns, multiple primary minimizers, and varied integer density charges. It also checks the residual-density inequality for every subset of each small ground set. These are finite implementation checks; the proof above applies to arbitrary oracle matroids, including nonrepresentable ones.

## 4. A sharp entropy estimate on subcubic graphs

### 4.1 Exact statement

Let G be any finite loopless multigraph on 2m>=2 vertices, with maximum degree at most three (parallel edges counted separately), and at least one perfect matching. For every x in P(G),

`F(x)-H(x) <= (1-1/m) c3 B(x)`,

`c3=log(3)/(2 log(3/2))`.  (SC)

For each m the coefficient is best possible among these graphs. For m>=2 it is best possible even among simple graphs. This is a proved technical deduction, not a general-degree theorem or a significance acceptance.

### 4.2 The scalar three-probability inequality

For `p1+p2+p3=1`, `pi>=0`, put

`h(p)=-sum pi log pi`, `b(p)=-sum (1-pi)log(1-pi)`.

Then `h(p)<=c3 b(p)`. Here and throughout, endpoint products are interpreted continuously. I give the proof so the crucial scalar step is not left as an estimate to assume.

Write c=c3 and `f(u)=-u log u+c(1-u)log(1-u)`. One has `1<c<2`, `f(0)=f(1)=0`, and

`f''(u)=-1/u+c/(1-u)`.

It is negative below `a=1/(c+1)` and positive above a. The continuous function `sum f(pi)` attains its maximum on the simplex. On its boundary, the two nonzero coordinates p,1-p give `(1-c)h(p,1-p)<=0`.

At an interior maximum, the derivatives f'(pi) agree. There cannot be two coordinates strictly greater than a: the second derivative in their difference direction would be positive. There cannot be two coordinates at least a with one strictly greater either. If two equal a, the third is `1-2a<a`, and strict decrease of f' on `(0,a)` contradicts stationarity. If all coordinates are at most a, strict decrease on that interval forces equality, giving p=(1/3,1/3,1/3), where `sum f(pi)=0` by the definition of c.

In the remaining case exactly one coordinate exceeds a. Neither other coordinate can equal a, since f' has its strict minimum there. Thus the other two lie below a and stationarity forces them equal. Write them t,t and the large coordinate 1-2t; then `0<t<1/3`. It suffices to check

`g(t)=2f(t)+f(1-2t)<=0` for `0<=t<=1/3`.

For `u=(1-2t)/t>=1`, direct differentiation gives

`g'(t)/2 = k(u):=log u-c log((u+1)/2)`.

Now `k(1)=0` and `k'(u)=[1-(c-1)u]/[u(u+1)]`. Since `1<c<2`, k increases to a single positive maximum and then decreases to minus infinity. It has exactly one further zero on `(1,infinity)`. As t increases, u decreases. Thus g first decreases and then increases on `(0,1/3)`; its maximum on this interval is at an endpoint. Both endpoint values are zero: g(0)=0 and g(1/3)=3f(1/3)=0. This proves the scalar inequality, including every boundary case.

### 4.3 Lift to matching entropy and prove sharpness

At a vertex v the chosen incident edge is a categorical variable with probabilities `(x_e:e incident to v)`. There are at most three categories; pad with zeroes and apply the scalar inequality. Summing over vertices counts each labelled edge twice, hence

`F(x)<=c3 B(x)`.  (L)

For **any** law p on perfect matchings of mean x, the star choice at each vertex is a function of the whole matching. Thus `Ent(p)>=h(x_delta(v))` at every vertex. Averaging these 2m inequalities yields

`Ent(p)>=F(x)/m`.

In particular `H(x)>=F(x)/m`. Combining with (L) proves

`F-H <=(1-1/m)F <=(1-1/m)c3 B`,

including m=1, zero coordinates, disconnected graphs, and value-one edges.

For sharpness use exactly the source's Klee graphs G_m and means `x_e=1/3` from `ex:prop-klee-face`. The source proves

`H=log3`, `F=m log3`, `B=2m log(3/2)`.

Both inequalities just used are equalities. The graphs are simple for m>=2 and subcubic at every m. At m=1, three parallel edges give H=F and B>0, so the zero coefficient is also optimal. No fresh extremal construction is being claimed.

### 4.4 Why this does not prove the general target

The improvement is exact but elementary after the source's extremizers: the matching law is only used through the entropy of a function. It should not be submitted as a nonroutine finding under the I07/I14/I15/I17 standard.

The scalar step already fails at degree four for coefficient 3/2. For a uniform four-category star, `h=log4` and `b=3log(4/3)`, with `h>(3/2)b`; equivalently `3^9>4^7`. This is not merely a probability vector with no graph realization. In the simple graph K6 minus a perfect matching, edge symmetry gives a feasible uniform mean x_e=1/4. There are eight perfect matchings, so its actual maximum entropy at this mean is log8, and this graph is **not** a counterexample to the target. It shows precisely that the scalar domination route cannot pass to general degree by the same proof.

Finite checks enumerate the source triangle expansions through m=7, retaining all perfect matchings and verifying that the recursively tight cuts leave exactly the three distinguished ones. The scalar inequality is also tested on all 16,471 ternary rational distributions with denominator 180. Floating-point entropy evaluations are diagnostics only; Sections 4.2–4.3 give the general proof.

## 5. Tight-cut decomposition: a complete identity and the unresolved term

### 5.1 Exact entropy gluing

Let G be a loopless labelled multigraph, x in P(G), and S a proper odd set with `x(C)=1`, `C=delta(S)`. Contract the two sides as in source `geom:lem-gluing`, obtaining G1,G2 and restricted means x1,x2. Write `q=(x_e:e in C)`, a probability vector, and `h(q)=-sum q_e log q_e`.

Then

`H_G(x)=H_G1(x1)+H_G2(x2)-h(q)`.  (G)

**Proof.** Every matching in a law of mean x crosses C an odd positive number of times. Expected crossing number one forces exactly one crossing almost surely. Let E_C be its crossing label and M1,M2 the two contracted matchings. They determine the original matching, and E_C is determined by each of them. The conditional entropy inequality gives

`Ent(M1,M2)<=Ent(M1)+Ent(M2)-h(q)`.

Their means are x1,x2, proving the upper bound in (G). Conversely take separate entropy-maximizing laws at x1,x2. Sample E_C with law q and, conditional on its value, sample those laws independently conditioned on that edge. Ignore q_e=0 labels. The **source's existing gluing construction** makes this a valid matching law with mean x, and conditional independence makes its entropy exactly the right side of (G). This proves equality. No compatibility of separate arbitrary completions is assumed: the shared crossing label is fixed before gluing. ∎

Define `D_G=F_G-H_G` and `b(q)=-sum (1-q_e)log(1-q_e)`. Crossing labels occur once in G and twice in the contracted pair, so

`D_G(x)=D_G1(x1)+D_G2(x2)`,

`B_G(x)=B_G1(x1)+B_G2(x2)-b(q)`.  (DB)

Therefore for `E_c=F-cB-H`,

`E_c(G,x)=E_c(G1,x1)+E_c(G2,x2)+c b(q)`.  (SEP)

This positive separator term is the obstruction to the proposed simple induction. Individual inequalities `E_c(Gi,xi)<=0` do not establish the parent inequality. Iterating any finite valid cut decomposition gives

`E_c(root)=sum_leaf E_c(leaf)+c sum_split b(q_split)`.

The missing step for c=3/2 is an **aggregate negative leaf allowance paying this entire separator sum**, or a different global entropy argument. No such estimate is proved here. It is not legitimate to drop the term, replace it by zero because the cut is tight, or assume the contracted means can be optimized independently while changing their crossing marginals.

In the source's Klee family, decomposition into K4 leaves has m-1 leaves and m-2 splits. Each split has q=(1/3,1/3,1/3). Formula (DB) recovers exactly `D=(m-1)log3` and `B=2m log(3/2)`. This is a useful adversarial check: already the source's coefficient-one failure is explained by cumulative separators. It also confirms why sharp face dimension alone cannot be substituted for a new entropy estimate.

The source trace obstruction, combined only with `d>=s-3m+2`, yields `0>=2+(c-2)m`. At c=3/2 this is consistent for m>=4; there is no contradiction. One needs information beyond that scalar trace and codimension pair. The subcubic argument supplies such information only in its restricted degree range.

### 5.2 A precise near-tight statement, with its computational limit

Let `S1,...,Sk` be any fixed finite family of odd sets, and put `delta_j=x(delta(Sj))-1>=0`. Let `beta=(sum delta_j)/2<1/2`. Choose an entropy-maximizing law p of mean x. Let Good mean that every specified cut is crossed once.

There is a feasible mean y on the intersection of those tight-cut faces such that

`||x-y||_infinity<=beta`,

`|H(x)-H(y)|<=h2(beta)+beta log N(G)`,  (NT)

where h2 is binary entropy with natural logarithms. The conditional law `p(.|Good)` realizes y and is entropy maximizing at y. No laminarity is needed for this statement.

**Proof.** If a matching crosses Sj more than once, it crosses at least three times. Markov's inequality applied to the nonnegative excess gives probability at most delta_j/2. A union bound gives `q=P(not Good)<=beta`, so Good has positive probability. Conditioning changes total variation by exactly q, hence changes each edge mean by at most q. Every specified cut then has mean crossing count one.

The conditional law maximizes entropy at its own mean y. Otherwise replace it by a higher-entropy law of mean y and retain the bad conditional law and mixture weight q. Any matching law of mean y crosses every selected cut once almost surely, so the replacement stays in Good. The original overall mean remains x and the mixture entropy increases, contradicting maximality of p.

Let Hg=H(y), and Hb be the entropy of the bad conditional law if q>0. Since Good is determined by the matching,

`H(x)=h2(q)+(1-q)Hg+q Hb`.

Both conditional entropies lie in `[0,log N(G)]`. Thus the absolute difference from Hg is at most `h2(q)+q log N(G)`, which is at most the right side of (NT), because q<=beta<1/2 and h2 increases there. The q=0 case is exact. ∎

This is a standard conditioning bound, not a new entropy algorithm. It depends on an entropy-maximizing input law, and its error grows with log N(G). The supplied FPRAS for a uniform law is not such a sampler at prescribed x. Even if such a sampler were available, rejection sampling would merely implement the conditioning with expected trials at most `1/(1-beta)`; it would not supply the missing separator allowance in (SEP). No dimension-free or relative-error improvement is asserted.

Exact rational diagnostics check the conditional product identity on 9, 45, and 225 crossing-one matchings of K6, K8 and K10, respectively. Separate positive Gibbs laws with dyadic crossing penalties verify the parity/slack bound, exact total variation after conditioning, and every coordinate perturbation bound. These computations support (G)/(NT), not the unresolved general coefficient.

## 6. An explicit obstruction to the global-bin correspondence transfer

In the list proof, different bins are automatically mutually nonconflicting because an actual color has one global bin. To copy this feature to a correspondence assignment, a bin map b on list entries must satisfy

`b(a)=b(a') for every forbidden pair aa'`.  (BIN)

Otherwise selecting entries in different bins could still create a forbidden pair, so stable sets within individual bins would not certify a coloring. Condition (BIN) forces b to be constant on each connected component of the cover graph (the graph with only forbidden-pair edges, as in the source's convention).

For every integer k>=2, take the base cycle `v0 v1 v2 v3 v0`, with `L(vi)={(vi,j):j in Z/kZ}`. On the first three edges match identical second coordinates; on the closing edge match `(v3,j)` to `(v0,j+1)`. These are legitimate perfect edgewise matchings. In the cover, a path of length four runs

`(v0,j)—(v1,j)—(v2,j)—(v3,j)—(v0,j+1)`.

Iterating j visits all 4k entries. The cover is a connected cycle, so every map satisfying (BIN) uses only one bin over the entire assignment. There is no way to give each list a positive fraction of many globally nonconflicting bins by this method.

This failure is not a coloring lower bound for large k. For k>=3 the choices `(0,1,0,1)` at the four vertices form a valid coloring. For k=2 the three identity edges force alternation and the closing shift forbids it, recovering the familiar even-cycle DP obstruction. Thus the bin problem persists even on an elementary colorable graph with arbitrarily large lists, not merely at an insufficient-list endpoint.

Two attempted repairs remain unproved:

* **List-local bins followed by conflict deletion.** Independent local partitions avoid forced global collapse, but leave forbidden pairs between differently named bins. The list proof's arbitrary eligible sets control vertex coverage, not the distribution of these surviving forbidden entry pairs. A bound preserving the linear color budget throughout the adaptive thinning stages is missing.
* **Apply the clique-free DP bound inside the minor recursion.** The source fixes clique order r and maximum degree Delta. Setting r=t from a K_t-minor exclusion does not give an absolute constant; a degeneracy bound does not give a maximum-degree bound for the entire graph. Stars already separate these degree notions. The partitioned adjustment lemma controls weighted local triangles but does not supply the minor-recursion palette reservation or an absolute-in-t quantitative estimate.

These are failures of two specific transfers. They do not show the linear DP statement false, or exclude a different use of the source's stronger local adjustment/independent-set-richness interfaces.

## 7. Reproducibility and handoff

From the repository root run:

```sh
python frontier/experiments/i22_combinatorial_discovery/diagnostics.py
python frontier/experiments/i22_combinatorial_discovery/verify.py
```

The diagnostic uses only the Python standard library. Integer/rational checks verify density optimizers, the tight-face matching supports, conditional probability identities, the cut-slack/TV bounds, and connected correspondence covers. The scalar entropy grid and displayed entropy-identity errors use floating point and are explicitly not proofs. The general arguments are written above. [results.json](../experiments/i22_combinatorial_discovery/results.json) records the finite outcomes.

The artifact seal covers the report, scripts, selected sources, input snapshots, raw query evidence, literature bytes, extracted contracts and read locators. The verifier checks each pinned source against the frozen complete tree using both Git blob SHA-1 and SHA-256; checks primary evidence and exact contract slices; and reports live shared-input drift separately from changes to frozen premises. It does not edit shared inputs or treat index drift as mathematical corruption.

Final verification passes for 14 frozen inputs, 107 pinned source texts, 236 source contracts, 23 read locators, 18 primary-literature artifacts from six papers, eight primary contracts, and 162 sealed artifacts. The separate full-cache search rechecked SHA-256 for all 9,340 texts. The live `frontier/TEN-FINDINGS.md` differs from its frozen input snapshot; this concurrent shared-ledger drift is recorded in [verification.json](../sources/i22_combinatorial_discovery/verification.json). No frozen mathematical dependency failed verification.

**Handoff disposition.** Retain the two complete technical deductions and the scoped gap/false-target records. The best general entropy target still needs the missing separator compensation or a different estimate. The DP target needs a correspondence-compatible replacement for global palette use, together with the required uniform bounds. The polynomial prophet completion and sharp subcubic coefficient are reviewable mathematical results, but their reductions already explain why they fall below the requested substantial-contribution standard. No finding number, acceptance, priority, or count change is requested.
