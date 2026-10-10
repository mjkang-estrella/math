# I37 — Square-exponent avoidance: two constructive attempts and a stronger method obstruction

**Disposition: developed gap report; target C is not proved or disproved. No substantial finding is proposed.** The new completed deductions are an obstruction to *arbitrary nonuniform fair-selector routing with completion-independent local signatures*, a sharp obstruction to a proposed independent-tail coding relaxation, and an exact finite digital covering reduction. The first goes beyond the fixed-branching asymptotic failure in I36. None constructs the required avoiding set, and none is offered as a substitute accepted finding.

The unchanged target is

\[
\forall\eta\in(0,1)\ \exists E\subset[0,1]\text{ compact},\quad
m(E)>1-\eta,\qquad
\forall x\in\mathbb R\ \forall s\ne0\ \exists n\ge1:
x+s2^{-n^2}\notin E. \tag{C}
\]

All pinned OpenAI proofs and their internal operations are accepted at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No upstream truth audit, agents, shared edits, staging, commits, pushes, or other-project writes were performed. Parent integration and any fresh independent proof/significance reviews are separate. The exact current brief, original discovery history, I36 reports, and decisive R3 comparison are frozen or hash-bound in the owned evidence directory.

## 1. Scope, source contracts, and early comparison

The original three-target screen is retained, rather than being restarted with weaker versions of C. Its candidates were: (i) one compact near-full-measure set avoiding all signed affine geometric sequences, all ratios simultaneously; (ii) separable-Hilbert-valued full-sequence Fourier convergence for Bochner LlogL, with the dimension-free Luxemburg-norm weak-L1 maximal estimate; and (iii) C. The first has I36 R2 proof PASS and final R3 **TECHNICAL ONLY**. The second follows by the classical scalar randomization/density transfer from the source's actual weak-L1 norm estimate and is technical. The third is the sole discovery target here. The lower-adjacent-ratio extension is already Jiang–Xi Theorem 1.1, not a fourth discovery. The two constructive routes below attack C itself. Their intermediate sufficient conditions are not independently nominated findings.

I read the complete G/D proof sections and drivers, Jiang–Xi's complete primary proof, KP's published §§3.1–4, Chlebík's Theorem 15 proof and relevant fast-decay/relative-gap passages, and the corrected Kolountzakis 1997 PDF pages 3–11 visually. The 1997 extraction remains garbled, so the visual pages, bound to the identical freshly retrieved PDF, are the reading evidence. The full I02 report and independent review, I36 report and both reviews were read; R011's combined separator/global-maximum operation was checked against its final significance review. No new claim is drawn from the rejected I02 discrete-convexity exceptional set, or from any parked transport/algebra task.

The complete preprint tree has 13,223 entries and 749 manuscript directories; the catalogue's 719 count lags. All 9,340 read-only cached text files, 141,349,121 bytes, were rehashed against their manifest and complete Git tree and searched. This is inventory/search coverage, not semantic reading of 749 manuscripts. The similarity-specific direct pinned companions are G and D. Their 23 text artifacts are reused by exact Git blob, SHA-256 and pinned raw URL; the full cache was not copied.

**G:** *The geometric case of the Erdős similarity conjecture*, October 5, 2026, `build/sections/01-introduction.tex`, `thm:main`, proves the fixed-q version. `03-windows.tex` gives `lem:window-span`, `lem:stability`, `lem:separation`; `04-routing.tex` gives mean density, routing preservation and exact conditional independent-test law; `05-scales.tex` gives local representatives, parameter order, and open repair after taking the supremum over dilation. The full path/URL/Git/SHA record is [pinned-manifest.json](../sources/i37_supergeometric_avoidance/pinned-manifest.json).

**D:** *The dyadic case of the Erdős similarity conjecture*, September 25, 2026, `build/sections/{periodic,windows,routing,tests,scales,repair,global}.tex`. In particular `lem:representatives` uses a deterministic set of scales on each center-exposure atom. Its proof actually produces **one representative for a parameter that agrees for every completion of the tables**, by matching all local finest keys. This stronger signature property, distinguished from mere failure detection, matters below. D's final index-shift rescaling is not valid for square exponents; G's signed summable dilation assembly is the applicable reduction.

**Jiang–Xi:** [2610.11449v1](https://arxiv.org/abs/2610.11449v1), submitted October 8, 2026; fresh abstract bytes still list v1. Lemma 2.1 selects a subsequence with ratios in [α,1/2] from a sequence with positive adjacent-ratio liminf. Lemma 5.1 pays the representative count using `b_n/b_j≤α^{-(j-n)}`. Section 6 explicitly explains the limitation when the lower bound fails. For C, `a_(n+1)/a_n=2^{-(2n+1)}→0`; every increasing-index subsequence has ratios tending to zero as well. This source supplies neither C nor the schedule needed below.

**Chlebík:** [1512.05607v1](https://arxiv.org/abs/1512.05607v1), Theorem 15 requires arbitrarily large finite subsets with normalized minimum gap δ satisfying `−log δ=o(m)`. It really does fail for **every** m-point subset of the square sequence, not merely consecutive blocks. If `k_1<...<k_m`, then

\[
\delta\le {2^{-k_{m-1}^2}\over(7/8)2^{-k_1^2}}
\le {8\over7}\,2^{-[(m-1)^2-1]}. \tag{1}
\]

The numerator bounds the last gap; the denominator bounds the diameter since any two consecutive distinct terms have ratio at most 1/8. Also `k_(m-1)≥k_1+m−2` and `k_1≥1`. Thus the negative logarithm grows at least quadratically. Chlebík's Example 5 allows arbitrarily fast decreases **between inserted fine clusters**; it does not say arbitrary rapidly decreasing sequences are covered. Those clusters are absent here. In fact the largest first gap of any subset is at least 7/8 of its diameter, excluding arbitrary relative fineness too.

**KP:** [published 2025 paper](https://msp.org/apde/2025/18-1/apde-v18-n1-p02-p.pdf), §3.1 already permits moving physical membership; Remark 3.2 separates point separation, point supply, and event complexity; §4 provides multivariable grid-crossing hyperplanes. I36 R3 therefore remains decisive for I36. Those operations do not supply square-sequence trials: at t=1 a physical logarithmic window of width r has at most `√r+2` terms and can be empty. On a bounded normalized copy, the number separated at resolution ε is only `O(√log(1/ε))`; the tail below ε contributes at most a bounded number of additional ε-separated points. This cannot meet the `α(N)/log N→∞` supply of KP Theorem 4.1 at polynomial resolution.

**Kolountzakis 1997:** [correct author PDF](https://eigen-space.org/mk/ps/universal.pdf), Theorem 1 removes almost every parameter pair; Theorem 2 makes the projection of surviving pairs onto the **scale axis** null. Section 2.2 explicitly distinguishes the still-needed small projection onto the **center axis**. For rapidly decreasing subsequences, §2.3 uses near-independence of dilates modulo a small period, integrated over the dilation parameter. Replacing this integration by a supremum is exactly the unpaid step, not a consequence of rapid decay. Theorem 3's finite-gap proof, pp. 9–11, is excluded by (1).

The 2026 two-fold-sumset paper's current [v2](https://arxiv.org/abs/2607.03584v2) is a surrounding comparison, read at its statement/counting interfaces, not a new full-proof dependency. Its extra infinite summand changes the pattern. Its `I(W)J(W)/W→∞` limsup condition does not even give the equal square-exponent double-sum endpoint by direct substitution: both counts are order √W, giving a bounded quotient. In any case avoiding a larger sumset would not prove C.

The [CLP preprint, 2204.12720v1](https://arxiv.org/abs/2204.12720v1), Theorem 1.1 and Corollary 1.2, does apply to the square sequence: take `φ(n)=log((2n+1)log2)`, which is increasing and `o(n)`. But the conclusion is dimension one of avoiding points, not positive measure. Its Proposition 4.4 proves the constructed dimension-one subset has measure zero by a summable digit-event bound and Borel–Cantelli; the ambient Cantor set having measure close to one does not fix this. This is a particularly relevant failed shortcut for digit coding.

The [Feng–Lai–Xiong preprint, 2312.01319v1](https://arxiv.org/abs/2312.01319v1), Theorem 1.1, goes in a different direction: since the square sequence satisfies its upper-ratio condition, every positive-measure E contains `f(2^(−n²))` for a bi-Lipschitz f with `f′(0)=1`. In particular these points have the form `x+2^(−n²)+o(2^(−n²))`. Thus a proposed relaxation demanding avoidance of **all** termwise relative-o(1) perturbations is false. The multiplier/perturbations depend on E. This does not settle the exact affine pattern. These two additional papers were read at their quoted theorem and measure-zero-proof interfaces, not claimed as full-proof audits. No current-status claim here relies on old survey language, third-party summaries, or the withdrawn 2020 manuscript.

**No hidden containment reduction.** The square sequence is a subset of the dyadic sequence, which is the wrong inclusion for transferring avoidance. More generally it contains no infinite affine geometric progression. Such a progression's accumulation point would have to be 0, so its translation is 0 and its scale positive. Taking logarithms would put infinitely many distinct integer squares in an infinite arithmetic progression with a fixed positive step. But consecutive selected squares have unbounded gaps. This is impossible. It likewise contains no affine positive null subsequence with a positive lower adjacent-ratio bound. These arguments reject actual subset/similarity implications, not just heuristic comparisons of gaps.

## 2. Attempt A: completely nonuniform finite routing

The first constructive attempt removes the fixed M, fixed-height and equal-window restrictions. Let T be any finite ordered rooted tree, each internal vertex U having `m_U≥2` children; the last child is default. Give **every edge**, including default edges, a nonempty integer interval `W_e=[a_e,b_e]`, with `a_e≥3`, and place the intervals disjointly in global preorder. Gaps may be arbitrary nonnegative integers. Allow unequal selector biases `0<θ_e<1` on nondefault edges. Choose an integer ℓ≥2 and nested grids

\[
N_b=2^{b^2+\ell},\quad J_b(z)=\lfloor N_b\{z\}\rfloor .
\]

All selector entries are independent Bernoulli-θ_e; all terminal entries are independent Bernoulli-p, independent of all selectors. Route by first successful selector, else default, and set B by the routed terminal bit. This is an actual finite random periodic set, with `Eρ(B)=p`, regardless of tree size or biases.

The proposed gain was to make late windows singletons, use many children there, and increase branching where physical resolution is expensive. Singletons at leaves really have constant local dilation complexity even at huge n. The following exact formulas expose what remains when those leaves are connected into a routing construction.

### 2.1. Geometry and the exact schedule interface

For each noninitial edge e let b′ be the preceding window endpoint. Stability excludes the periodic intervals

\[
[\gamma-2^{1-a_e^2},\gamma),\qquad \gamma\in N_{b'}^{-1}\mathbb Z.
\]

Thus the unstable density is at most

\[
L=\sum_{e\text{ noninitial}}\min\{1,2^{\ell+1+(b')^2-a_e^2}\}. \tag{2}
\]

At stable centers all earlier keys are preserved for every tested n and every t∈[1,2]. Within one window, the center and the tested points have distinct keys: they lie in an interval of length at most 2^(1−9), their distances from the center are at least `2^{-b_e²}`, and distances between distinct sequence terms exceed that lower bound. The cell width is at most one quarter of it. Nesting preserves distinctness at every descendant grid. This includes wraparound and exact boundary points.

Expose the center entry in every selector table. At a first-default vertex U, define the source local predicates Q_i by entering child i on a successful current selector and then using its routed terminal bit. Stability gives `Q_i(x+t2^{-n²})=1⇒x+t2^{-n²}∈B` for n∈W_(U,i). On every fixed center-exposure atom ξ and for every **fixed** t, terminal addresses are distinct after all selectors are conditioned, exactly as in G/D. Consequently

\[
F_U=\mathbb P(\text{all local tests fail}\mid\xi)
=\prod_{i<m_U}(1-p\theta_{U,i})^{r_{U,i}},\qquad r_e=|W_e|. \tag{3}
\]

This is an equality; no independence of adaptive routes is assumed.

Let b_e* be the endpoint of the last edge in e's child block, including e. All local predicates are determined by their block's finest key. One may use

\[
D_U=4+2\sum_{i<m_U}\sum_{n\in W_{U,i}}
\left(1+2^{(b_{U,i}^*)^2+\ell-n^2}\right) \tag{4}
\]

as an upper bound on representatives, by listing every crossing and all intervening intervals. Boundary scales are retained. Unlike an abstract trial count, (4) includes every actual local terminal resolution.

The no-default probability has a finite exact recursion. Write q(L)=1 at leaves, and

\[
q(U)=\sum_{i<m_U}\theta_{U,i}\prod_{j<i}(1-\theta_{U,j})q(U_i).
\tag{5}
\]

Default choices contribute zero because the event being counted is *no default anywhere*. A schedule with

\[
L<p,\qquad q(\mathrm{root})<p,\qquad
D_UF_U<p\ \text{at every first-default-reachable U} \tag{6}
\]

would give an open periodic hitting set of density ≤6p. Here “first-default-reachable” means the root-to-U path uses only nondefault children. To prove the implication, apply (3) on each ξ, union-bound over (4), add (5), integrate the resulting ≤2p failure probability on stable centers and ≤1 elsewhere, enlarge B by density p, and cover the closed exceptional-center projection by an open set of additional excess density p. The estimates are `Eρ(B+)≤2p`, `Eρ(R)≤3p`. At repaired centers, the square-sequence tail converges to the center, so it enters the open cover. This is the source repair with every quantifier preserved.

If (6) could be met for every p, G's assembly with `p_k=(η/64)4^{-|k|}` would remove at most `7η/16` from [0,1], after including both signs. It uses dilation of the hitting sets, not a false shift of square indices. This proves the sufficiency of the interface; it does **not** assert existence of its schedules. The transfer itself is inherited, not a substantial theorem.

### 2.2. A uniform obstruction to the fair-selector schedule

The following rules out much more than letting r tend to infinity at fixed M. It allows **every finite tree above and every choice of its nonuniform disjoint index windows**, with any gaps.

**Proposition 1 (scope: completion-independent local signatures).** Suppose θ_e=1/2 on all nondefault edges. At each first-default-reachable U, require a finite set R_U, fixed before the remaining table entries are exposed, with the property

\[
\forall t\in[1,2]\ \exists t'\in R_U\ \forall\omega\in\xi:\quad
Q_i^\omega(x+t2^{-n^2})=Q_i^\omega(x+t'2^{-n^2})
\quad(i<m_U,\ n\in W_{U,i}). \tag{7}
\]

Then for any p∈(0,1/2), it is impossible to have both `q(root)<p` and

\[
|R_U|(1-p/2)^{T_U}<p\quad\text{at every such U},\qquad
T_U=\sum_{i<m_U}|W_{U,i}|. \tag{8}
\]

This applies to the exact signature construction used by G/D and I36. It is **not** a lower bound on the actual all-dilation failure probability. It does not rule out representatives that only detect failures, a representative chosen from revealed tables, correlated tables, overlapping/reused windows, non-index-window constructions, or bias changes. Those are distinct mechanisms.

**Proof.** First suppose a reachable U has a nonleaf last nondefault child, i=m_U−1. Write a,b for this edge's endpoints and B=b_e*. Since the child is internal, its subtree contains at least two edges with nonempty later windows. Therefore `B≥b+2`. All nondefault windows at U occur by index b, so `T_U≤b`. Hence

\[
\Delta=B^2-a^2\ge(b+2)^2-b^2=4b+4\ge4T_U+4. \tag{9}
\]

Now consider just the coordinate `(i,n=a)` in (7). As t traverses [1,2], the finest local key J_B(x+t2^(−a²)) takes at least

\[
2^{B^2+\ell-a^2}=2^{\Delta+\ell} \tag{10}
\]

distinct values. Indeed, the path length is 2^(−a²), its grid length in cells is that integer, and it traverses less than a full period, including if it wraps through zero.

Different values in (10) are different **completion-independent predicate signatures**, not just an overcount of an unnecessarily fine grid. For any pair t,t′ with distinct J_B keys, set their current-edge selector entries to one and every selector encountered along the all-default path below that child to zero for both points. This sends both local paths to the final leaf of that child subtree, whose incoming endpoint is B. All these spatial keys differ from the corresponding center key: separation holds at b and persists at every finer grid. Thus these choices are consistent with every exposed ξ. Shared selector addresses between the two points cause no conflict, since they receive the same assigned value in each table. At the final leaf assign terminal one to one key and zero to the other. Terminal entries were unexposed and these keys are distinct. The two local predicates then differ in one completion. Consequently they cannot share a representative in (7), proving `|R_U|≥2^(Δ+ℓ)`.

At every fixed representative the failure probability is exactly `(1-p/2)^T_U`. Since `1-p/2>1/2`, (9) gives

\[
|R_U|(1-p/2)^{T_U}>2^{\Delta+\ell-T_U}>1. \tag{11}
\]

Thus (8) cannot hold at this U for any p∈(0,1), even if exact representatives replace the upper bound (4).

It remains to consider trees where **every reachable U has a leaf as its last nondefault child**. Let w_U be the probability the center reaches U without a previous default. At U, choosing the last nondefault leaf has probability `2^{-(m_U-1)}`, exactly equal to the probability of choosing the default. The first events terminate with no default; the second events are disjoint first-default events. Summing their probabilities gives

\[
\mathbb P(\text{no default})\ge
\sum_Uw_U2^{-(m_U-1)}
=\mathbb P(\text{some default}).
\]

A finite route ends at a leaf, so these complementary probabilities sum to one. Therefore `q(root)≥1/2`, contradicting `q(root)<p`. This includes trees with no internal vertices. The two cases exhaust all trees. □

**What this pays.** Late singleton windows genuinely avoid their own quadratic span, but connecting enough of them via a fair routing tree forces either the last-child subtree cost (9) or the stopping-probability loss 1/2. Increasing M after r, increasing M with depth, nonuniform r, or pruning the complete tree do not evade this proposition within its stated signature model. The obstruction uses the **local** child block only; it does not incorrectly charge the globally finest grid.

### 2.3. Biased selectors: a real escape from the proposition, still an unpaid schedule

With θ_e unequal, (3)–(5) remain valid. At a last nondefault leaf the ratio of its stopping probability to the default probability is `θ_last/(1−θ_last)`, rather than one. Taking θ_last small therefore genuinely escapes the 1/2 stopping argument; it is not ruled out by Proposition 1. But it simultaneously reduces the trial rate `−log(1−pθ_last)`.

I examined a comb with a continuing first child and a suffix of terminal children at each vertex. Let the continuing selector have success probability c, and let `A=∏suffix(1−θ_i)`. Conditional on reaching that vertex before a default, the probabilities are `c` of continuing, `(1−c)A` of a default, and `(1−c)(1−A)` of stopping at a nondefault leaf. For d identical levels, with a terminal end after d continuations,

\[
q_d=(1-A)(1-c^d)+c^d=1-A+Ac^d. \tag{12}
\]

Thus `q_d<p` requires `A>1−p`. If the suffix windows are singletons, their total failure exponent obeys, for p<1/2,

\[
\sum_{\rm suffix}-\log(1-p\theta_i)
\le {p\over1-p}\sum_i\theta_i
\le {p\over1-p}[-\log A]
< {p\over1-p}[-\log(1-p)]. \tag{13}
\]

This is order p², too small even to make their fixed-scale failure <p. For example at p≤1/4, (13) is less than 1/9, while `log(1/p)≥log4`. The continuing-child tests would have to supply the missing exponent; they carry a descendant-resolution cost. Making suffix windows longer changes (13), so this is **not** a no-go theorem for biased trees. It identifies the exact tradeoff ignored by “take very small biases and enormous branching.” A successful biased schedule must prove (6), or a stronger weighted replacement for (8), with actual positions and all exposed atoms. No such schedule was obtained.

An alternative is to average poor atoms instead of requiring (8) individually. The sufficient estimate would become a sum of their first-default probabilities times certified conditional failure bounds, together with q(root). Proposition 1 does not exclude this. The present constructions give no bound on that sum tending to zero: replacing every expensive conditional estimate by one loses the probability amplification. This is recorded as an unpaid operation, not silently discarded as impossible.

## 3. Attempt B: square-index digital coding and coherent dilation chaining

This route avoids assigning a finest descendant resolution to every trial. The long gaps between square bit positions suggest coding different shifts on different digit blocks. The obstacle is the common real multiplier: the later bits of `t2^(−n²)` are all shifts of the **same** binary expansion of t. They are neither independent random bits nor arbitrary independently chosen suffixes. The following reduction keeps them exactly.

### 3.1. An explicit finite covering problem sufficient for C

For integers N≥1 and K≥N² set Q=2^K. Seek S⊂Z/QZ such that

\[
\forall j\in\{0,\ldots,Q-1\}\ \forall h\in\{0,\ldots,Q\}
\ \exists n\in\{1,\ldots,N\}:\quad
j+2^{K-n^2}+\left\lfloor{h\over2^{n^2}}\right\rfloor\pmod Q\in S.
\tag{14}
\]

The **unpaid digital covering lemma** is that, for every ε>0, some N,K and S satisfy (14) with `|S|/Q<ε`. This is a concrete finite extremal problem with all coefficients explicit, not a finite check asserted to prove its asymptotics.

**Proposition 2.** If that lemma holds, C follows. More precisely, a single S satisfying (14) gives an open periodic hitting set for all real centers and t∈[1,2] of density at most `3|S|/Q+δ`, for any δ>0.

**Proof.** Take fractional x and write `Qx=j+u`, 0≤u<1. Write `Q(t−1)=h+v`, 0≤v<1; at t=2 use h=Q,v=0. For a given n,

\[
Q(x+t2^{-n^2})
=j+2^{K-n^2}+\lfloor h/2^{n^2}\rfloor
 +u+\{h/2^{n^2}\}+v/2^{n^2}. \tag{15}
\]

Because h is integer, its fractional remainder divided by 2^(n²) is at most `1−2^(−n²)`, and v<1. The last three terms lie in [0,2). Thus the cell of the actual point is either the integer base in (15) or its successor, modulo Q. Choose the witnessing n from (14). The union of closed cells with labels in `S∪(S+1)` contains the point, including exact boundaries. An open enlargement of that union can have arbitrarily small additional density; its measure is at most `2|S|/Q+δ`, hence certainly the stated `3|S|/Q+δ`. The redundant factor three also permits symmetric one-cell padding. This handles every real x by periodicity and both endpoints of [1,2]. Arbitrarily small ε,δ give periodic sets of arbitrarily small density. Apply G's signed, summable dilation assembly to get C. □

This formulation is also quantitatively necessary up to limiting constants for the **periodic hitting problem**: if an open periodic H already hits every (x,t), compactness of `T×[1,2]` gives finitely many indices ≤N and a uniform positive interior margin for at least one hit at each pair. At a sufficiently fine dyadic mesh with K≥N², let S contain those cells whose closures lie in H. The grid pairs `x=j/Q,t=1+h/Q` have a hit with that margin; its cell belongs to S, giving (14), and `|S|/Q≤ρ(H)`. This is an exact translation of the missing periodic problem, not a new proof of it or an independent significance claim.

**Why plain random cells do not close it.** For fixed j,h the N base cells in (14) are distinct (successive sequence differences at this resolution exceed one cell). A Bernoulli-ε set S misses that pattern with probability `(1−ε)^N`. There are Q(Q+1) parameter pairs, so the direct bound is `Q(Q+1)(1−ε)^N`. Since K≥N² and ε is fixed small, this certificate grows rather than vanishes. Repeating the classical union bound in these coordinates pays no new operation. A structured code must use the square quotient relations, or the parameter cover must adapt to surviving failures.

At K=4,N=2, the finite problem is solved exactly: every complement avoiding its 104 distinct two-point edges has at most two cells, attained by two adjacent cells. Thus the smallest blocking S has 14 of 16 cells. One can see this without optimization: the pair differences, with signs, are every nonzero residue except ±1; three vertices always contain a forbidden pair. This is a small boundary test, not an asymptotic lower bound for growing N.

### 3.2. Exact counterexample to forgetting coherent tails

A proposed simplification was to retain each shift's first changed coordinate but give it an arbitrary later suffix. This would remove dilation entropy completely. It is false as a route to arbitrarily small deletion density.

**Proposition 3 (rooted triangular stars).** Let N≥1 and `A⊂{0,1}^N` have more than `2^(N−1)` elements. Then there are x∈A and y_i∈A, 1≤i≤N, such that y_i agrees with x before coordinate i and differs at coordinate i; its later coordinates are unrestricted. Equivalently,

\[
y_i=(x_1,\ldots,x_{i-1},1-x_i,*) . \tag{16}
\]

The threshold 1/2 is sharp: a coordinate half-cube has no such full star. In particular deleting less than half the cube cannot hit every rooted pattern in this independent-tail relaxation.

**Proof.** At N=1 a set of size greater than one is the whole cube. For N>1 both first-coordinate sections are nonempty, since one section contains at most half the cube. At least one section has more than half the size of its (N−1)-cube. By induction choose the center x and all its later-coordinate witnesses in that section; any element of the other nonempty section is y_1. Distinct first disagreement coordinates make all witnesses distinct from each other and x. The half-cube has a fixed first bit, so lacks y_1 for every x. □

The conclusion includes x∈A, respecting the accumulation-center constraint of compact E. It therefore is not an artifact of allowing the center outside the avoiding set. It does **not** assert those freely chosen suffixes can be realized by a single real t. That is precisely why it refutes the proposed relaxation rather than C.

There are real algebraic constraints to exploit instead. In block j, the fractional increment caused by shift i involves `\{2^{n_j²−n_i²}t\}`. Repeated square differences force identical fractional quantities: with indices 1,5,7,

\[
5^2-1^2=7^2-5^2=24,
\]

so those two quantities are exactly equal for every t. Assigning them independently, say 0 and 1/2, is impossible. Conversely, merely noting this equality gives no low-density covering code for all the other digits and their carries. Formula (15) keeps all carries; no probabilistic independence is claimed for digits of a fixed adversarial t.

### 3.3. A rigorous chaining interface, and the unproved part

Here is a sufficient alternative that would avoid a one-shot finest-grid count. Work on a countable product of finite probability spaces, with `(\mathcal F_j)` exposing finitely many coordinates at each stage. Let H_j be nested finite unions of open periodic intervals, determined by those finite exposures, with H=∪H_j and `Eρ(H)≤p`. For fixed center x, maintain a finite family `\mathcal U_j(x)` of closed dyadic parameter intervals, adapted to `\mathcal F_j`, covering every t for which no index has yet been certified to hit H_j. Children refine surviving parents. A cell may be removed only with a verified open-hit certificate covering **every** t in that cell, including its endpoints. Suppose for almost every x

\[
\mathbb E\#\mathcal U_0(x)\le C<\infty,\qquad
\mathbb E[\#\mathcal U_{j+1}(x)\mid\mathcal F_j]
\le\theta\#\mathcal U_j(x),\quad0\le\theta<1. \tag{17}
\]

Then the measure of centers missing H at some t is zero almost surely. Indeed a missed t belongs to a surviving interval at every level, so its probability at fixed x is ≤`Cθ^j` for every j. To check measurability, let R_j be the center projection of the closed set of pairs missing H_j at all indices n≤j. There are only finitely many outcomes for H_j, and each R_j is closed by compact projection, so its indicator is jointly Borel in outcome and center. These closed pair sets decrease. Compactness of the dilation interval implies that their projected intersection equals `R=∩_j R_j`, the centers missing H at some t at every index. Thus R is closed on each outcome and jointly measurable. Tonelli gives `Eρ(R)=0`. Since `Eρ(H)≤p`, there is an outcome of density ≤2p with null exceptional projection. An open cover of that null projection of density <p repairs every center by the null-sequence tail. The result has density <3p. G's signed assembly then applies.

This proof gives the exact measurable object, budget, and conditional extinction obligation that “nets converge” omitted. It also works with a verified varying contraction product tending to zero in place of θ^j. It is only a **sufficient criterion**. I did not construct H_j and certified cells satisfying (17) for square exponents at a summable density budget.

For independent deletions on a uniform finest mesh, a typical parameter interval splits into exponentially many finer intervals while only order √(mesh depth) square-index points become separated. Already the unconditional random-cell estimate after (15) fails. More importantly, surviving cells have been selected using previous table entries, so their future tests cannot be counted with the unconditioned law (3). A usable implementation must expose new addresses conditionally on the survivor sigma-field and prove their distinctness while controlling the expected number of surviving children. Neither KP's deterministic arrangement partition nor the accepted G/D fixed-center exposure supplies this **survivor-conditioned** estimate. That is the exact unpaid lemma for this second route.

## 4. Adversarial review and disposition

The constructive dependencies are:

`G/D routing/repair → exact nonuniform geometry (2) → biased conditional identity (3) → schedule (6) [UNPROVED] → C`;

`square arithmetic → finite covering lemma (14) [UNPROVED] → robust real-parameter enclosure (15) → periodic hitting → C`;

or `nested open random sets + conditional contraction (17) [UNPROVED] → null center projection + open tail repair → C`.

Proposition 1 closes a method question under explicit restrictions, not any of those missing positive arrows. Its proof does not question the accepted geometric operations: for geometric exponents, moving a child endpoint two indices costs a constant exponent, whereas `(b+2)²−b²=4b+4` is what makes (9) dominate **all** incoming trials for square exponents. No analogous contradiction is inferred for G/D.

The key distinction in (7) is the order `∀t ∃t′ ∀ω`. A much weaker failure-detecting set, or `∀ω ∀t ∃t′` with representatives effectively selected after exposure, is not covered by the lower-bound proof. The user-requested “randomized selectors allocating trials” therefore remains a legitimate direction, but needs a new invariant; Proposition 1 must not be quoted as ruling it out. Likewise a lower bound on a union-bound *certificate* is not a lower bound on the underlying failure event.

The independent-tail obstruction retains the center and every finite coordinate. It is a counterexample to a precise combinatorial shortcut, not an invalid exchange of the set/sequence quantifiers. The old density-point obstruction for all variable-ratio sequences stays in force. The digital reduction handles the top endpoint h=Q, wraparound, exact integer boundaries and non-dyadic x,t by the two-cell enclosure. It does not use a dense-set argument without a quantitative margin.

The resulting partial work does not clear the substantial-discovery gate. R011 paid a missing separator term and enabled a stronger no-cut bound at a positive global maximum. Here the positive covering or conditional-survival operation is still missing. An elementary obstruction and a finite reformulation do not replace it. No new acceptance, count, worldwide priority, general superlacunary impossibility, or theorem C is claimed.

## 5. Evidence and reproduction

The [source directory](../sources/i37_supergeometric_avoidance/) freezes the full brief, necessary prior histories, exact source identities, passage records, primary request/response bytes, version records, and complete inventory/search audit. Three saved web query/result payloads are bounded discovery evidence; noisy/irrelevant hits are not mathematical sources. One initial exploratory search was not saved and is not represented as sealed evidence. Fresh primary downloads include G/D's cited comparison papers; the required Jiang–Xi, Chlebík, KP published, and corrected 1997 PDF bytes equal the prior copies. Current version pages and failures are recorded, not inferred from search snippets. The prior wrong guessed Kolountzakis identifier and withdrawn 2020 claim remain excluded.

The [exact diagnostic](../experiments/i37_supergeometric_avoidance/checks.py) checks 295 small ordered trees, 206 nonuniform local bounds, 27 actual-key/table completions separating local predicates (including wraparound), 32 biased-comb stopping recurrences, all 65,812 subsets of binary cubes of dimensions 1–4, the K=4,N=2 finite covering optimum, 720 rational real-to-digital enclosures, 792 finite relative-gap inequalities, and nine biased-selector probability identities. These computations test formulas and boundary cases; the universal proofs are written above. A diagnostic-output bug initially used an overwritten modulus when printing the minimum cover size; it was corrected to the asserted value 14 before sealing. It did not affect the exhaustive optimizer or any proof.

Run from the project root:

```sh
python -B frontier/experiments/i37_supergeometric_avoidance/verify.py
```

The verifier checks the owned seal without regenerating it, immutable input hashes, frozen mutable snapshots, all pinned Git/SHA identities, read-passage hashes, saved response bytes, the complete cache inventory/search reproduction, and byte-for-byte diagnostic reproduction. Shared-ledger drift is reported separately. It writes only its authorized I37 verification output. Earlier author/reviewer verifiers are not rerun and are not claimed as newly reproduced; their sealed reports are historical inputs. **Final result: C remains an explicitly developed gap; no substantial finding proposed.**
