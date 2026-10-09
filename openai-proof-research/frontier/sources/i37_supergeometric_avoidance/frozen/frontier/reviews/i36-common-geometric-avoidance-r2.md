# I36 Theorem A — independent full-proof review R2

**Original-proof verdict: PASS, without mathematical repairs.** The theorem retains the author's full quantifiers: one compact set, every geometric ratio in (0,1), every real center, and every nonzero signed dilation. The measure bound is exactly the claimed `1−7η/16`. This is a proof verdict under the stipulated truth of the pinned OpenAI corpus, **not** a significance, acceptance, priority, or count decision.

The reviewed report is [I36](../iterations/i36-harmonic-analysis-discovery.md), SHA-256 `acc4b9f04d9f90c6dfa4cb54333c2c57026a87d8fc4030ce8f832405b943eb5f`. Its bytes were unchanged throughout this review. I independently reconstructed §§3–6, read the entire report, both complete family-084 proofs and their driver files, the original discovery brief, the review brief and its accumulated objections. All proof-critical constants and quantifier transitions are checked below. No theorem statement has been weakened, and there is no repaired replacement theorem.

The operation that closes the additional obligation is the following combination. Physical displacement windows give a common construction and a linear number of fresh trials uniformly on a compact ratio slab. For a fixed center and exposed first-default vertex, all active-index and local-address changes lie on a finite arrangement of straight lines in `(log t,−log q)`. Only that vertex's child subtrees enter the address count. The arrangement costs an exponential factor `exp(4r log 2)` and a polynomial factor in the absolute final depth; the branching choice beats the first, and the proved linear depth bound pays the second. This is why the construction works for the continuum of ratios, rather than just a prescribed countable family.

## 1. Statement, premises, and review boundaries

For every `η∈(0,1)` there exists a compact `Eη⊂[0,1]` such that

\[
 m(E_\eta)\ge1-7\eta/16>1-\eta,
 \qquad
 \forall q\in(0,1)\ \forall x\in\mathbb R\ \forall s\ne0\
 \exists n\ge1:\ x+sq^n\notin E_\eta.
\]

The set is chosen before all three parameters. The assertion concerns infinite geometric sequences; it does not assert that a prescribed finite prefix is always missed, or that one first-hit bound works for every nonzero scale and ratio. Applying it with `s q^N` gives omissions at indices exceeding every `N`, hence infinitely many distinct omitted points. That is a consequence of this theorem, not an additional finding.

The immutable source revision is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The two family-084 manuscripts are:

- **G:** [The geometric case of the Erdős similarity conjecture](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/main.tex). Its `thm:main` permits dependence on a fixed ratio. The complete proof is in `01-introduction.tex`, `01-history.tex`, `02-periodic.tex`, `03-windows.tex`, `04-routing.tex`, and `05-scales.tex`.
- **D:** [The dyadic case of the Erdős similarity conjecture](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026/build/paper.tex). All eight proof sections were read: introduction, periodic, windows, routing, tests, scales, repair, global.

The accepted interfaces include G's `lem:window-span`, `lem:stability`, `lem:separation`, `lem:density`, `lem:routing`, `lem:independent-tests`, `lem:conditional-scales`, and its open repair; D provides the same mechanism with explicit full-center exposure and local-subtree accounting. Their truth is a premise. The work here checks the proposed alteration of their inputs and the resulting deduction; it does not reopen the upstream truth question. Source identities, raw URLs, exact contracts and full-section read hashes are in [the R2 source directory](../sources/i36_common_geometric_avoidance_r2/pinned-manifest.json).

The current ledger records five accepted findings. The frozen I02 report and review were read in full: its wrong avoiding-family exceptional set concerns discrete convexity and supplies no permissible bridge here. Its unrestricted-spread and Kakeya failures remain failures. R011 and the relevant final-significance mechanism passages were read to preserve the separate gate. This review neither changes that gate nor judges whether I36's additional operation clears it.

## 2. Independent reconstruction of the common periodic lemma

Fix `0<q−<q+<1` and `0<p<1`. I reconstruct an open 1-periodic set `H` of density at most `6p` satisfying

\[
 \forall x\in\mathbb R\ \forall t\in[1,2]\ \forall q\in[q_-,q_+]\
 \exists n\ge1:\ x+tq^n\in H. \tag{P}
\]

All construction parameters are selected before `x,t,q`. Center-dependent representatives are only an instrument in the proof; they do not change the random set.

### 2.1. Parameter order and deterministic geometry

Put `Lmin=−log q+`, `Lmax=−log q−`, and `κ=(log 2)/(2Lmax)`. These numbers are finite, with `0<Lmin≤Lmax`. Choose the parameters in this order:

1. Integer `ℓ≥1` with `2^(−ℓ)≤(1−q+)/4`.
2. Integer `M≥2` with `β=p(M−1)κ/2>4log 2+1`.
3. Integer `d≥1` with `(1−2^(1−M))^d<p`.
4. The complete ordered M-ary tree of height d, its finite edge count `K=Σ_{h=1}^d M^h`, then integer `g≥1` with `K 2^(ℓ−g)<p`.
5. An integer `r0≥max(1,2Lmax/log 2)`, ultimately chosen large enough in §2.5.

The finiteness of the enormous tree is sufficient; no feasible computational size is asserted. In particular, choosing `M` does not force a dependence of `d` or `g` on the later `r0`.

Define `r1=r0`, `σ1=M r0+(M−1)g`, and, for `h≥2`,

\[
 r_h=\max(r_0,g+\sigma_{h-1}),\qquad
 \sigma_h=M(r_h+g+\sigma_{h-1})+(M-1)g.
\]

Place intervals `[ae,be]` of **real coordinate length** `rh`, so `be=ae+rh`, on every edge in preorder, starting at 3 and placing the next start at the previous end plus g. These are logarithmic-distance intervals, not integer-index windows. Accordingly there is no inherited `+1` in the length or gap formula. The edge-plus-child block has span `rh` at height one and `rh+g+σ(h−1)≤2rh` otherwise. Its last endpoint `be*` therefore satisfies

\[
 b_e^*-a_e\le2r_h.
\]

The final endpoint is `B=3+σd`. All edges, including default edges and their descendants, receive intervals. This is necessary for terminal resolution and subtree-span control.

Set `Ze=[2^(−be),2^(−ae)]` and `Ie(t,q)={n≥1:tq^n∈Ze}`. Writing `L=−log q`, the admissible real n form

\[
 [(a_e\log2+\log t)/L,\ (b_e\log2+\log t)/L].
\]

Its left endpoint is strictly positive. A closed interval of length u contains at least `u−1` integers, so

\[
 |I_e(t,q)|\ge r_h\log2/L_{\max}-1\ge\kappa r_h.
\]

The last inequality uses the explicit lower bound on r0. It is valid at all endpoint equalities and does not assume that the active indices are constant as q changes. All active indices are at most

\[
 J=\left\lceil (B+1)\log2/L_{\min}\right\rceil,
\]

because `t≤2` and `tq^n≥2^(−B)`.

Use the common dyadic grids `Nb=2^(b+ℓ)`, real-line boundary lattices `Γb=Nb^(−1)Z`, and periodic half-open keys `Jb(z)=floor(Nb{z})`. Every finer key determines each coarser key, including at integers.

For every noninitial edge, let b′ be its immediate predecessor's endpoint. Declare x stable if `(x,x+2^(−ae)]∩Γb′` is empty for every such edge. Failure for one transition occupies the periodic intervals `[γ−2^(−ae),γ)`, of density at most `2^(ℓ−g)`. Thus the unstable-center density is less than p. This set is deterministic and independent of **both** t and q.

For a stable x, each displacement z in Ze preserves the predecessor key, and by nesting every earlier key. The excluded left endpoint is correct: beginning at a boundary and moving a short distance right stays in its right-hand cell. Landing at the next boundary is forbidden by the included right endpoint. The real-line lattice includes wraparound boundaries.

Conversely, at grid be, the center and all points `x+tq^n`, `n∈Ie(t,q)`, have distinct keys. They lie in an interval of length at most `1/8`. Distances from the center are at least `2^(−be)`; distances between two distinct active points are at least `(1−q+)2^(−be)`. The cell width is at most one quarter of the latter bound. Circular distance equals real distance in this short interval. Equal periodic keys would force distance less than the cell width, which is impossible. Nesting preserves distinctness at every finer grid.

These arguments establish the exact deterministic hypotheses needed by the adapted routing construction. No continuity approximation from a dense set of ratios is involved.

### 2.2. The random set and full center exposure

Give every nondefault edge an independent fair-bit table indexed by its grid cells. Give every leaf an independent Bernoulli-p table at its incoming-edge grid. All entries across all tables are independent. Route a point by the first nondefault child with selector one, using the final child when all selectors vanish. At the selected leaf, its addressed terminal bit defines membership in `Bω`.

The finite probability space can have arbitrary Bernoulli parameter p. For each outcome the set is a finite union of half-open cells per period. Conditioning on **all** selectors fixes a point's terminal address without changing its Bernoulli-p law. Integration gives `Eρ(Bω)=p`.

For a fixed x, expose its addressed entry in **every** selector table, not just those on its route. This is a deterministic coordinate subset of the product probability space. Each atom ξ fixes the center route and leaves every unexposed selector coordinate independent and fair; no terminal coordinate was exposed.

The probability of no default on the center route is exactly `(1−2^(1−M))^d`. One reveals the reached vertex's selectors only after its ancestor decisions; the new vertex uses different tables. This argument does not require the route itself to be independent of earlier choices.

On an atom with a first-default vertex U of height h, let `r=rh` and `ei=(U,i)` for `i<M`. Define the local leaf `Li(y)` by routing from child i, regardless of whether the actual root route enters that child, and define

\[
 Q_i(y)=S_{e_i}(J_{b_{e_i}}(y))
 T_{L_i(y)}(J_{b(L_i(y))}(y)).
\]

For an active displacement in Zei, stability preserves all ancestor decisions needed to reach U. Before the first default, each chosen ancestor child is nondefault; its selector and all preceding rejected selectors occur earlier in preorder. At U the selectors of children preceding i also occur earlier and retain their exposed zero values. Consequently `Qi(x+tq^n)=1` forces the actual route to enter child i and to read a terminal one. Therefore

\[
 Q_i(x+tq^n)=1\ \Longrightarrow\ x+tq^n\in B_\omega. \tag{1}
\]

No reverse implication is required. If Qi vanishes, the actual route may visit an unrelated much finer subtree; its addresses are irrelevant to this sufficient test and must not be charged to the representative count.

### 2.3. The conditional failure identity

Fix `(t,q)` before revealing unused entries. There are

\[
 T(t,q)=\sum_{i<M}|I_{e_i}(t,q)|\ge(M-1)\kappa r
\]

local trials. For fixed i, separation proves that their current-edge selector addresses are pairwise distinct and different from the center's exposed address. Different i use different tables. Their selector bits `Ai,n` are thus independent fair bits conditional on ξ.

Now condition on all selectors. Every local terminal address is fixed. Different child indices have disjoint leaf tables. Different leaves also have different tables. If two trials below the same child select the same leaf, its incoming-edge grid refines the current-edge grid, where their keys were already distinct. Their terminal addresses are therefore distinct in this last case as well. This remains true for trials whose current selector is zero; including them causes no problem.

Conditional on all selectors, these terminal bits are independent Bernoulli-p variables. Precisely the trials with current bit one need a terminal zero for failure. Hence, after averaging over the selectors conditional on ξ,

\[
 \mathbb P(\text{all active local trials fail}\mid\xi)
 =\mathbb E[(1-p)^{\sum A_{i,n}}\mid\xi]
 =(1-p/2)^{T(t,q)}\le e^{-\beta r}. \tag{2}
\]

This reasoning permits completely dependent local routes. It never multiplies terminal probabilities before their addresses are fixed, and never chooses a parameter using unused bits.

### 2.4. A representative for every parameter, including all boundaries

Set `v=log t` and `u=−log q`; the parameter domain is the closed rectangle `[0,log 2]×[Lmin,Lmax]`. For every `i<M` and `1≤n≤J`, include the active-set boundary lines

\[
 v-nu=-a_{e_i}\log2,\qquad v-nu=-b_{e_i}\log2.
\]

Also include `v−nu=log(γ−x)` for every `γ∈Γbe_i*` with `γ−x∈Zei`. Such differences are positive, so the logarithm is defined. The finest **local** grid has at most

\[
 1+N_{b_{e_i}^*}(2^{-a_{e_i}}-2^{-b_{e_i}})
 \le1+2^{\ell+2r}
\]

boundaries in that displacement interval. This counts real-line boundaries, including those at integer wraparound, not just boundaries in one arbitrarily chosen period.

The total number of listed lines before deduplication is at most

\[
 L_0=(M-1)J(3+2^{\ell+2r}).
\]

Add the four rectangle sides and remove duplicates. An arrangement of m distinct lines has at most `m(m−1)/2` vertices, `m²` open one-dimensional pieces and `1+m(m+1)/2` open two-dimensional regions, in total `2m²+1`. Parallelism or concurrency only reduces these bounds. With the rectangle sides included, restriction to the rectangle introduces no uncounted stratum; intersections of convex strata with it cannot split into disconnected pieces. Thus one point from every nonempty stratum of **each** dimension gives at most

\[
 8[5+(M-1)J(3+2^{\ell+2r})]^2 \tag{3}
\]

representatives, a generous upper bound for `2(L0+4)²+1`.

On a stratum all line signs, including zeros, are constant. The active sets are therefore exactly constant. While an index is active, its point cannot cross any boundary of its finest local grid without changing one of those signs. If the stratum lies on a boundary line, the point is exactly at that fixed boundary and always receives the same right-hand key. Thus every active finest local key is constant. It determines all coarser selectors and terminal addresses used by Qi, for every completion of the random tables. Inactive indices need no key control.

This proves a deterministic representative identity, not an almost-everywhere statement. The representatives depend only on x, U and the deterministic construction. Given ξ they are fixed before unused bits are seen. No measurable choice of representatives as a function of x is needed: the probability inequality is pointwise in x, and the later integration is of explicitly closed exceptional-center sets.

If any parameter pair misses `Bω` at all indices through J, (1) makes all its active local tests fail. Its representative has the same active tests. Apply (2) separately to each representative and take a union bound; no independence between representatives is assumed. This yields (3) times `exp(−βr)` as the conditional failure bound.

### 2.5. Explicit resolution of the apparent circularity

The preceding expression still contains J, which depends on r0 through the entire tree. That dependence cannot be hidden in a constant. The report correctly pays it.

Define `A0=0`, `Ah=4M(1+A(h−1))`. Induction gives `σh≤Ah(r0+g)`. At height one this is immediate. For higher heights, `rh≤r0+g+σ(h−1)` and therefore

\[
 \sigma_h\le Mr_0+(3M-1)g+2M\sigma_{h-1}
 \le4M(1+A_{h-1})(r_0+g).
\]

Consequently `B≤3+Ad(r0+g)` and

\[
 J\le C_J(r_0+g+1),\qquad
 C_J=1+(\log2/L_{\min})(4+A_d).
\]

Here `Ad,CJ` are fixed before r0. With `J≥1`, the bracket in (3) is at most `9MJ 2^(ℓ+2r)`. Hence the conditional bound is at most

\[
 C_0(r_0+g+1)^2e^{-\gamma r},\qquad
 C_0=648M^2 2^{2\ell}C_J^2,\quad
 \gamma=\beta-4\log2>1. \tag{4}
\]

Every quantity in C0 and γ was fixed at stages 1–4. A sufficiently large integer r0, also satisfying its earlier lower bound, therefore makes

\[
 C_0(r_0+g+1)^2e^{-\gamma r_0}<p.
\]

Since every rh is at least r0, (4) is less than p at every possible first-default vertex. There is no additional factor for the number of vertices: the exposure atoms partition the probability space, and each conditional estimate is at most p. Adding the less-than-p no-default event yields, for every stable x,

\[
 \mathbb P(\exists(t,q)\ \forall 1\le n\le J:\
 x+tq^n\notin B_\omega)\le2p. \tag{5}
\]

The use of a height-dependent r does not alter the polynomial prefactor. This is the decisive uniform closing argument.

### 2.6. Measurable exceptional centers and repair

Enlarge each outcome to an open periodic `Bω+⊃Bω` with added density at most p. This is possible because its half-open cells have only finitely many endpoints per period. The finite outcome space avoids any measurable-selection issue.

Let `Rω` consist of centers for which **some** parameter pair in the full compact rectangle misses `Bω+` at every index `1,…,J`. On the circle this is the projection of a closed subset of `T×[1,2]×[q−,q+]`: each finite point map `(x,t,q)↦x+tq^n mod1` is continuous and the target complement of `Bω+` is closed. Compactness makes the projection closed. In particular its indicator is measurable, also jointly with the finite outcome variable.

For stable x, membership in Rω implies the event in (5); unstable centers have probability at most one. Therefore

\[
 \mathbb E\rho(R_\omega)\le2p\rho(S)+\rho(S^c)\le3p,
 \qquad \mathbb E\rho(B_\omega^+)\le2p.
\]

Choose one outcome with `ρ(B+)+ρ(R)≤5p`. Choose an open periodic neighborhood `V⊃R` with `ρ(V)≤ρ(R)+p`. Then `H=B+∪V` is open, periodic, and has density at most `6p`.

If `x∉R`, negating its definition gives a hit for **every** parameter pair among indices through J. If `x∈R`, openness of V and `tq^n→0` put the tail in V. The convergence is even uniform on the compact parameter rectangle, but only the pointwise conclusion is required. These tail indices may exceed J. This proves (P) at every center and parameter.

The repair concerns centers that miss at some parameter, after the simultaneous probability bound. Integrating an almost-everywhere statement in the ratio variable would not suffice, and is not what happens here.

## 3. The global measure and signed-scale audit

For `j≥3`, set `Qj=[1/j,1−1/j]`. Their union is (0,1). For `k∈Z` set

\[
 p_{j,k}=(\eta/64)2^{-(j-2)}4^{-|k|}.
\]

Each belongs to (0,1). Apply (P) on Qj with this budget and choose all sets `Hj,k` before any target q,x,s. Let

\[
 C=\bigcup_{j\ge3,k\in\mathbb Z}
       (2^kH_{j,k}\cup(-2^kH_{j,k})),\qquad
 E_\eta=[0,1]\setminus C.
\]

C is open and symmetric, hence Eη is compact. For either sign,

\[
 m((\pm2^kH_{j,k})\cap[0,1])
 \le\max(1,2^k)\rho(H_{j,k}).
\]

For `k≤0`, the interval contains exactly `2^(−k)` periods; after reflection one integrates over the corresponding negative integer number of periods. For `k>0`, the normalized interval `[0,2^(−k)]`, or `[-2^(−k),0]` after reflection, is contained in one unit-period interval. This proves the bound for both signs without any assumption on where the mass lies in a period.

The j-budget sum is one. The negative k sum is `Σ_{m≥1}4^(−m)=1/3`, the k=0 term is one, and the positive k sum is `Σ_{k≥1}2^(−k)=1`. Thus

\[
 m(C\cap[0,1])\le12\sum_{j,k}p_{j,k}\max(1,2^k)
 =\frac{12\eta}{64}\left(\frac13+1+1\right)=\frac{7\eta}{16}.
\]

Given q and `s>0`, choose j with `q∈Qj` and k with `s=2^k t`, `1≤t<2`. Apply (P) at center `2^(−k)x`; multiplication by `2^k` gives a point `x+sq^n∈C`. For `s<0`, apply the positive assertion to `−x,−s` and reflect. No index shift by a power of two is used. The missing point lies outside Eη whether or not it lies in `[0,1]`.

The construction is therefore independent of q as asserted. Approaching q=0 or q=1 requires other slabs and different finite constants; no uniform endpoint estimate was assumed.

## 4. Adversarial conclusions and sideclaim scope

The main potential failure modes were resolved as follows.

- The current selector entries avoid the center's exposed coordinate **in their own table**, by geometric separation. Sharing a numerical cell index across different table names is harmless.
- Leaf choice can be adaptive and dependent across trials. Conditioning on all selectors first, and then checking the full `(leaf,key)` address, gives the required product terminal law.
- Stability preserves all previously consulted ancestor and sibling keys. Later unrelated siblings are unnecessary for the successful-route implication.
- Moving indices are controlled by explicit entry/exit lines; closed windows and all lower-dimensional strata are retained. A fixed-index discretization would not prove the result.
- The lattice count is local to one child block. Charging the entire construction's finest grid would lose the exponent comparison.
- The total index depth is paid via the proved linear bound for J. The order `M,d,g` before r0 is respected throughout.
- Raw finite-space probabilities do not require parameter-event regularity. The center integral is taken only after open enlargement and compact projection have established Borel measurability.
- Countable assembly takes **already uniform** slab constructions. It does not exchange a per-ratio existence quantifier with an uncountable intersection.

The density-point warning in author §9 is correct: at a density point, sufficiently small intervals `[x+0.9·2^(−k),x+1.1·2^(−k)]` meet E. Choosing one point from each produces adjacent ratios in `[9/22,11/18]⊂[1/3,2/3]`. Hence a positive-measure set cannot avoid all sequences with variable ratios in that interval. This does not counterexample A: those sequences have independent choices at infinitely many indices, whereas the geometric family has the finite-dimensional line partition just proved.

**Separate sideclaim check, not part of the A verdict.** I checked the source's actual `cor:fourier-weak-l1` and the author's §7 reduction. The quoted bound is indeed a Luxemburg-norm weak-L1 bound. The Rademacher second/fourth moments, Paley–Zygmund constant `1/12`, expected norm bound `4a`, and resulting `48√2 CF` maximal constant are valid. Finite-dimensional projection and Orlicz-norm polynomial density give the stated separable-Hilbert limit. The finite-r variation counterexample uses the N unit Fourier increments and a `O(log²N)` input norm, so rules out that norm estimate, not a.e. convergence. These are technical deductions. The supergeometric argument in §8 remains a failure of the stated representative/trial budget; it is not a theorem of nonuniversality or impossibility. None is needed to prove A or receives a count/significance judgment here.

## 5. Exact diagnostics and provenance

The independent [checks.py](../experiments/i36_common_geometric_avoidance_r2/checks.py) uses exact integers and fractions. Its new parameter-partition diagnostic constructs full small arrangements in logarithmic coordinates. Coordinates are rational linear combinations of logarithms of primes; signs are determined exactly by clearing denominators and comparing integer products. It uses no floating-point logarithms or tolerances.

For each of three centers, it enumerates every vertex, clipped edge and adjacent two-dimensional face of a local parameter rectangle, including wraparound and a center not aligned with the finest grid. It compares sign signatures with independently computed periodic keys, samples multiple points of each edge, checks rational `(t,q)` points directly via rational powers, and verifies Euler's subdivision identity. The fixture tests the partition mechanism; its small windows are not claimed to satisfy the full probabilistic construction's large-r0 hypotheses.

The output records 159 vertices, 237 edges and 81 faces across the three arrangements, with 948 exact signature evaluations and 622 wraparound active-point evaluations. Independent recursion checks cover 108 parameter trees and 6,066 edges. Conditional checks cover 192 deliberately dependent-route configurations, three exact failure identities and 64 full-center exposure patterns. Certified integer comparisons illustrate exponential domination after constants are fixed. The signed-scale coefficient is checked exactly as `7/16`. These finite checks support the formulas; the universal theorem rests on §§2–3 above.

The author's verifier was reproduced with its source and seal unchanged. It normally writes its own `verification.json`, which is outside this review's authorized write scope. [reproduce_author.py](../experiments/i36_common_geometric_avoidance_r2/reproduce_author.py) executes the original file with its original `__file__` and captures only that single report write in memory. All 126 author files monitored before and after, including its report, seal and pre-existing verification output, remained byte-identical. The verifier reports PASS for 124 sealed files, 39 pinned files, 21 contracts, 32 read passages/visual pages and 19 primary responses; all original diagnostic counts reproduce. Its two shared-ledger drifts are retained separately. It validates the recorded 9,340-file search count and the complete 749-manuscript inventory; it does **not** rehash every corpus-cache file. This review makes no such claim either.

The exact review brief (including the original discovery brief and all accumulated objections) is frozen in [full-brief.txt](../sources/i36_common_geometric_avoidance_r2/full-brief.txt). The author report and core obligations are copied into the owned frozen directory, and the remaining immutable author/prior evidence is bound by SHA-256 in [input-manifest.json](../sources/i36_common_geometric_avoidance_r2/input-manifest.json). The 24 selected pinned-file identities include all G/D text artifacts and the optional Fourier final section. All 26 logged reading passages and 18 retained contracts are checkable against their source bytes. Mutable shared ledgers are explicitly marked and checked separately from mathematical inputs.

Fresh web and HTTP reads retained version-specific primary metadata for [Burgin et al., 2210.09284v1](https://arxiv.org/abs/2210.09284v1) and [Jiang–Xi, 2610.11449v1](https://arxiv.org/abs/2610.11449v1). The former's Question 1 asks for some affine geometric sequence; its Theorem 1.1 fixes the center at zero and Proposition 3.3 is an almost-every-parameter assertion. The latter's Theorem 1.1 concerns a given sequence and Corollary 6.1 a prescribed countable family. These passages were read from retained version-specific primary texts. Neither is used as a proof premise here. This is a scope check, not a fresh full-literature or significance audit.

No fresh retrieval failed. The bound historical failure record preserves the wrong guessed Kolountzakis identifier (actually Temme), nonexistent-v2 attempt and broken PDF text extraction. The wrong paper and withdrawn 2020 claim are excluded; I did not represent the author's visual reading of the corrected historical PDF as a new R2 visual read. The exact primary read scope and failures are recorded in [read-scope.json](../sources/i36_common_geometric_avoidance_r2/read-scope.json).

Run from the repository root:

```sh
python frontier/experiments/i36_common_geometric_avoidance_r2/verify.py
```

The verifier checks the owned artifact seal, immutable inputs, pinned Git blobs against the complete tree, passage hashes, contracts, fresh response bytes, and independent diagnostic reproduction, and re-executes the unchanged author verifier with its output intercepted. It reports shared-ledger drift separately. It does not regenerate a seal. No subagents, shared edits, staging, commits, pushes or publication were performed.

**Disposition:** original Theorem A and its proof PASS without repairs. Parent integration and the separate significance review remain independent gates; this report changes no accepted-finding count.
