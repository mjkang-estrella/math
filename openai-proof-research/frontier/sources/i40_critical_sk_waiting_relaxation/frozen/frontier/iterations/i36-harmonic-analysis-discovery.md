# I36 — A common avoiding set for every geometric ratio

**Status: complete proposed deduction, submitted to the parent for fresh full-proof and separate significance review. No acceptance, finding number, count increment, or worldwide-priority claim.** Under the stipulated pinned corpus, the construction below gives, for each η>0, one compact E⊂[0,1] of measure >1−η containing no signed affine copy of {qⁿ:n≥1} for **any** q∈(0,1). The set is independent of q. The proposed additional operation replaces sequence-index windows by physical-distance windows, permits the tested indices to vary with the parameters, and controls their simultaneous changes by an arrangement of lines in (log t,−log q). The source's random routing, conditional terminal independence, and exceptional-center repair are inherited and are identified as such.

Three primary targets were screened: this simultaneous-ratio theorem, Hilbert-valued full-sequence LlogL Fourier convergence, and nonuniversality of {2^(−n²):n≥1}. The second has a complete standard randomization reduction and is **TECHNICAL ONLY**. The third retains an explicit entropy-budget gap. Two additional nearby screens reject the already-published lower-adjacent-ratio extension and a false finite-variation endpoint upgrade. Thus only the simultaneous-ratio theorem is proposed for review; none of the other deductions is counted.

All OpenAI results and their internal operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are assumed true. This report does not audit them. No agents were launched. All writes are restricted to this report and `frontier/{sources,experiments}/i36_harmonic_analysis_discovery/`. No shared indexes, staging, commits, pushes, or other projects were changed.

## 1. Research obligations and source screen

The operative full brief is frozen in [full-brief.txt](../sources/i36_harmonic_analysis_discovery/full-brief.txt). The rules, count ledger, iteration index, complete I02 cross-field report and independent review, R011, and its final significance review are frozen or bound by SHA-256 in [input-manifest.json](../sources/i36_harmonic_analysis_discovery/input-manifest.json). R011's standard is the **combined missing operation**, not a changed display formula: the rooted allowance must cancel separator cost and make the no-cut bound legal at a positive global maximum. I14, I15, I17, and I30 remain technical despite proof PASS. The historical F and technical R records do not enter the five accepted findings.

I02's unrestricted-spread threshold counterexample, wrong avoiding-set exceptional set, dimension-four-only Kakeya lift, and classical rank-one obstruction are not reused as discovery routes. This report has no transport, matroid, MCM, signed Saxl, prime-reservoir, kinetic, or endpoint-varifold claim. In particular, it does not overlap I35's splitting-invariant entropic bias work.

The **complete** `sources/preprints-tree.json` was parsed: 749 manuscript directories, not the stale catalogue's 719. The complete catalogue was parsed for family entries, and all 9,340 read-only cached text files were searched. The inventory, exact queries, file hits, line hits, and prior-report search are retained in `complete-manuscript-inventory.txt`, `inventory-screen.json`, `corpus-search-audit.json`, and `prior-search-audit.json`. This is a full inventory/search audit, not a claim to have semantically read all 749 manuscripts. The actual selected statements were read. Both family-084 manuscripts were read completely, including the dyadic companion's entire proof; family 075's introduction and complete final Fourier deduction, including the weak-L1 corollary, were read. The screen found no additional direct pinned companion supplying simultaneous ratio avoidance. All 39 text files of these three manuscripts are locally frozen with checked Git blob and SHA-256 identities. The full cache was not copied or modified.

### Exact contracts

All following paths are below the pinned raw root
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`.
The [pinned manifest](../sources/i36_harmonic_analysis_discovery/pinned-manifest.json) gives complete URLs, bytes, Git blobs, and SHA-256 values; [read-passages.json](../sources/i36_harmonic_analysis_discovery/read-passages.json) gives line ranges and passage hashes.

**G:** `preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/sections/01-introduction.tex`, `thm:main`: for every **fixed** q∈(0,1) and η∈(0,1), there is compact E_{q,η}⊂[0,1], m(E)>1−η, avoiding x+sG_q for every x∈R and s≠0. It explicitly permits E to depend on q. `02-periodic.tex`, `prop:periodic`, gives an open periodic hitting set of density ≤6p for every center and t∈[1,2], still with q fixed.

The inherited proof interfaces are `03-windows.tex`, `lem:window-span`, `lem:stability`, `lem:separation`; `04-routing.tex`, `lem:density`, `lem:routing`, `lem:independent-tests`; and `05-scales.tex`, `lem:conditional-scales`, equations `eq:local-boundaries`, `eq:branching-choice`, and `eq:exceptional-centers`. G's grids depend on q, its index windows are fixed, and its representatives vary only t. None of those statements already quantifies a common random set over q.

**D:** `preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026/build/sections/periodic.tex`, `lem:periodic`; `windows.tex`, `eq:padding`; `tests.tex`, `lem:fixed-scale`; `scales.tex`, `lem:representatives`, `prop:raw-failure`; `repair.tex`; and `global.tex`. D supplies the same local-subtree routing architecture for q=1/2. It does not give the continuum-ratio representative lemma below. Its index-shifting final dilation trick is special to 2^(−n); here we use G's summable signed-dilation construction instead.

**F:** `preprints/Almost-everywhere-Fourier-convergence-in-L-log-L-September-23-2026/build/sections/01-introduction.tex`, `thm:main`, and `11-fourier.tex`, `cor:fourier-weak-l1`, `eq:fourier-weak-l1`. On normalized T, Φ(u)=u log(2+u), the actual source includes

λ μ{sup_N |S_N f|>λ} ≤ C_F ||f||_Φ.

This is a **Luxemburg-norm** weak-L1 estimate, not the modular inequality μ{S*f>λ}≤C∫Φ(|f|/λ). The proof below never substitutes the latter. No variational or coordinatewise different-frequency estimate is inferred from a.e. convergence.

## 2. Candidate screen and early primary comparison

### A. One set for all geometric ratios — selected

For every η∈(0,1), seek compact E_η⊂[0,1] such that

m(E_η)>1−η, and ∀q∈(0,1) ∀x∈R ∀s∈R\{0} ∃n≥1: x+sqⁿ∉E_η.  (A)

G supplies the probability amplification and repair for one q. Intersecting countably many fixed-q avoiding sets covers only countably many ratios. A dense countable set of parameters is insufficient: avoidance is an open condition in q for a fixed witnessed finite hit, and an open dense set need not be the full interval. Compactness would require coverage of **all** parameters before a finite subcover can be taken. No such coverage is supplied by density.

The early primary comparison found an exact significance target: **Question 1** of Burgin–Goldberg–Keleti–MacMahon–Wang, [arXiv:2210.09284v1](https://arxiv.org/abs/2210.09284v1), asks whether every positive-measure set contains some translated geometric sequence with some ratio. Its Theorem 1.1 only excludes progressions centered at zero; Proposition 3.3 excludes almost every parameter triple. Neither has (A)'s all-center/all-ratio quantifiers. This report's proposed theorem would give a negative answer to that question, under the stipulated source mechanism. It is not a new resolution of the entire Erdős similarity conjecture.

The newly located Jiang–Xi [arXiv:2610.11449v1](https://arxiv.org/abs/2610.11449v1), dated 8 October 2026, is especially relevant. Its full proof adapts G to a **given** null sequence whose adjacent ratios have positive liminf. Corollary 6.1 handles a prescribed **countable** family and tails. Its grids remain sequence-dependent and its Lemma 5.1 varies only dilation. This is stronger than the catalogue for individual nongeometric sequences, but does not supply a common set for uncountably many q. It is prior art for candidate D below, not a premise needed for (A).

The plausible missing mechanism is a **common physical-scale construction**, with varying active indices and a simultaneous two-parameter representative count. Sections 3–6 give the complete proposed proof.

### B. Hilbert-valued endpoint Fourier convergence — proved, technical

For every separable complex Hilbert space H and Bochner measurable f:T→H with ∫Φ(||f||_H)<∞, seek full-sequence norm convergence S_N f(x)→f(x) a.e., with

sup_{λ>0} λ μ{sup_N ||S_N f||_H>λ} ≤ C || ||f||_H ||_Φ,             (B)

where C is independent of H. This genuinely requires a vector-valued deduction; componentwise a.e. convergence alone is insufficient. However, the source's **actual** scalar weak-L1 norm estimate makes standard Rademacher linearization pay the whole step. Section 7 gives that reduction with constant 48√2 C_F for finite-dimensional inputs and the usual limit. It does not control (Σ_j sup_N |S_N f_j|²)^(1/2), which allows a different cutoff in each coordinate. B is deliberately **not** offered as substantial.

A stronger finite-r variation estimate at the same endpoint was eliminated early. Oberlin–Seeger–Tao–Thiele–Wright, [A variation norm Carleson theorem](https://webhomes.maths.ed.ac.uk/~wright/papers/osttw0710.pdf), Theorem 1.1 and Section 2, distinguish p>r′ from the restricted endpoint. The explicit polynomial test in §7 independently rules out LlogL→weak-L1 r-variation for every fixed finite r. No interpolation from per-p bounds or a.e. convergence is used.

### C. The supergeometric sequence 2^(−n²) — developed gap

For every η∈(0,1), seek compact E⊂[0,1], m(E)>1−η, with

∀x∈R ∀s≠0 ∃n≥1: x+s2^(−n²)∉E.                            (C)

G's routing mechanism is a plausible starting point because arbitrary branching provides many tests without raising the expected density. But the lower adjacent ratio is 2^(−2n−1)→0; Jiang–Xi's theorem does not cover C. Nor does Chlebík's relative finite-gap criterion automatically cover it. In sequence-index windows the required resolution grows quadratically in the last index, while trial count grows only linearly. In physical windows the point count is sublinear. Section 8 gives the exact gap and two distinct mechanisms attempted. No impossibility of C is claimed.

### D. Given sequences with adjacent ratios bounded below — prior-art rejection

The apparently promising statement “every positive null sequence with liminf a_{n+1}/a_n>0 is nonuniversal, even without monotonicity” is exactly Jiang–Xi Theorem 1.1. Their Lemma 2.1 first selects a subsequence with ratios in [α,1/2]; the rest replaces q powers by two-sided ratio estimates in G's proof. This is an explicit existing operation, and is excluded before deeper work. We do not rename it a new finding or weaken C back to it.

## 3. Main theorem and the normalized common-set lemma

**Theorem A.** For every η∈(0,1) there exists one compact E_η⊂[0,1] with

m(E_η) ≥ 1−7η/16 > 1−η

such that, for every q∈(0,1), every x∈R, and every nonzero real s, at least one integer n≥1 satisfies x+sqⁿ∉E_η.

The theorem is an existence result. The construction is finite at each normalized stage but has enormous parameters, and no practical efficiency assertion is made. The missing index need not have a bound uniform over all q,x,s. Applying the theorem to the scale sq^N shows that every such affine progression actually has infinitely many omitted points; this is a consequence of the same theorem, not another finding.

**Common periodic lemma.** Fix 0<q_-<q_+<1 and p∈(0,1). There exists an open 1-periodic H⊂R such that ρ(H):=m(H∩[0,1))≤6p and

∀x∈R ∀t∈[1,2] ∀q∈[q_-,q_+] ∃n≥1: x+tqⁿ∈H.              (P)

Every construction parameter in the proof of P is chosen before x,t,q. The representatives may depend on x and its exposed first-default vertex; they never depend on the unrevealed random tables.

### 3.1. Parameters and physical windows

Put L_min=log(1/q_+)>0, L_max=log(1/q_-)≥L_min, and

κ=log 2/(2L_max).

Choose an integer ℓ≥1 with 2^(−ℓ)≤(1−q_+)/4. Choose an integer M≥2 so that

β:=p(M−1)κ/2 > 4 log 2 + 1.                               (3.1)

Choose a depth d≥1 with (1−2^(1−M))^d<p. This fixes the finite complete ordered M-ary tree and its edge count K. Choose an integer g≥1 with

K 2^(ℓ−g)<p.                                               (3.2)

A final integer r0 will be taken sufficiently large, in particular r0≥2L_max/log 2. It is chosen **after** M,d,g. Let σ_0=0. Set

r_1=r0,  σ_1=M r0+(M−1)g;

r_h=max{r0,g+σ_{h−1}},
σ_h=M(r_h+g+σ_{h−1})+(M−1)g  (2≤h≤d).                      (3.3)

List edges in preorder (edge, then its child subtree, then next sibling). An edge leaving height h receives a **real logarithmic-distance interval** [a_e,b_e] of length r_h, with integer endpoints b_e=a_e+r_h. Start at a=3; consecutive windows satisfy a_next=b_previous+g. The associated physical displacement window is

Z_e=[2^(−b_e),2^(−a_e)].                                    (3.4)

These are not fixed intervals of sequence indices. For given (t,q), define the active indices

I_e(t,q)={n≥1: t qⁿ∈Z_e}.                                  (3.5)

If b_e^* is the last endpoint in the edge-plus-child block, the same preorder padding calculation as G gives

b_e^*−a_e≤2r_h.                                            (3.6)

Indeed it is r_1 for a leaf edge and r_h+g+σ_{h−1}≤2r_h otherwise. The final endpoint is B=3+σ_d. Define

J=ceil((B+1)log 2/L_min).                                  (3.7)

All active n lie in {1,…,J}: t qⁿ≥2^(−B) implies n≤(B log 2+log t)/log(1/q)≤(B+1)log 2/L_min.

For every q,t and edge of length r,

|I_e(t,q)|≥r log 2/L_max−1≥κr.                             (3.8)

To see this, the permissible real n lie in the closed interval
[(a_e log 2+log t)/L,(b_e log 2+log t)/L], L=log(1/q).
Its length is r log 2/L and its lower endpoint is positive. Any closed interval of length u contains at least u−1 integers; its integers are therefore positive. The last inequality follows from r≥r0≥2L_max/log 2. Endpoints are included throughout.

For each integer b set N_b=2^(b+ℓ), Γ_b=N_b^(−1)Z, and J_b(z)=floor(N_b{z}). These common dyadic grids do not depend on q or t. Finer keys determine all coarser keys.

### 3.2. Stability and separation, simultaneously for q,t

Call a center x stable when, for every noninitial window e with predecessor endpoint b′,

(x,x+2^(−a_e)]∩Γ_{b′}=∅.                                  (3.9)

The unstable centers for one transition lie in the periodic intervals [γ−2^(−a_e),γ), γ∈Γ_{b′}, of total density at most

N_{b′}2^(−a_e)=2^(ℓ−g).

Thus ρ(S^c)<p by (3.2). For x∈S and z∈Z_e, every earlier key satisfies J_{b_f}(x+z)=J_{b_f}(x). This follows first for b′ because no boundary is crossed, and then for all earlier grids by nesting. A center at a boundary belongs to its right-hand cell; a positive displacement landing at the next boundary is excluded by (3.9).

For fixed (t,q), the center and the active points x+tqⁿ, n∈I_e(t,q), have distinct keys at grid b_e and every finer grid. They lie in an interval of length at most 2^(−3)=1/8. Any pair of distinct active displacements differs by at least

(1−q_+)2^(−b_e),

and their distance from zero is at least 2^(−b_e). But grid width is 2^(−b_e−ℓ)≤(1−q_+)2^(−b_e)/4. Circular distance equals ordinary distance in this short interval; equal periodic keys would have smaller distance than the grid width, a contradiction. This also handles wrap-around and points exactly on grid boundaries.

## 4. Random routing and conditional probability

Use the source's finite probability construction on these common grids. Every nondefault edge e=(P,i), i<M, has an independent fair-bit table S_e on its N_{b_e} cells. Every leaf L has an independent Bernoulli-p table T_L at the grid of its incoming edge. All entries are independent. Route z to the first child with selector value one, or child M by default, repeatedly until a leaf L(z). Set

B_ω={z:T_{L(z)}(J_{b(L(z))}(z))=1}.

Each outcome is a union of finitely many half-open cells per period. Conditioning on all selectors fixes the terminal address of z, whose entry still has mean p. Hence Eρ(B_ω)=p. This density calculation is unchanged by the number of children, windows, parameters, or active indices.

For fixed x expose its addressed entry in **every** selector table. Denote the resulting field by F_x. Under the unconditioned law the center route has no default with probability (1−2^(1−M))^d<p. Condition on an atom ξ of F_x that has a first-default vertex U of height h. Set r=r_h, e_i=(U,i), i<M. Its location and all windows are now fixed independently of the remaining entries.

Let L_i(z) be the leaf reached starting at child U_i. The source's local predicate is

Q_i(z)=S_{e_i}(J_{b_ei}(z)) T_{L_i(z)}(J_{b(L_i(z))}(z)).

For a stable x, any z=tqⁿ∈Z_ei preserves all selector decisions needed to reach U and all prior rejections there. Thus

Q_i(x+tqⁿ)=1 ⇒ x+tqⁿ∈B_ω.                                (4.1)

This is the same route-preservation proof as G, now justified by the parameter-uniform physical stability in §3.2.

For **fixed** (t,q) on ξ, consider pairs (i,n) with n∈I_ei(t,q). Their current-edge selector entries are distinct and unexposed, by separation; different i use different tables. These entries A_{i,n} are independent fair bits conditional on ξ.

Next condition on all selectors. The selected terminal addresses are distinct: different children have disjoint leaf tables; different leaves have different tables; and at a common leaf below one child, nesting preserves the distinct keys already present at b_ei. Terminal entries are consequently independent Bernoulli-p variables under this conditioning, although the routes themselves need not be independent. Therefore, writing T(t,q)=Σ_{i<M}|I_ei(t,q)|,

P(all active local tests fail | ξ)
= E[(1−p)^(Σ A_{i,n}) | ξ]
= (1−p/2)^T(t,q)
≤ exp(−p T(t,q)/2)
≤ exp(−βr).                                                (4.2)

The active index set is fixed when (t,q) is fixed. We have not conditioned on success, nor chosen a parameter after seeing unused table values. The following deterministic representative lemma handles all parameters together.

## 5. The added operation: a common parameter partition with moving indices

**Representative lemma.** Fix stable x and ξ as above. There is a finite set R(x,U)⊂[1,2]×[q_-,q_+] such that, for every parameter pair, some representative has exactly the same active index sets and active finest local keys. It therefore has exactly the same active local-test values for every completion of ξ. Moreover,

|R(x,U)|≤8[5+(M−1)J(3+2^(ℓ+2r))]².                       (5.1)

**Proof.** Write v=log t∈[0,log 2], u=−log q∈[L_min,L_max]. For each i<M and 1≤n≤J, record two boundary lines

v−nu=−a_ei log 2,  v−nu=−b_ei log 2.                      (5.2)

Their signs determine whether n is active. Also, for every grid boundary γ∈Γ_{b_ei^*} with c:=γ−x∈Z_ei, record the line

v−nu=log c.                                                (5.3)

The number of such c for a fixed edge is at most

1+N_{b_ei^*}(2^(−a_ei)−2^(−b_ei))
≤1+2^(ℓ+b_ei^*−a_ei)
≤1+2^(ℓ+2r).                                              (5.4)

Thus there are at most L0=(M−1)J(3+2^(ℓ+2r)) lines before repetitions are removed. These lines depend on x, U and deterministic data alone. The logarithms have positive arguments because Z_ei consists of positive displacements.

Include the four sides of the parameter rectangle as lines. An arrangement of m distinct lines has at most m(m−1)/2 vertices, m² one-dimensional open pieces, and 1+m(m+1)/2 two-dimensional regions. Parallel lines and multiple intersections can only lower these upper bounds. The total is at most 2m²+1. Intersect the strata with the closed rectangle; because the sides are included, every nonempty intersection is already a stratum or a portion of one, and convexity prevents splitting into multiple components. Choose one representative from each nonempty stratum of dimension 0, 1, or 2. The generous bound 8(L0+5)² follows.

On each stratum the signs, including exact zeros, of all (5.2)–(5.3) are constant. Hence the active sets are constant. For active n, the point x+exp(v−nu) stays within its physical interval and cannot cross a boundary of its finest local grid without changing such a sign. Its key is constant. If it lies exactly on a boundary along a stratum, the half-open convention assigns its fixed boundary key; vertices and rectangle sides are separately represented. When an index is inactive its key is immaterial. Since the finest local key determines every table address consulted by Q_i, the required agreement holds for all table completions. Map the representatives back by t=e^v, q=e^(−u). This proves the lemma. □

**Closing the size budget without circular parameter choices.** Combining (4.2) and (5.1), the conditional probability that some (t,q) misses B_ω at every n≤J is at most

8[5+(M−1)J(3+2^(ℓ+2r))]² e^(−βr).                        (5.5)

The only appearance of the final absolute depth B is the **polynomial** factor J². It is essential to account for this factor: it cannot simply be called constant while r0 is still changing.

Here is an explicit bound. Set A_0=0 and A_h=4M(1+A_{h−1}). From (3.3),

σ_h≤A_h(r0+g).

Indeed r_h≤r0+g+σ_{h−1} for h≥2; the asserted recursion dominates all three terms in σ_h, and the height-one formula also satisfies it. Thus B≤3+A_d(r0+g). With

C_J=1+(log 2/L_min)(4+A_d),

(3.7) implies J≤C_J(r0+g+1). Also 3+2^(ℓ+2r)≤4·2^(ℓ+2r) and J≥1, so

5+(M−1)J(3+2^(ℓ+2r))≤9 M J 2^(ℓ+2r).

Consequently (5.5) is at most

C0 (r0+g+1)² exp[−γ r],

where C0=648 M² 2^(2ℓ) C_J² and γ=β−4log 2>1.             (5.6)

All quantities in C0 and γ were fixed before r0. Choose the integer r0≥2L_max/log 2 large enough that

C0(r0+g+1)² e^(−γr0)<p.                                   (5.7)

Such an integer exists since a fixed polynomial times a decaying exponential tends to zero. Because every r_h≥r0, (5.6) is <p at every possible U. Averaging over ξ adds **no factor** for the number of possible U; the atoms partition the probability space. Adding the probability <p of no default gives, for every stable center x,

P(∃(t,q)∈[1,2]×[q_-,q_+] ∀1≤n≤J: x+tqⁿ∉B_ω)≤2p.        (5.8)

This is the missing simultaneous estimate. The physical grids, changing active sets, boundary strata, and polynomial absolute-depth dependence are all required; merely squaring the old fixed-q scale count would not prove it.

## 6. Exceptional-center repair and global quantifiers

Enlarge each finite-cell outcome B_ω to open periodic B_ω^+ with ρ(B_ω^+)≤ρ(B_ω)+p. Define

R_ω={x:∃(t,q)∈[1,2]×[q_-,q_+] ∀1≤n≤J, x+tqⁿ∉B_ω^+}.

On T this is the projection of a closed subset of the compact product T×[1,2]×[q_-,q_+]. It is closed and periodic. The probability space is finite, so all ensuing integrals are of measurable functions. By (5.8) and ρ(S^c)<p,

Eρ(R_ω)≤2pρ(S)+ρ(S^c)≤3p,
Eρ(B_ω^+)≤2p.

Choose one outcome with ρ(B^+)+ρ(R)≤5p. Outer regularity on T gives open periodic V⊃R with ρ(V)≤ρ(R)+p. Set H=B^+∪V. Then H is open, 1-periodic and ρ(H)≤6p.

For x∉R every parameter pair has a hit among n≤J. For x∈R, its open neighborhood V contains x+tqⁿ for all sufficiently large n, because tqⁿ→0. In fact the convergence is uniform over the compact parameter rectangle, since tqⁿ≤2q_+ⁿ, but only the stated pointwise conclusion is needed. The repair indices may exceed J. This proves P with **all** centers and parameters, not almost every center or parameter.

To prove Theorem A, take ratio intervals Q_j=[1/j,1−1/j], j≥3; their union is (0,1). For every j≥3 and k∈Z apply P with

p_{j,k}=(η/64) 2^(−(j−2)) 4^(−|k|)

to obtain H_{j,k}. Set

C=⋃_{j≥3,k∈Z}(2^k H_{j,k} ∪ (−2^k H_{j,k})),
E_η=[0,1]\C.

This is a countable union of open sets, so E_η is compact. Each signed dilation has measure in [0,1] at most max{1,2^k}ρ(H_{j,k}). Therefore

m(C∩[0,1])≤12Σ_{j,k}p_{j,k}max{1,2^k}
=(12η/64)·1·(1/3+1+1)=7η/16.

Given q∈(0,1), x∈R and s>0, choose j with q∈Q_j and k with s=2^k t, 1≤t<2. The hit for H_{j,k} at center 2^(−k)x gives x+sqⁿ∈C. For s<0 apply the positive-scale argument to −x,−s and reflect, using C=−C. Thus every signed affine copy is missed by E_η. All choices of H precede q,x,s. This proves the complete proposed theorem. □

## 7. Fourier screen: a technical positive deduction and an exact obstruction

For completeness, the Hilbert-valued target B does follow from F without a new analytic operation. First suppose f=(f_1,…,f_m), F0=(Σ|f_j|²)^(1/2), and take a>||F0||_Φ so ∫Φ(F0/a)≤1. Let g_ε=Σ ε_j f_j for independent fair signs. At each point put t=F0/a and Z=|g_ε|/F0 (zero when F0=0). Then EZ≤1 and EZ²=1. Since 2+tZ≤(2+t)(1+Z),

EΦ(|g_ε|/a)≤t log(2+t) EZ+t E[Z log(1+Z)]
≤Φ(t)+t≤3Φ(t).

For any scalar g, convexity gives ||g||_Φ≤a max{1,∫Φ(|g|/a)}. Hence E||g_ε||_Φ≤4a. This argument uses a Luxemburg norm throughout and asserts no scalar modular weak endpoint.

Fix a finite maximum over N≤K, and on the measurable set A where max_N||S_N f||_2>λ select the first such N(x). For z_j=S_{N(x)}f_j(x), the sign sum has second moment Σ|z_j|² and fourth moment at most 3(Σ|z_j|²)². Paley–Zygmund gives

P_ε(|Σ ε_j z_j|>λ/√2)≥1/12  (x∈A).

Integrating and using F,

μ(A)≤12 E_ε μ{S*g_ε>λ/√2}
≤(12√2 C_F/λ) E||g_ε||_Φ
≤48√2 C_F a/λ.

Let a decrease to ||F0||_Φ and K increase. For separable H, apply finite-dimensional orthogonal projections and pass monotonically in the output norms, with input norm bounded by that of ||f||_H. Bochner integrability follows from Φ(u)≥u log 2, so Fourier coefficients and projections commute. This proves B's maximal bound. Finite-rank trigonometric polynomials are dense in the Bochner Orlicz norm: Φ satisfies Δ2, truncate f, approximate its bounded range by simple finite-rank functions, then approximate scalar components by trigonometric polynomials. The usual oscillation estimate against these polynomials, the maximal inequality, and convergence in measure of the approximants give S_N f→f a.e. in H. This is a classical randomization/density transfer, hence technical regardless of whether the exact endpoint wording is elsewhere stated.

**No finite variation upgrade.** For fixed 1≤r<∞ put f_N(x)=Σ_{k=1}^N e^{ikx}. Its symmetric partial sums have N successive increments each of modulus one, so V^r(S_n f_N)(x)≥N^(1/r) at every x. On [−π,π], the geometric-series identity gives |f_N(x)|≤min{N,π/|x|}. Thus ||f_N||_1≤C log(2+N), and

∫Φ(|f_N|)≤log(2+N)||f_N||_1≤C log²(2+N).

By the preceding Luxemburg bound, ||f_N||_Φ≤C′log²(2+N). A hypothetical V^r:LlogL→L^(1,∞) norm bound would imply N^(1/r)≤C_r log²(2+N), which is false for large N. This is an analytic counterexample to that **estimate**, not a disproof of F's a.e. convergence statement. It also shows why the variation conclusion cannot be read out of the scalar source or inferred by interpolation near p=1.

## 8. Supergeometric attempt and alternative mechanism

For C, two approaches were developed far enough to locate their exact unpaid costs.

**Index-window route.** On a length-r interval of n for a_n=2^(−n²), a grid distinguishing the last point has resolution comparable to 2^(b²), not 2^b. If a descendant reaches b^*≈a+2r, a local dilation path starting near index a meets a number of boundaries on the order of 2^((b^*)²−a²). The exponent includes 4r²+4ar, whereas the fixed-parameter independent-test exponent is only p(M−1)r/2. For fixed M,p the analogue of the source's “large r0” step cannot close with this count. Taking much larger branching M after r is not a completed fix: d and the later indices then change, so the bound is not uniform in the newly enlarged tree. These are failures of this budget, not lower bounds on every possible construction.

**Physical-window route.** At t=1 the active indices in [2^(−b),2^(−a)] satisfy a≤n²≤b. In a window of length r=b−a their number is at most √b−√a+2≤√r+2. When a≫r, it can be much smaller or zero. There is no analogue of (3.8) with a positive universal κ. The new two-parameter arrangement construction therefore cannot be transplanted to C merely by changing n to n²: the crucial linear supply of tests is gone.

**Alternative considered.** One could assign nonuniform physical windows that contain a prescribed number of square indices and allow branching to grow with physical depth. That restores trials but enlarges the edge-plus-descendant resolution and the number of parameter representatives at the same time. A sufficient missing lemma is a finite routing scheme, for every p>0, with stable-center loss <p, no-default probability <p, and conditional all-dilation failure <p for the square-index sequence while retaining mean terminal density p. More explicitly it must make

(number of representatives for an edge and its descendants)
× exp[−p·(available independent trials)/2]<p

at every possible first-default vertex, with parameters chosen before the center and dilation. Neither the inherited padded tree nor the physical-window version above proves that inequality for 2^(−n²). No positive result for C, no general no-go theorem, and no statement about all superlacunary sequences is claimed.

As an exact small diagnosis of the first naive ratio-uniform route for A, reuse the q=1/2 reference grid N_b=2^(b+4) at b=12. At q=1/4, both q^b and q^(b−1) have key zero, the same as the center. Thus the fixed-q separation lemma cannot simply be declared uniform on [1/4,1/2]. The successful proof changes the **windows and active indices**, as well as the representative count. Conversely, simply intersecting avoiding sets for a dense sequence of ratios leaves the quantifier gap described in §2. These alternatives were rejected before the physical-window argument was completed.

## 9. Adversarial audit, dependency graph, and significance limits

The dependency chain for the proposed result is:

G/D routing architecture → common physical windows (§3) → parameter-uniform stability and distinct addresses (§§3–4) → moving-index line-arrangement representatives (§5) → fixed-parameter failure plus explicit noncircular budget (5.6–5.7) → compact exceptional-center repair (§6) → countable ratio slabs and signed scales → Theorem A.

The source already contains the architecture, mean-density identity, first-default probability, conditional terminal proof, local-subtree principle, and open-neighborhood repair. Arrangement counts, elementary compactness, and summable unions are classical. The proposed added content is their common-grid/moving-index implementation with an all-ratio estimate. No particular inherited lemma is renamed a discovery.

**Why an uncountable extension cannot be obtained from uniform ratio constants alone.** For every measurable E of positive measure, there exist x and a positive null sequence z_n with z_{n+1}/z_n∈[1/3,2/3] such that x+z_n∈E for all n. Indeed, choose a Lebesgue density point x. For every sufficiently large integer k, the interval [x+(9/10)2^(−k),x+(11/10)2^(−k)] has positive intersection with E: otherwise its missing length (1/5)2^(−k) would contradict density one at x. Choose one point there and subtract x; start the sequence at a sufficiently large k. Consecutive ratios lie in [9/22,11/18]⊂[1/3,2/3]. Thus no single positive-measure set can avoid **all** sequences with those two-sided bounds. This is not a counterexample to Theorem A, because the chosen ratios need not be constant. It demonstrates that the finite-dimensional parameter partition, not only uniform separation and density constants, is indispensable. In particular, Jiang–Xi's per-sequence statement cannot simply have its set/sequence quantifiers exchanged.

The following attacks were checked explicitly.

- **Boundary strata:** both active-window equalities and every relevant finest-grid equality enter the arrangement. Zero-dimensional and one-dimensional strata are retained. Ignoring them would leave exact rational/logarithmic configurations uncontrolled.
- **Absolute index depth:** J depends on r0 and the entire tree. It is bounded by C_J(r0+g+1) and paid in (5.7); it is never silently fixed while r0 grows.
- **Quantifier and conditioning order:** the random set and grids are common to all q. Only a deterministic finite set of parameter representatives, fixed on the center-exposure atom, is used before unexposed entries are evaluated.
- **Terminal collisions:** selectors may share information through routes. The proof conditions on all selectors and proves terminal addresses distinct, rather than assuming routes independent.
- **Far finer unrelated subtrees:** representatives only use Q_i and its own child subtree. Failed local predicates may route elsewhere in the actual global construction; those irrelevant finer keys are not counted. Success implication (4.1), not equivalence, is sufficient.
- **Unstable centers and topology:** stability is physical and uniform. Repair projects a closed set from a compact parameter product after open enlargement. It supplies every remaining center by tail points, never just a.e. centers.
- **q near zero or one:** no uniform finite constants across (0,1) are claimed. Compact slabs are combined only after each is proved with constants depending on its endpoints.
- **Scale and sign:** both expanding and contracting dyadic dilations are paid by max{1,2^k}; no false invariance of qⁿ under dyadic index shift is used. Negative s uses reflection.
- **Finite patterns:** every finite prefix remains measure universal. The theorem only excludes the entire infinite pattern; repair may use arbitrarily late indices.
- **Other transformation classes:** no avoidance under arbitrary bi-Lipschitz maps, no Kakeya statement, and no consequence for variable-coefficient tubes follows.

Primary comparison is bounded, not a proof of worldwide priority. G/D and Jiang–Xi use fixed sequence-index windows. Burgin et al. Proposition 3.3 integrates over parameter triples, leaving possible exceptional q or centers, while the theorem here repairs a supremum over a compact ratio–dilation rectangle at each center. Kolountzakis's [1997 primary paper](https://eigen-space.org/mk/ps/universal.pdf), Theorems 1–3 and Sections 2–3, supplies the random-cell and almost-everywhere-parameter background; its large-finite-gap condition is different. Chlebík [1512.05607v1](https://arxiv.org/abs/1512.05607v1), Theorem 15, uses the relative minimum-gap condition; the source's branching already goes beyond that one-level calculation for geometric sequences. The almost-everywhere, fixed-center, fixed-pattern, and full-Hausdorff-dimension conclusions cannot be substituted for A.

The full Jiang–Xi proof was read specifically to test whether the new operation was already present. It is a necessary prior-art comparison, not independent verification of this candidate. It gives a concrete reason to reject the variable-ratio **single-sequence** extension as an already paid operation. Whether the simultaneous physical-window implementation clears this project's substantial-mechanism threshold remains a question for the parent's separate significance review. A proof PASS alone must not settle it, as I14/I15/I17/I30 demonstrate.

## 10. Evidence and reproducibility

The source directory contains the original operative brief, frozen relevant rejection/acceptance history, complete manuscript inventory, full-corpus search hits, source contracts/read passages, pinned source copies and manifest, primary retrieval bytes, current abstract/version pages, query/response payloads, and retrieval failures. Only necessary prior inputs are bound; shared ledger drift is reported separately. The downloaded survey is orientation only: no current-status inference relies on its older v1, and its later correction is noted. Kolountzakis's author-hosted PDF has a broken text encoding; pages 3–11 were rendered and read visually, and those PNGs are retained. The renderer emitted Type-3 glyph bounding-box warnings, but the inspected pages are legible. The retrieved 2020 full-similarity claim is excluded as withdrawn. Two-fold sumset and Rajchman manuscripts were retrieved for the surrounding literature screen, but no theorem here relies on them. Their roles as larger-pattern and atomless-measure criteria are already distinguished by the fully read pinned introductions; they are not asserted to have received a fresh full-proof audit here.

A guessed historical arXiv identifier retrieved an unrelated Temme paper; it is explicitly rejected in `literature/retrieval-assessment.json` and replaced by Kolountzakis's author-hosted primary PDF. The attempted nonexistent v2 HTML of 2210.09284 returned an internal error; the current abstract lists v1, and that PDF is retained. A missing optional HTML parser caused the first extraction script to fail; the standard-library retry succeeded. Failures are not concealed or treated as evidence.

Run from the repository root:

```sh
python frontier/experiments/i36_harmonic_analysis_discovery/verify.py
```

The verifier checks the report/evidence seal, pinned Git/SHA identities against the complete tree, immutable input dependencies, retained primary bytes, and byte-for-byte reproduction of the exact diagnostic output. It reports mutable shared-ledger drift separately. `checks.py` tests padding and its linear depth budget, rational active-index counts and grid separation, stable boundary conventions, adaptive terminal-address distinctness, exact conditional Bernoulli sums, the line-arrangement combinatorics, and the signed-scale budget. The supergeometric tests and reference-grid collision have analytic explanations above. No floating-point success is used as proof.

The completed offline run is **PASS**: 124 sealed files, 39 pinned files, 21 source contracts, 32 logged passages/visual pages, and 19 retained primary responses. Exact diagnostics cover 6,624 tree edges, 540 active windows, 129,189 separation pairs, 576 stable-key cases, 4,096 adaptive routing outcomes, and 36 probability identities. Both shared ledgers have drifted from the frozen starting versions; their baseline/current hashes are reported separately in `verification.json`, and no immutable dependency has drifted. Run `verify.py` to review the seal; `seal.py` is the author-side regeneration utility and should not be run to validate an existing seal.

The diagnostics are a separate adversarial pass by the same researcher, **not independent proof review**. The universal theorem rests on §§3–6 and the stipulated source operations. The parent owns independent proof review, a separate significance review, integration, each finding's commit, and publication. This report changes none of those gates or the accepted count.
