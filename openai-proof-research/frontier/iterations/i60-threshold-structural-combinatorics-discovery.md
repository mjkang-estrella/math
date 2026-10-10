# I60 — Thresholds and structural combinatorics: slice transfer, compatibility, and two-union limits

Date: 2026-10-09. Premise: all theorem statements **and lower proof operations** in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. External new results are not additional axioms.

**Disposition: a complete technical slice-transfer theorem, two refuted strengthenings, a technical robust-Hall partial, and an unresolved same-density two-union target. No substantial finding is nominated.** The positive slice theorem has an explicit reduction to the source influence theorem, classical slice Poincaré, and elementary conditional averaging/coarea. Its endpoint logarithmic exponent does not make that reduction a nonroutine discovery. There is no count, priority, integration, or publication decision in this report.

The exact [assignment](../sources/i60_threshold_structural_combinatorics_discovery/full-brief.txt), [frozen inputs](../sources/i60_threshold_structural_combinatorics_discovery/inputs.json), [pinned sources](../sources/i60_threshold_structural_combinatorics_discovery/pinned-manifest.json), [passages](../sources/i60_threshold_structural_combinatorics_discovery/read-passages.json), [objections and responses](../sources/i60_threshold_structural_combinatorics_discovery/objections.json), and [primary retrievals](../sources/i60_threshold_structural_combinatorics_discovery/literature/responses.json) accompany the report. Only the assigned I60 report and two directories were written; no agents, shared edits, staging, commits, or publishing were used.

## 1. Scope and prior audit

I read AGENTS.md, the current ledger, I13/I19/I22/I25, and the I56/I58 contribution decisions. In particular, I do not reuse common-base projection, weighted switch mixing, signed Saxl, matching entropy, prophet implementation, correspondence coloring, approximate PSD rank, or the closed standard-map route. I59 is independent and untouched.

The complete preprint tree has 13,223 entries and 749 manuscript directories. All **9,340** cached corpus files were independently hashed against their Git blob identities from that complete tree; the truncated root tree and old 719 headline were not used as authority. Thirty-four selected files from five source families were copied, not recursive earlier evidence archives. Full reads cover both influence proofs, the entire graph-decomposition proof, the entire discrete-convexity proof, and the selector/rounding proof of the integral–fractional companion. Exact ranges and hashes are retained separately. Search coverage is not full-corpus reading.

The strongest available operations matter:

* The graph and hypergraph papers prove the **nonmonotone**, all-bias pivotal-influence inequalities. Their conditional Fourier identity averages squared restricted coefficients over *all* exterior degrees. The small block keeps every incident edge. Their capture and high-degree arguments, not merely threshold-width statements, are available.
* The graph-decomposition paper's `prop:transfer` already embeds the cut piece while fixing its entire small part Y. Its source tests control smoothed unions of neighborhood requirements; its target tests hold simultaneously for every small Y and compressed family. A prescribed-root version within that range is already in the proof.
* The discrete-convexity introduction's `cor:two-union` already gives two unions with constant density loss. Its 32-row signed identity and pair-sampling cover, followed by dependent-row density restoration, prove same-density smallness with 2^75 unions. The integral–fractional companion repeats the two-union constant-loss consequence explicitly.

## 2. Four precise screens and current antecedents

### S: fixed-cardinality isoperimetry — developed through two constructions

Let N=binom(n,2), Ω_m={A⊆E(K_n):|A|=m}, and ν_m be uniform. For Boolean vertex-invariant f define

\[
 \mathcal I_m(f)=\frac1N\sum_{e<e'}\Pr_{\nu_m}\{f(A^{ee'})\ne f(A)\},
 \qquad
 \delta_m(f)=\Pr\{f(A-a+b)\ne f(A)\},
\]

where A is uniform, a is uniform in A, b uniform in E\A, and A^{ee'} swaps the two membership bits. For 0<m<N,

\[
 \mathcal I_m=\frac{m(N-m)}N\delta_m,
 \qquad \widetilde{\mathcal I}_m:=N\delta_m
       =\frac{\mathcal I_m}{p(1-p)},\quad p=m/N.                 \tag{2.1}
\]

The initial strong target was Var_{ν_m} f≤C(log n)^−2 \mathcal I_m, uniformly over **all** m. Section 5 refutes it by the two-edge wedge property. The corrected dense target requires ηN≤m≤(1−η)N, with C_η. Section 3 proves it, and more generally proves the all-slice version using \widetilde{\mathcal I}_m. No noise-sensitivity or real-valued spectral-gap conclusion is inferred.

Early primary comparison identified Filmus's [*Orthogonal basis for functions over a slice of the Boolean hypercube*, current v2, 14 March 2022](https://arxiv.org/abs/1406.0142v2), especially Theorem 4.2 and Lemmas 5.5–5.6, and Filmus–Mossel's [*Harmonicity and invariance on slices of the Boolean cube*, current v5](https://arxiv.org/abs/1507.02713v5), Lemma 4.4 and Theorem 4.6. These supply classical transposition Poincaré and slice/cube comparison machinery. Their harmonic lift is not a Boolean extension with automatically bounded pivotal influence. The complete construction below avoids asserting that it is. The positive result is technically closed, not nominated on the basis of a missing printed statement.

### G: compatible copies of the decomposition pieces — refuted

Target: absolute k,L such that every H on at most n vertices has fixed edge pieces whose embeddings into **one** G(n,min{Lq(H;n),1}) agree wherever source vertices coincide and together give an injective map on V(H), with probability at least 1/2. This is equivalent to full containment of H at constant times its integral expectation threshold. It is false, already for a spanning perfect matching; Section 6 pays the integral-q upper bound and isolated-vertex obstruction directly.

The current primary is Ascoli–He–Park–Talagrand [arXiv:2608.11183v1](https://arxiv.org/abs/2608.11183v1), Theorem 1.8, its `perm` argument in Lemmas 2.1–2.3, Theorems 1.12–1.13, and Section 8. Its compatible relabelings lie in deterministic likely families; they are not simultaneous copies in one random host. That distinction is essential. Their Question 8.2 asks about two-thresholds, not this false stronger containment assertion.

A search also surfaced Yang, [arXiv:2609.20864v2](https://arxiv.org/abs/2609.20864v2). The **current official version is withdrawn**, 21 September 2026; its page reports concerns about the analysis and interpretation. The attempted current PDF returns 404. Neither its search abstract nor a secondary review is used as a theorem. The withdrawal and failed response are retained.

### R: local resilience of rooted neighborhood transfer — refuted in the proposed norm

Target: an absolute ε>0 such that, in the full parameter range of the source's `prop:transfer`, the prescribed-Y embedding survives **every** target edge deletion F with Δ(F)≤εnr_*, where r_*=1−(1−r)^32. This is stronger than plain containment and concerns genuinely adversarial per-vertex deletions, not additional independent thinning.

It is false for a single rooted two-edge wedge when r=n^−1/200, s=2. Destroying one common neighborhood uses only O(nr_*²) deletions at a root and one at each other affected vertex, asymptotically below εnr_*. Section 7 proves the assertion and retains the strongest direct source deduction: simultaneous resistance to deletion of at most floor(nr^s/20) **candidate vertices**. That surviving claim is only the source's unused Hall slack, not a resilience discovery. AHPT's center tests and the pinned compression/Hall proof were read before drawing this distinction.

### D: two unions with no density loss — unresolved

Exact target: there exists absolute ε∈(0,1/2) such that, for all finite nonempty X, all 0<p<1, and all D⊆2^X with μ_p(D)≥1−ε, the exceptional family E_2(D) has an **integral** containment cover of cost at most 1/2 at the **same** p. Repeated members are allowed in the two unions. No monotonicity of D is imposed.

The source already has this conclusion with 2^75 unions, and already has two unions at p/(50·512^4). Section 8 constructs the full two-row Fourier fractional certificate and explains why the available rounding operations do not close the same-density integral gap. This is an actual certificate construction, not an assumed rounding criterion offered as a solution.

Current Li [*On p-Spread Measures*, v2, revised 6 October 2026](https://arxiv.org/abs/2609.08967v2), **Theorem 1.15 and its proof**, already gives the precise fractional threshold recovered below. The v1 theorem numbering used in some source references is no longer current. Li's Theorem 1.19 also provides a coupling with two Bernoulli marginals; their dependence is permitted and does not give an integral cover at p. Park [arXiv:2609.14681v1](https://arxiv.org/abs/2609.14681v1), Theorem 3.4/Corollary 3.5, has the earlier fractional/rounding comparison. These are attribution and scope comparisons; the two-row certificate is proved below without taking a new external theorem on trust.

## 3. Construction A: conditional completion gives a complete technical transfer theorem

The construction applies to any permutation group Γ on a coordinate set of size N, including the vertex-induced graph/hypergraph group. Its independence from the special source proof is part of the technical-only assessment.

**Transfer theorem T.** Suppose N≥2, 1≤m≤N−1, p=m/N, and every Γ-invariant Boolean h on {0,1}^N obeys

\[
 \operatorname{Var}_{\mu_p}h\le a\sum_e I_{e,p}(h).
                                                               \tag{3.1}
\]

Then every Γ-invariant Boolean f on Ω_m obeys

\[
 \operatorname{Var}_{\nu_m}f
 \le \left(aN+\frac12\mathbb E|K-m|\right)\delta_m(f)
 \le \left(a+\frac{\sqrt{Np(1-p)}}{2N}\right)
                 \widetilde{\mathcal I}_m(f),\quad K\sim\mathrm{Bin}(N,p).
                                                               \tag{T}
\]

No transitivity, monotonicity, lower bound on p, or algorithmic access assumption is needed. The endpoint slices m=0,N are singleton spaces and have zero variance separately.

### 3.1 The extension and its exact means

For A⊆[N], |A|=k, define

\[
 g(A)=
 \begin{cases}
  \mathbb E[f(B):B\in\Omega_m,\ B\supseteq A],&k\le m,\\
  \mathbb E[f(B):B\in\Omega_m,\ B\subseteq A],&k\ge m,
 \end{cases}                                                    \tag{3.2}
\]

with uniform averaging in each line. At k=m these agree with f(A). Thus 0≤g≤1 and g is Γ-invariant. A uniform k-set followed by the indicated completion/deletion produces a uniform m-set. Consequently E_{ν_k}g=μ:=E_{ν_m}f for every k, including k=0,N. In particular,

\[
 \operatorname{Var}_{\mu_p}g
   =\mathbb E_K\operatorname{Var}_{\nu_K}g.                       \tag{3.3}
\]

This constant layer mean is why random cardinality does not introduce a spurious edge-count component.

### 3.2 Variance retained on each layer

The classical uniform-slice Poincaré inequality on an M-coordinate slice is

\[
 \operatorname{Var}u\le\frac1{2M}\sum_{i<j}\mathbb E(u-u^{ij})^2. \tag{P}
\]

For singleton slices it is trivial. For other slices, Filmus v2, Lemmas 5.5–5.6, prove it by orthogonal decomposition: the unnormalized transposition Laplacian has degree-d eigenvalue d(M+1−d)≥M for every nonconstant component, 1≤d≤min(ℓ,M−ℓ). Its Dirichlet form is one half of the sum in (P), giving exactly the stated normalization. This is a classical input; its proof and factor conventions were inspected.

For k<m, couple A uniform in Ω_k with B uniform among its m-supersets. Conditional on A, use (P) on the M=N−k free coordinates. The variance decomposition gives

\[
 \operatorname{Var}_{\nu_m}f-\operatorname{Var}_{\nu_k}g
 =\mathbb E_A\operatorname{Var}(f(B)\mid A).
\]

To average the conditional Dirichlet form, reverse the sampling: B is uniform, and A is a uniform k-subset of B. A nontrivial swap of B removes one element of B and adds one outside B. It is available on the free coordinates precisely when its removed element is not in A, an event of probability (m−k)/m. Each unordered coordinate pair is counted once. Thus

\[
 0\le\operatorname{Var}f-\operatorname{Var}_{\nu_k}g
 \le\frac{N(m-k)}{2m(N-k)}\mathcal I_m
 =\frac{(m-k)(N-m)}{2(N-k)}\delta_m
 \le\frac{m-k}{2}\delta_m.                                     \tag{3.4}
\]

For k>m, use (P) on the k coordinates of a uniform k-superset A of B. A swap is available precisely when its added element is in A; conditional on B this has probability (k−m)/(N−m). Therefore

\[
 0\le\operatorname{Var}f-\operatorname{Var}_{\nu_k}g
 \le\frac{N(k-m)}{2k(N-m)}\mathcal I_m
 =\frac{(k-m)m}{2k}\delta_m
 \le\frac{k-m}{2}\delta_m.                                     \tag{3.5}
\]

Equality of the variances holds at k=m. All denominators used in (3.4)–(3.5) are positive in their respective cases. Averaging over K in (3.3) gives

\[
 \operatorname{Var}_{\nu_m}f
 \le\operatorname{Var}_{\mu_p}g+\tfrac12\mathbb E|K-m|\delta_m.  \tag{3.6}
\]

### 3.3 Adjacent-layer L1 gradients

Choose A uniformly in Ω_k and e uniformly outside A. If k<m, put t=(m−k)/(N−k). A uniform m-superset of A contains e with probability t. Conditional on containing e its mean f is g(A+e); conditional on avoiding e write the mean as h. Hence

\[
 g(A)=t g(A+e)+(1-t)h.
\]

Couple the two conditional completions by choosing B uniformly among the m-supersets of A avoiding e, choosing b uniformly from B\A, and replacing b by e. The replacement is uniform among the m-supersets containing A+e: every possible result has exactly N−m equally weighted preimages. Averaging over A,e makes (B,b,e) a uniform directed swap from Ω_m. Jensen's inequality therefore gives

\[
 \mathbb E_{A,e}|g(A+e)-g(A)|
 \le\frac{N-m}{N-k}\delta_m\le\delta_m.                         \tag{3.7}
\]

If k≥m, a uniform m-subset of A+e contains e with probability t=m/(k+1). Couple a uniform m-subset B of A to one containing e by replacing a uniform b∈B. The same uniform directed-swap marginal yields

\[
 \mathbb E_{A,e}|g(A+e)-g(A)|
 \le\frac{m}{k+1}\delta_m\le\delta_m.                           \tag{3.8}
\]

There is no assertion of pointwise bounds by δ_m: these are **averaged** inequalities. In the sum of cube coordinate gradients, first choose e uniformly, then sample the other N−1 bits at bias p. Conditional on their count k, the pair (A,e) has exactly the preceding uniform law. Thus

\[
 \sum_e\mathbb E_{\mu_p}|\Delta_e g|\le N\delta_m.               \tag{3.9}
\]

### 3.4 Coarea, rather than a false real-valued spectral gap

For 0<t<1, h_t=1_{g>t} is Γ-invariant and Boolean, so (3.1) applies. For independent X,X' with law μ_p,

\[
 \operatorname{Var}g=\tfrac12\mathbb E(g(X)-g(X'))^2
 \le\tfrac12\mathbb E|g(X)-g(X')|
 =\int_0^1\operatorname{Var}h_t\,dt.
\]

Also ∫_0^1 I_{e,p}(h_t)dt=E|Δ_e g|, since the thresholds at which two numbers disagree form the interval between them. The spaces are finite, so interchanging integrals and sums requires no limiting argument. Therefore

\[
 \operatorname{Var}_{\mu_p}g
 \le a\sum_e\mathbb E|\Delta_e g|\le aN\delta_m.
\]

Combine with (3.6) and use E|K−m|≤sqrt(Np(1−p)) to prove T. This uses L1 gradients of a bounded function; it does **not** promote the Boolean source inequality to an L2 spectral gap. ∎

### 3.5 Graph and hypergraph consequences, with boundaries

For graphs, take a=2^17/(log n)^2. For n≥3, N≥n²/3 and (log n)^2≤n, while sqrt(p(1−p))≤1/2. Thus

\[
 \boxed{\operatorname{Var}_{\nu_m}f
 \le\frac{2^{17}+1}{(\log n)^2}\widetilde{\mathcal I}_m(f)}.     \tag{S}
\]

For fixed η∈(0,1/2], every ηN≤m≤(1−η)N consequently satisfies

\[
 \boxed{\operatorname{Var}_{\nu_m}f
 \le\frac{2^{17}+1}{\eta(1-\eta)(\log n)^2}\mathcal I_m(f)}.    \tag{Sη}
\]

For n=2 every slice is a singleton. Empty/full slices at all n also have zero variance. Constants in Sη are uniform in n,m,f for the stated fixed η, with no hidden asymptotic cutoff.

For every fixed r≥3, put N=binom(n,r), α=r/(r−1). Applying T to the source gives

\[
 \operatorname{Var}_{\nu_m}f
 \le\left(\frac{C_r}{(\log n)^\alpha}+\frac1{4\sqrt{\binom nr}}\right)
         \widetilde{\mathcal I}_m(f).                           \tag{SH}
\]

This displayed bound is valid literally for n≥r, whenever an interior slice exists. At n=r none does. A constant C'_r absorbs the second term into (log n)^−α: for n≥2r use binom(n,r)≥(n/r)^r, and the supremum of (log n)^α n^−r/2 is finite; the finitely many r<n<2r values have positive binomial coefficients. No r-uniform assertion is made.

**Contribution assessment.** T consists of classical conditional averaging, the exact Johnson-slice Poincaré constant, a one-swap coupling, and the elementary level-set integral. It reproduces the full corrected target from the strongest pinned nonmonotone source theorem, without a new restriction engine. S/Sη/SH and their variants are one technical partial. The proof is complete at author level, but it has no independent analytic review acceptance.

## 4. Construction B: random priorities, its exact identities, and the failed direct transfer

This was a different actual extension, not a relabeling of (3.2). Give the N coordinates independent U_e uniform on [0,1], and let A(U) be the m coordinates of smallest priority. Almost surely there are no ties. Put F(U)=f(A(U)). It is Boolean, Γ-invariant, and has exactly the ν_m law of f.

Fix all priorities except U_e. Let B be the m smallest other coordinates, b its largest-priority member, and T the m-th order statistic of the N−1 other priorities. There are exactly two possible outputs:

\[
 F(U)=f(B-b+e)\quad(U_e<T),\qquad F(U)=f(B)\quad(U_e>T).
\]

Define D_e=Pr[f(B-b+e)≠f(B)], over the other priorities. Their order is uniform and independent of their ordered numerical values. For a uniformly chosen e, B is a uniform m-set avoiding e and b uniform in B. Therefore

\[
 \sum_eD_e=N\delta_m.                                         \tag{4.1}
\]

Independent resampling of U_e changes the output with probability 2T(1−T) on a disagreeing fiber. Since T~Beta(m,N−m),

\[
 \Pr[F(U)\ne F(U^{\mathrm{resample}\ e})]
 =\frac{2m(N-m)}{N(N+1)}D_e,
 \quad
 \sum_e\Pr[\text{change}]=\frac{2N}{N+1}\mathcal I_m.           \tag{4.2}
\]

For completeness, E T(1−T)=m(N−m)/(N(N+1)) follows by integrating the order-statistic density `(N−1)!/((m−1)!(N−m−1)!) t^(m−1)(1−t)^(N−m−1)`. The factorization with D_e uses the independence of labels/order and ordered values; it is not an arbitrary independence assertion.

One might now hope to apply the source directly on continuous product coordinates. That step is unavailable: its Boolean biased-bit derivative and hypercontractive estimates do not assert an alphabet-independent resampling inequality on [0,1]. A step fiber at a very small threshold is an explicit obstruction to a uniform 2→4 estimate for ordinary coordinate resampling noise: an indicator of a set of measure t has norm ratio t^−1/4 before smoothing, and the nonconstant part still has an order-one multiple of that spike after any fixed positive noise retention.

A concrete binary repair is to write U_e=Σ_{j≥1}2^−j ξ_{e,j}. For a step at any fixed threshold T, flipping bit j changes the step on an interval of total measure at most 2^{1−j}. Thus

\[
 I_{e,j}(F)\le2^{1-j}D_e,
 \quad\sum_{e,j}I_{e,j}(F)\le2N\delta_m,
 \quad\sum_e\sum_{j>b}I_{e,j}(F)\le2^{1-b}N\delta_m.            \tag{4.3}
\]

Finite-bit conditional expectations converge in L2 to F; conditional variance/Efron–Stein also controls the discarded Fourier mass by one quarter of the last sum. This is a genuine small-tail interface, not a proof of the desired capture estimate.

The source's combinatorial capture now fails if used unchanged: Walsh support indexes **colored edge bits**, and one edge can occur at many bit levels. Take k=4 and the five bits of one fixed graph edge. The support size 5 is at most k²/2=8, but any vertex block that touches it retains all five bits, and any block that misses it retains zero. The event `1≤retained degree≤4` has probability **zero**. The source's simple-graph support lemma cannot be cited for this support. More generally use k+1 bits of one edge for any k≥3.

Bounding multiplicities by a cutoff b only gives the generic multigraph bound `minimum positive vertex degree ≤sqrt(2bs)`, with an extra b in the original Fourier cutoff. To make the discarded mass in (4.3) as small as O((log n)^−2 Nδ_m), this crude route chooses b of order log log n. It therefore does not give the endpoint by the unchanged capture proof. This diagnoses that particular truncation/capture strategy, not an impossibility of a better argument. A weighted spectral capture estimate that uses the geometric bit tails could repair this route, but is not proved here and is unnecessary for T.

Adversarial examples test both extensions. For the noninvariant diagnostic f(A)=1_{1∈A}, (3.2) is fractional on the empty/full layers (mean m/N), while F remains Boolean; they are not the same extension. For invariant f, all edge-count functions are constant on each fixed slice, so a balanced edge-count example on the product cube supplies neither a counterexample to Sη nor a noise-sensitivity conclusion. The actual sparse wedge counterexample follows next.

## 5. Exact sparse obstruction to an all-density unnormalized swap bound

For n≥4 and m=2, let f=1 when the two graph edges share a vertex. This is vertex-invariant. With N=binom(n,2),

\[
 a:=\Pr(f=1)=\frac{2(n-2)}{N-1}=\frac4{n+1}.
\]

From a wedge, after choosing an edge to remove, exactly binom(n−2,2) of the N−2 available replacement edges are disjoint from the retained edge. Uniform swap reversibility makes the two directional boundary flows equal, so

\[
 \delta_m=2a\frac{\binom{n-2}{2}}{N-2},\qquad
 \mathcal I_m=\frac{4a}{N}\binom{n-2}{2}.
\]

Consequently

\[
 \frac{\operatorname{Var}f}{\mathcal I_m}
 =\frac{n(n-1)}{4(n+1)(n-2)}\longrightarrow\frac14.             \tag{W}
\]

No absolute C can make Var f≤C(log n)^−2 \mathcal I_m for every m,n. This is an actual graph-property counterexample, not a noninvariant dictator. It does not refute the pivotal normalization S, nor the fixed-η target Sη. It does not show the factor 1/[p(1−p)] in the general transfer theorem is optimal.

## 6. Full compatibility fails already for spanning perfect matchings

Let n=2h and H be a perfect matching on all n vertices. For a uniform perfect matching M of K_n and any s-edge matching S,

\[
 \Pr(S\subseteq M)=\frac1{(n-1)(n-3)\cdots(n-2s+1)}.
\]

For a nonmatching S the probability is zero. The factors in the denominator decrease with s; the geometric mean of a prefix is at least the geometric mean of the full list. The full product is at least h!≥(h/e)^h, the latter following from the integral lower bound for log(h!). Hence

\[
 \Pr(S\subseteq M)\le(2e/n)^{|S|}                             \tag{6.1}
\]

for all S, including the empty set. If n>2e, any containment cover C of all perfect matchings obeys

\[
 1\le\sum_{S\in C}\Pr(S\subseteq M)
   \le\sum_{S\in C}(2e/n)^{|S|}.
\]

Thus no budget-1/2 cover exists at 2e/n, and q(H;n)<2e/n. Only this large-n bound is needed to refute uniform constants; the finitely many smaller n do not affect the counterexample sequence.

For p=A/n with any fixed A>0 and n>A, let Z count isolated vertices in G(n,p). Then

\[
 \mathbb EZ=n(1-p)^{n-1},\quad
 \mathbb EZ^2=\mathbb EZ+n(n-1)(1-p)^{2n-3},
\]

and

\[
 \frac{\operatorname{Var}Z}{(\mathbb EZ)^2}
 \le\frac1{\mathbb EZ}+\frac p{1-p}\longrightarrow0.
\]

The first term tends to zero because EZ is asymptotic to ne^−A. Chebyshev gives Pr(Z=0)→0. A spanning perfect matching has no isolated vertex, so its containment probability also tends to zero.

Given any proposed fixed L, use A=2eL. Since Lq(H;n)≤A/n for large n, monotonicity gives failure of the claimed success probability at Lq. Globally compatible, injective piece embeddings would be an embedding of H, a contradiction. Even vertex-disjoint source pieces do not avoid this problem: their separately chosen target images need not be disjoint. Requiring agreement only on common roots is weaker and is **not** refuted by this argument; within the source's small-Y cut range it is already supplied.

## 7. Rooted resilience: what fails and what survives

### 7.1 The local edge-deletion target is false

Take s=2, r=n^−1/200 and Y={1,2}. Then r^s=n^−1/100 and s≤10 log n for all sufficiently large n, as required in `prop:transfer`. Set p=r_*=1−(1−r)^32. Thus p→0 and np→∞. Let J consist of one outside vertex adjacent to both roots. J has one outside positive-degree vertex, degree two, and appears with the prescribed roots in a source graph G(n,r) with probability tending to one since nr²→∞. Since the source's typical class has probability at least 1−1/K0, there exists a source graph in that class with such a witness outside vertex w for every sufficiently large n; choose this w and then fix the labelled J. A union bound proves this existence without any independence between typicality and wedge occurrence.

In a target G(n,p), delete every edge from root 1 to a common neighbor of roots 1 and 2 outside Y. This kills every prescribed-root copy of J. The number C of deletions at root 1 is Bin(n−2,p²), while every other affected vertex loses exactly one edge. For any fixed ε>0,

\[
 \Pr(C>\varepsilon np)\le\frac{(n-2)p^2}{\varepsilon np}
 \le p/\varepsilon\longrightarrow0.
\]

Also 1≤εnp eventually. Thus with probability tending to one the deletion has maximum degree at most εnp and eliminates all such embeddings. Markov's inequality suffices; no unverified random-graph resilience theorem is used. This obstruction concerns **fixed roots**. It does not claim that all unrooted wedges are destroyed.

### 7.2 A complete technical vertex-deletion partial

Under exactly the source's transfer hypotheses, increase its absolute N1 if needed so that m0=n−|Y|≥n/2. On the source's simultaneous target-test event, every admissible cut piece J still embeds fixing Y after **any** deletion of at most

\[
 t=\lfloor nr^s/20\rfloor
\]

candidate vertices outside Y. This statement embeds the active bipartite support; discarded isolated vertices of an n-vertex presentation are not asserted to fit into a smaller host after deletions.

Indeed, for any nonempty family U of outside vertices to match, the source compression gives a test Q with x=x(Q)≥r^s, source demand |U|≤4xm0, and target supply at least (3/4)x_*(Q)m0.

If x≤1/16, the source's amplification gives x_*≥8x, so supply minus demand is at least 2xm0≥nr^s>t. If x>1/16, supply is at least (3/4)(1−e^−1)m0 and demand at most n/8. Their difference is at least `[3(1−e^−1)/8−1/8]n>n/20≥t`. The strict numerical inequality follows already from e>2. Deleting t candidates therefore preserves every Hall inequality, simultaneously for all choices of deleted vertices. Hall supplies the required active-support injection.

This proof uses the very inequalities already displayed in the source. It changes neither the compression construction nor the probability event, so it is explicitly technical. It does not imply resistance to local edge deletions; Section 7.1 explains why those are a different operation.

## 8. Same-density two unions: explicit fractional construction and exact unpaid step

Let X=[N], 0<p<1, D⊆2^X, f=1_D, and a=μ_p(D)>0. Use the source's signed coefficients

\[
 b(U)=(1-p)^{|U|}\sum_{z\in\{0,1\}^U}(-1)^{|z|}
              \mathbb E[f(z,Y)],\qquad w(U)=b(U)^2,
\]

where Y is the product sample outside U. For S∈E_2(D), use two rows rather than the source's 32. In columns of S give (x,y) the signed mass

\[
 p^{x+y}(1-p)^{2-x-y}-(1-p)^2(-1)^{x+y};
\]

outside S use product masses. The mass of the all-zero column is zero. Every array with nonzero mass covers S by its two rows, so the product of the two f-values is zero. Expanding the finite column product gives

\[
 0=\sum_{U\subseteq S}(-1)^{|U|}w(U),\qquad
 \sum_{\varnothing\ne U\subseteq S}w(U)\ge a^2.                \tag{8.1}
\]

Thus c_U=min{1,w(U)/a²} for nonempty U, c_empty=0, is a fractional cover of E_2(D). Capping preserves coverage: either a capped coefficient alone is one or the total is unchanged. The source Fourier normalization gives

\[
 p^{|U|}w(U)=(1-p)^{|U|}\widehat f(U)^2.
\]

Removing the constant coefficient and retaining the factor (1−p),

\[
 \sum_{U\ne\varnothing}p^{|U|}c_U
 \le\frac{1-p}{a^2}\sum_{U\ne\varnothing}\widehat f(U)^2
 =\frac{(1-p)(1-a)}a.                                        \tag{8.2}
\]

In particular, this cost is ≤1/2 whenever

\[
 a\ge\frac{2-2p}{3-2p}.                                      \tag{8.3}
\]

This is **exactly the fractional conclusion of Li v2, Theorem 1.15**. His proof uses the same signed spectral operator and LP duality; (8.1)–(8.2) expose explicit coefficients. It is attributed technical work, not a new result from this project. It is also a lower source-proof operation (the two-row version is explicitly credited in the pinned 32-row proof).

The integral companion converts the budget into a cover at p/(25·512^4). That does not close D. Its actual selector/rounding proof chooses the color products so their mean is at most the fractional density divided by five; setting the target density equal to p loses this mean comparison for sets of unbounded size. A small total cost (8.2) at p does not control `Σ c_U(Cp)^|U|` for an absolute C>1 and unbounded |U|. No such control or a replacement same-density rounding construction is proved here.

Trying the pinned 32-row covering argument with two rows has a specific failure: the exceptional estimate is a **first** power sum of w, not a sixteenth power sum. In a bin w≤2^−h, the existing bound of fewer than 2^{12h} members gives only 2^{11h}, rather than the summable 2^−4h used by the source. Replacing 32 by 2 in the same proof is not legitimate. It would require a new cover that uses the special spectral structure of these weights; ordinary fractional rounding alone is insufficient as currently available.

The high-bias range is already elementary. If p≥1/2, make two Bernoulli-p rows coordinatewise by probabilities `Pr(1,0)=Pr(0,1)=1−p`, `Pr(1,1)=2p−1`, `Pr(0,0)=0`, independently across coordinates. Their union is X surely. If a>1/2, both rows belong to D with positive probability by the union bound. Therefore E_2(D)=empty. At a=1 or E_2(D)=empty, the empty cover suffices for all p. The unresolved range is 0<p<1/2 and a uniformly close to, but below, one. The report neither proves nor refutes D there.

## 9. Evidence, reproducibility, and limitations

The source directory records full source bytes and exact passage ranges, primary version pages/PDFs/text, retrieval status and failures, frozen scope controls, source contracts, prior-screen line **multisets**, and a separate immutable-old-file watch. The four shared ledgers `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` are explicitly informational/mutable. The frozen prior-screen domain is the finite list of I13/I19/I22/I25 input reports; it is never expanded on replay. No I52 verifier or historical seal was changed or re-sealed. Its historical growing-domain failure remains untouched; this task does not describe a replay of that verifier as passing.

Current literature checks were performed before development and after formulation. Retained final search results include irrelevant hits and prove no absence theorem. The attempted `mathdb.org` homepage is a Korean mathematics site, not a verified matching open-problem catalogue; domain-restricted searches produced no relevant verified entry. No MathDB score or problem rank is invented. AHPT Section 8 and Talagrand's problem as quoted and distinguished in the actual sources provide the verified problem context.

The read-only exact diagnostic has **59,175 assertions**. It exhausts every Boolean function on every interior slice for 2≤N≤5; also every vertex-invariant function on every K4 slice. It constructs the completion extension explicitly and independently sums variances, swaps, adjacent gradients, and coarea intervals using rational arithmetic. Priority fiber identities are checked by all rankings for N≤4. Further tests cover every dyadic threshold through eight bits, the repeated-edge capture counterexample, wedge formulas for n=4,…,12, matching-spread products and isolation moments, and every set family on at most three coordinates at three rational biases for the two-row signed certificate. No finite test is substituted for the general proofs, no interval-free decimal is used as a certificate, and no algorithmic complexity theorem is claimed.

From the project root, both commands are read-only and print JSON:

```sh
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i60_threshold_structural_combinatorics_discovery/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i60_threshold_structural_combinatorics_discovery/verify.py
```

The verifier checks the report/evidence seal, frozen inputs, live immutable reports and watched old seals, selected Git blobs, all 9,340 cached corpus identities, exact passage hashes, primary response bytes, sorted prior-search multisets, and an independent rerun of the diagnostics. Live ledger drift is listed separately. The seal excludes only itself and the last verifier-output file; it is not a claim of independent proof review or worldwide novelty.

**Handoff.** T/S/Sη/SH and the restricted Hall slack theorem are complete technical partials. The all-density unnormalized slice claim, globally compatible decomposition, and proposed rooted local-edge-resilience claim are refuted in their exact stated scopes. The same-density two-union integral cover D remains unproved and unrefuted; its available fractional construction is already Li's current result. No further deduction here has an indispensable new mechanism that survives the contribution gate, so no substantial acceptance is requested.
