# I25 rooted matching entropy: independent significance and primary-prior-art review R3

**Verdict: SUBSTANTIAL candidate, conditional on proof correctness.** The contribution is the all-roots entropy allowance that is exactly additive under tight-cut contraction, used inside a global-maximizer induction to make the stronger no-cut dimension estimate applicable. This supplies the separator compensation missing from I22 and lowers the universal prescribed-mean coefficient from 2 to 3/2. The ingredients of the calculation are inherited; the connection that makes them prove this uniform improvement is substantive under the stringent standard applied to I15, I17 and I22. This is a significance judgment, not an acceptance/count action or a priority certificate.

The separately requested [R2 proof review](i25-rooted-entropy-proof-r2.md) became available before completion and reports **PASS** for the full universal rooted theorem, without repairs. I read its completed report and froze that input. My significance conclusion does not replace its proof audit, and remains conditional on the theorem being correct.

**Reviewed object and obligations.** The candidate is the entire resumed report [I25](../iterations/i25-matching-entropy-improvement-resumed.md), SHA-256 `154c12153988580f2845680f6824168c981e1f420c36c623886788b79f780824`. This review read that report and [I22](../iterations/i22-combinatorial-discovery.md) in full. The current ledger records four accepted findings toward the requested ten; this review changes neither ledger nor count. The operative R3 brief and original discovery brief are frozen. All OpenAI proofs pinned at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are assumed true. Only this report and the two authorized R3 evidence directories were written.

The complete pinned entropy manuscript was read, including all ten sections, all three appendices, the weighted consequences, component refinements, triangle-expansion examples and references. The direct FPRAS companion was checked at its theorem/input interfaces, including its weighted-input restrictions; this is not a fresh full audit of that algorithm. The full 749-manuscript inventory and all 9,340 cached text files were screened without copying the cache. The screen is not a claim to have read all 749 manuscripts.

**Exact theorem being judged.** Let $G$ be a finite loopless labelled multigraph on $2m\ge2$ vertices, with at least one perfect matching. For every $x\in P(G)$, let $H(x)$ denote the *maximum* entropy among matching laws with edge mean $x$, using natural logarithms. Set

\[
 F=-\sum_e x_e\log x_e,\qquad B=-\sum_e(1-x_e)\log(1-x_e),\qquad
 b_v=-\sum_{e\ni v}(1-x_e)\log(1-x_e),\quad D=F-H.
\]

The proposed assertion is, simultaneously for every root $v$,

\[
                 D(x)\le\tfrac32 W_v(x),\qquad W_v=B-b_v. \tag{R}
\]

Parallel edges remain distinct labels, and means on proper faces or with coordinates zero or one are included. Since $\sum_vb_v=2B$, averaging gives

\[
                 D(x)\le\tfrac32(1-1/m)B(x). \tag{U}
\]

The [strongest pinned source theorem](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/build/sections/01-introduction.tex) gives $D\le2(1-1/m)B$, not merely the older coefficient-three or coefficient-four appendix bounds. Thus the finite-order coefficient improves by a factor of $3/4$, for every $m>1$; it is not a degree cutoff or a fixed-order corollary. At $m=1$, both bounds are the exact equality $D=0$. Disconnected instances also admit componentwise application: source component refinements must be compared with corresponding componentwise candidate applications, rather than claiming that a single global formula always dominates every source refinement.

**What is inherited, and what changes the argument.** The following are available in the pinned source or standard primary literature: Edmonds' face description; the general supported-face dimension estimate $d\ge s-3m+2$; no-cut dimension $d\ge s-2m$; finite exponential-family covariance on the minimal face; stationarity/second-variation trace; conditional gluing through a labelled crossing edge; and the elementary ternary entropy inequality. The source already handles faces and labelled multigraph contractions. Neither the notion of a root, the function $b_v$, contraction, nor a short Hessian computation should be presented as novel in isolation.

The new organization is precise. For a nontrivial odd cut tight at the mean, write its crossing distribution as $q$, retain the original root in child 1, and use the contracted vertex as child 2's root $z$. Conditional gluing and maximum-entropy optimization give

\[
 H=H_1+H_2-h(q),\quad F=F_1+F_2-h(q),\quad
 B=B_1+B_2-b(q),\quad D=D_1+D_2.
\]

The original star is preserved in child 1, and $b_z=b(q)$ in child 2. Consequently

\[
               W_v=W_{1,v}+W_{2,z},\qquad
 D-cW_v=(D_1-cW_{1,v})+(D_2-cW_{2,z}). \tag{A}
\]

The usual unrooted potential instead satisfies

\[
 (D-cB)=(D_1-cB_1)+(D_2-cB_2)+c\,b(q). \tag{O}
\]

I22 could not pay that positive separator term. The simultaneously quantified root is exactly what pays it here; merely decomposing into bricks or invoking child unrooted inequalities does not do so.

The induction uses (A) at a **positive global maximum**, after deleting zero edges and handling fixed matching edges. A tight nontrivial odd cut would contradict the smaller-order rooted statements. Only then can the source's stronger no-cut dimension estimate be used. With $c=3/2+\epsilon$, the rooted Hessian changes the diagonal to

\[
 A_{ee}=-1/x_e+c\,\mathbf1_{e\not\ni v}/(1-x_e),
\]

and the source covariance calculation becomes

\[
                  0\ge d-s+m+c(m-1). \tag{T}
\]

Combining $d\ge s-2m$ with (T) gives $0\ge(c-1)m-c=(m-3)/2+\epsilon(m-1)>0$ for $m\ge3$. The two- and four-vertex cases are handled separately by labelled parallel collapse and the ternary inequality. Letting $\epsilon\downarrow0$ supplies the endpoint. This summary identifies the mechanism; R2 supplies the independent full proof audit.

**Reduction tests against the strongest available source mechanisms.** Three explicit checks keep the significance decision from resting on the absence of the displayed theorem in the source.

First, substituting the rooted objective into the old covariance/rank proof does **not** automatically improve its constant. Using the unrestricted source rank bound in (T) gives exactly

\[
 d-s+m+c(m-1)\ \ge\ (c-2)(m-1).
\]

This still has threshold 2. Conversely, the unrooted objective with source contraction leaves (O). The candidate needs both the additive rooted allowance and the induction that makes the better rank bound legal. Neither ingredient alone is a certificate of the theorem. This is a concrete bridge between two already available source interfaces, not a parameter substitution in a theorem whose hypotheses were already satisfied.

Second, the elementary route that made I22 technical does not extend uniformly. On $K_6$ minus a perfect matching, with mean $1/4$ on its twelve edges, $F=3\log4$, $B=9\log(4/3)$, $b_v=3\log(4/3)$. The elementary bound $H\ge F/m$ used by I22 yields $D\le2\log4$, exceeding the desired $\tfrac32W_v=9\log(4/3)$. The comparison is exact: $3^9>4^7$. The strongest finite-order source theorem gives $D\le12\log(4/3)$, also too large. The nonlinear appendix bound is 18 here, and its minimum with $F$ is still insufficient. The actual entropy is $\log8$, so this is an insufficiency example for these interfaces, not a counterexample. It rules out the direct scalar/finite-order/nonlinear combination used for I22; it does not prove that no ingenious consequence of the source could ever recover (R).

Third, positivity of all edge coordinates does not remove odd-cut face constraints. Source Klee-type faces have positive supported coordinates while retaining binding nontrivial cuts. The candidate cannot obtain the no-cut rank by simply deleting zero edges, nor can it exclude every fractional local maximum. Its ancillary Klee analysis exhibits negative fractional local maxima, even in the full polytope at the stated orders. Their sign explains the need for a positive **global** maximum and simultaneous induction. That analysis clarifies the bridge but is not counted as another substantial finding.

The four-vertex parallel-collapse argument, finite-order averaging, weighted duality and elementary counting substitutions are routine once (R) is proved. The significance case rests on the combined mechanism above, not on treating these consequences as independent advances. The same strict test rejected I15's iteration of an operation already used in its source proof and I17's elementary adjugate lifts plus a source product. Here a failed separator inequality is repaired by an invariant that also changes which face geometry can occur at an extremum; the reduction stops at a substantive missing step in the old argument.

**Primary prior-art comparisons.** Retrievals were fresh on 2026-10-09. Version-specific PDFs, abstract/current pages, HTTP metadata, submission histories and byte hashes are retained. The statements below were checked in primary text, not inferred from search snippets.

1. **Bipartite weighted Bethe comparison.** [Gurvits, arXiv:1106.2844v11](https://arxiv.org/abs/1106.2844v11), submitted 2012-06-20, Theorem 2.2 and its proof, gives the weighted permanent lower bound by maximizing the Bethe functional over doubly stochastic matrices. In the present notation the functional is energy plus (F-B). Entropy duality therefore supplies $H(x)\ge F(x)-B(x)$ for prescribed *bipartite* means, with boundary handled by limits. This is genuine prescribed-mean prior art, not counting-only prior art. Its coefficient 1 is stronger than the candidate's universal asymptotic coefficient on that subclass. It does not extend the weighted permanent theorem to a general hafnian; source nonbipartite examples already violate coefficient 1. Nor does coefficient 1 automatically subsume every rooted or small-order bound: (U) has coefficient $3/4$ at $m=2$. Scope and finite-order direction both matter.

2. **Nonbipartite Bethe and loop calculus.** [Chertkov, Gelfand and Shin, arXiv:1306.1267v1](https://arxiv.org/abs/1306.1267v1), 2013-06-05, is directly about arbitrary-graph perfect matchings. Its Bethe entropy is (F-B), on the degree-constrained relaxation; its loop and bootstrap identities, notably equations $20$–$21$, leave a transformed partition function or signed loop correction. Odd loops need not contribute positively. Section 9 explicitly raises the nonbipartite lower-bound extension as a question in that paper. Reading the formulas as a theorem that $Z\ge Z_{BP}$ for arbitrary graphs would be an error. No bound there evaluates the residual hafnian by the rooted $3/2$ allowance. The missing step is quantitative control of that correction, not a change of notation. The paper's older conjectural wording is not a statement of current unresolved status beyond what this search establishes.

3. **Root/star functionals in recent entropy work.** [Dong–Jain, arXiv:2609.02017v1](https://arxiv.org/abs/2609.02017v1), 2026-09-02, Theorems 1.3/3.1 and the good-vertex proof use $H_B=F-B$ and complementary star entropy. Their girth-dependent inequality is an **upper** comparison for matching-law entropy in the bipartite setting; the local star function and a vertex selected for a conditioning argument already occur. Thus the star functional by itself is not the contribution. Their argument does not provide a lower bound for the maximum-entropy law at every general-graph mean, simultaneously for every root, or the compensation (A). [Du–Xue, arXiv:2607.15549v1](https://arxiv.org/abs/2607.15549v1), 2026-07-17, Theorems 1.2–1.3 likewise give bipartite counting upper bounds with distinguished vertices in a reveal order. A distinguished vertex in an upper-bound proof is not this lower-bound invariant.

4. **Recent permanent approximation.** [Dong–Jain, arXiv:2609.11049v1](https://arxiv.org/abs/2609.11049v1), 2026-09-10, Theorem 1.1 gives, for fixed positive epsilon, a deterministic strongly polynomial multiplicative approximation to the nonnegative permanent within $(1+\epsilon)^n$. This is a stronger algorithmic statement in a different, bipartite weighted-counting domain. Neither a general hafnian nor an arbitrary prescribed-mean lower comparison follows by substituting a symmetric matrix into a permanent algorithm.

5. **Counting on high-dimensional faces.** [Abdi–Cornuéjols–Dadush–Dalirrooyfard, arXiv:2505.14497v2](https://arxiv.org/abs/2505.14497v2), 2026-04-20, was read beyond Corollary 6.6: Theorem 1.2 concerns minimal faces through special coordinates $1/\lambda$ or $1-1/\lambda$ in cube-ideal systems, with dimension at least a fixed positive fraction of the ambient dimension. Its proof constructs a cube slice inside the face and applies a geometric vertex-count estimate. Theorem 5.4 translates this to clutter cores; Theorem 6.3 and Corollary 6.6 apply rank bounds to regular graph counts. This already proves exponential counts at degrees at least four, including matchings respecting all minimum odd cuts. It supplies neither a weighted prescribed-mean entropy law nor the explicit universal $3/2$ complementary-entropy coefficient. Cardinality of a face does not bound maximum entropy at a specified point by the logarithm of that cardinality from below. The candidate's degree-four exponential consequence is therefore not a first exponential-count result.

6. **The closest old contraction/rank mechanism.** [Edmonds' 1965 primary polytope paper](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p125_A1b.pdf), Theorem (P), supplies the original matching inequalities; the degree-one face gives the perfect-matching description. [Edmonds–Lovász–Pulleyblank, 1982](https://doi.org/10.1007/BF02579233), Theorem 5.1, gives the brick-sensitive rank formula. Crucially, Lemma 5.5 already treats the family of matchings crossing a chosen odd cut once, with rank identity $r(\mathcal M_C)=r(G_1)+r(G_2)-|C_{\rm usable}|$, not only cuts tight for every matching of the original graph. Its proof glues affine bases of contractions. Thus it would be unfair to dismiss all older decomposition machinery as applying to the wrong domain. What it lacks is an entropy potential paying $b(q)$, and the all-root global-max induction. The source already imports the face/cut geometry. Rephrasing the old rank identity does not supply (A) as an inductive entropy theorem.

7. **Uncrossing and current tight-cut structure.** [Svensson–Tarnawski, arXiv:1704.01929v2](https://arxiv.org/abs/1704.01929v2), 2017-09-04, Lemma 2.2 and Appendix A give the laminar spanning description of tight face rows. [Lu–Dong, arXiv:2605.25695v1](https://arxiv.org/abs/2605.25695v1), 2026-05-25, Theorems 1.1/1.3 and its contraction proposition describe tight cuts in matching-covered multigraphs through barrier and related structures. These are structural inputs or refinements; neither passage furnishes a rooted complementary-entropy lower bound. The 1982 cut-restricted lemma above is the stronger relevant comparison, so the verdict does not depend on ignoring it.

8. **Entropy/counting duality and oracle access.** [Singh–Vishnoi, arXiv:1304.8108v1](https://arxiv.org/abs/1304.8108v1), 2013-04-30, Lemma 2.3 and Theorems 2.6–2.8, formalize maximum-entropy duality and the algorithmic connection with weighted generalized counting oracles and interiority assumptions. Weighted Gibbs duality is inherited. An unweighted counting FPRAS does not by itself provide the weighted marginal oracle needed for their maximum-entropy algorithms. The pinned direct companion must be used with its stated input contract; neither it nor this candidate automatically yields a new efficient sampler or prescribed-mean optimizer.

9. **Optimized binary entropy.** The original [Anari–Oveis Gharan–Vinzant FOCS 2018 paper](https://ieee-focs.org/FOCS-2018-Papers/pdfs/59f035.pdf), Conjecture 6, asks for a linear-error relation between optimized binary-coordinate entropy and log count. The correct arXiv companion is [1807.00929v2](https://arxiv.org/abs/1807.00929v2), 2018-11-05. This optimized objective is (F+B), not $H(x)$ for every fixed $x$. The pinned entropy source already answers that conjectural interface quantitatively. I25 improves its additive constant through (R); it is not a fresh solution of the original conjecture.

10. **Stronger counts in restricted classes.** [Esperet et al., arXiv:1012.2878v2](https://arxiv.org/abs/1012.2878v2), 2011-09-05, Theorem 1 proves at least (2^{|V|/3656}) perfect matchings for every bridgeless cubic multigraph. [Ebrahimnejad–Nagda–Oveis Gharan, arXiv:2103.08683v1](https://arxiv.org/abs/2103.08683v1), 2021-03-15, Theorems 1.3–1.4 impose spectral expansion and give algorithmic/counting conclusions approaching a stronger degree-dependent scale under suitable expansion. [Cuckler–Kahn, Combinatorica 2009](https://doi.org/10.1007/s00493-009-2366-9), Theorem 1.1, gives asymptotically sharper total counts for Dirac graphs; Theorem 1.2 is an upper bound on arbitrary matching-law entropy subject to a marginal smallness condition. None is a universal finite-order prescribed-mean lower bound on all loopless labelled multigraphs. I25 should not claim to dominate these specialized theorems.

11. **Klee examples and old obstructions.** [Cygan–Pilipczuk–Škrekovski, 2013](https://dmtcs.episciences.org/633), Lemma 2.1, gives the triangle-expansion three-colour structure used in the pinned source's examples. Three matching types on a constrained face do not mean that the whole graph has only three matchings; confusing these would conflict with the cubic counting theorem. The sharp scalar ternary constant $c_3=\log3/[2\log(3/2)]\approx1.35475565$, and its role as a general-graph obstruction through the source examples, are inherited. The review found no new lower obstruction from the computational searches.

These comparisons support a new mechanism relative to the strongest material actually checked. They do not establish exhaustive priority across all literature, unpublished work, or every source in the inventory. No exact duplicate found is not the logical basis of the verdict.

**Magnitude and limits of the consequences.** For finite edge log weights $\theta$, put $Q_\theta=\max_{x\in P(G)}[F(x)+\theta\cdot x]$. The usual Gibbs variational principle and $B\le m$ turn (U) into

\[
 Q_\theta-\tfrac32(m-1)\le\log Z_\theta\le Q_\theta,
\]

improving the pinned source's (2(m-1)) loss. The more precise bound maximizes $F+\theta\cdot x-\tfrac32(1-1/m)B$; this is a mathematical variational comparison, without an algorithmic efficiency assertion. Similarly, the optimized $F+B$ gap changes from $3m-2$ to $\tfrac52m-\tfrac32$.

For $k\ge2$ disjoint perfect matchings, or for a $k$-regular graph with every odd cut at least $k$, substitution of the feasible uniform mean gives

\[
 N(G)\ge k^m(1-1/k)^{\frac32(m-1)(k-1)}
       \ge k^m e^{-\frac32(m-1)}.
\]

The coarse bound improves by (e^{(m-1)/2}) over the source, and its growing-degree base changes from (k/e^2) to (k/e^{3/2}). That is an exponential-in-order improvement, not an epsilon that disappears with size. The refined degree-four base (4(3/4)^{9/2}) exceeds one; earlier cube-ideal results already establish exponential growth there. Regularity without the odd-cut hypothesis is not the claimed input. The ordinary matching-covered condition must not replace it.

The sharp universal coefficient remains undetermined between the inherited $c_3$ lower obstruction and the candidate's $3/2$ upper bound. The old suspected rooted ratio near 1.3677 was a cancellation artifact corrected to approximately 1.0017100294; it must not be used as a new lower bound. The Klee lower obstruction remains the relevant certified one. No new sampling algorithm, oracle implementation, optimal-constant result, or separate accepted finding follows just from these corollaries.

**Independent diagnostics and evidence quality.** This review's exact checks are deliberately about significance interfaces, rather than duplicating R2's full proof audit. The deterministic script verifies 1,888 edge-charge identities across cuts/roots, 294 rational evaluations of the strict trace contradiction, the exact degree-four scalar barrier $3^9>4^7$, and an arbitrary-law scope counterexample. For the last, a uniform law on a five-factorization of $K_6$ has uniform edge means $1/5$, entropy $\log5$, and $F-\operatorname{Ent}=2\log5>12\log(5/4)=\tfrac32W_v$, certified by $4^{12}>5^{10}$. The *maximum* entropy at this same mean is $\log15$. Hence replacing $H$ with entropy of any law would be false. These finite identities are not evidence of universal proof by enumeration.

The parent's reported larger Gibbs/root/gluing audit is retained as an input, not relabelled as this review's own experiment. The resumed author's 70-artifact seal and the 1,226-file original checkpoint are independently checked read-only by this review's verifier. Its input/content checks include the frozen candidate, full source text, exact extracted theorem contracts, read passages, primary retrieved bytes and version histories. Failed or mistaken retrievals are retained and explicitly excluded: nonexistent bootstrap v3 was corrected to v1; an incorrect Anari identifier was corrected to 1807.00929v2 plus the FOCS PDF; a Citeseer HTML response was replaced with the original published Cuckler–Kahn PDF. HTTP success alone is not treated as a paper.

Evidence is in [sources](../sources/i25_rooted_entropy_novelty_r3/) and [experiments](../experiments/i25_rooted_entropy_novelty_r3/). The operative brief is `full-brief.txt`; `inputs.json` freezes dependencies; `pinned-manifest.json` binds the 18 pinned source files to raw Git URLs, blobs and SHA-256; `source-contracts.json` and `read-passages.json` give exact text locations and hashes; `search-01.json` through `search-06.json` preserve queries/results; `literature/manifest.json`, `extra-manifest.json`, `version-history.json` and `retrieval-assessment.json` bind primary versions and rejected retrievals. `artifact-seal.json` covers this report and review-owned artifacts, excluding the seal itself and the generated verification output. Run `python frontier/experiments/i25_rooted_entropy_novelty_r3/verify.py` from the project root. Shared ledger/index drift is reported separately and is never silently reset.

**Final verification: PASS.** The offline verifier checks 126 sealed review artifacts, 19 frozen inputs, 18 pinned source files, 38 extracted theorem contracts, 51 read passages, 45 retrieved byte artifacts and 18 parsed primary texts. It independently confirms the resumed author’s 70-artifact seal, all 1,226 original files and all 9,340 read-only cached texts; the exact diagnostics reproduce byte-for-byte. During this review, the shared TEN-FINDINGS.md, frontier/README.md, parent integration note and Git index changed externally. Their baseline/current hashes are recorded separately in verification.json; none was rewritten or reset by this review. The candidate report and frozen R2 result did not drift. The ledger still records four accepted findings. Evidence-integrity PASS is not an independent universal-proof or priority certificate.

**Decision boundary.** On the evidence reviewed, there is no precise reduction certificate eliminating the separator/global-maximum bridge, no identified scope gap in the theorem that would make the improvement illusory, and no located primary theorem already delivering that bridge or the same universal bound. There is a concrete new combined invariant with a uniform, quantitatively material consequence. That warrants **SUBSTANTIAL candidate**, conditional on proof correctness. A primary source already using the same rooted separator compensation with the no-cut induction, or a direct source-theorem reduction without that substantive step, would change this significance judgment. The simultaneous R2 PASS strengthens confidence in correctness but does not certify priority or determine acceptance.


**Historical original discovery brief (verbatim).** The following is retained as the requested research history. Its path permissions are superseded by this R3 task's restrictions; this review has not written to the historical destinations.

```text
Work in /home/mj-kang/Documents/Dev/math/openai-proof-research. Read AGENTS.md/current ledger. User resumed ten substantial findings and authorized T3 agents; four accepted. Assume all proofs in openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb true. I25 focused constructive matching-entropy improvement beyond I22. No agents, sharedindex changes, staging, commits, pushes, or otherproject edits. Write only frontier/iterations/i25-matching-entropy-improvement.md and frontier/{sources,experiments}/i25_matching_entropy_improvement/.

Read FULL I22 report, actual entropy source including proof, nonlinear appendix, component refinements/examples, relevant companions and primary literature. Parent read I22, reproduced162sealedartifacts107pinnedfiles236contracts,2688densitytests and entropy/gluingdiagnostics. Neither I22 technical deduction is independent-proof accepted or a substantial finding. Do not recycle polynomialprophet completion or subcubic result.

Exact promising target: for every finite loopless labelled multigraph with a perfect matching and every x in its matching polytope, H(x)>=F(x)-(3/2)B(x), where H maximum matching-law entropy with mean x, F=-sum xlogx, B=-sum(1-x)log(1-x), naturallogs. Source gives coefficient2-2/m on2mvertices. More generally any rigorously proved universal coefficient strictly below2 with a genuine new bridge and exact scope would be meaningful; don't weaken to a trivial finiteorder/degree corollary. Target is not assumed true! First adversarially test structured graphs/Gibbs means; a rigorous substantive counterexample improving known lowerbound could be useful, numerical evidence alone is not.

I22 exact facts to independently scrutinize: subcubic sharp coefficient(1-1/m)c3, c3=log3/(2log(3/2))≈1.35475565, follows scalar ternary h<=c3b and H>=F/m; source Klee examples attain it, so notnew mechanism. Uniformdegree4 scalar h>(3/2)b, but K6minusmatching actualentropy is notcounterexample. For tightoddcut with crossing distribution q, entropygluing H=H1+H2-h(q), deficit D=F-H additive, B=B1+B2-b(q). Hence E_c=F-cB-H satisfies E_c(parent)=E_c(child1)+E_c(child2)+c b(q). Must pay positive separator sum; cannot drop it. Source trace at fractional localmax gives0>=d-s+(c+1)m; source dimension d>=s-3m+2 yields only0>=2+(c-2)m, insufficient c1.5 for m>=4. Need extra covariance/face or aggregate separator information. Near-tight conditional entropy estimate in I22 is standard, depends on unknown maxentropy law and log(numbermatchings); not a sampler or missing allowance.

Constructively investigate at least two mechanisms: strengthened Hessian/covariance trace using star constraints and tight-cut structure, versus aggregate entropy construction on tight-cut decomposition with explicit separator compensation. Also actively search for finite counterexamples through exact perfect-matching enumeration and positive Gibbs laws: Gibbs law is entropy-maximizing at its own edge means; if ratio exceeds proposed bound, certify it analytically or with rigorous rational/log bounds. Consider structured higherdegree extremizers before assuming sharp coefficient c3. Preserve labelled parallel edges/boundarymeans, contraction conventions and conditional compatibility. Do not infer weighted prescribedmean entropy from uniform FPRAS; convexoptimization access is not automatic. If only boundeddegree improvement emerges, verify nonroutine significance and new mechanism versus scalar categorical inequalities before proposing.

Compare strongest source-proof interfaces and fresh current primary literature early. Full749inventory sources/preprints-tree.json (paths preprints/), read-only9340textcache frontier/sources/i14_spectral_width_novelty_r3/corpus/ andmanifest; no truncatedtree. Other tasks I23kinetic and I24unimodality separate. Freeze originalbrief/dependencies, pinnedrawURLs/Git/SHA, exactstatementcontracts/readpassages, query and primaryversionbytes, deterministicdiagnostics with numerical limitations, artifactseal/verifier. Do notcopywholecache. Record sharedindexdrift separately. Deliver complete meaningfulcandidate ready for separate independentproof/significance or precise investigatedgap. No count/findingnumber/priorityclaim.
```
