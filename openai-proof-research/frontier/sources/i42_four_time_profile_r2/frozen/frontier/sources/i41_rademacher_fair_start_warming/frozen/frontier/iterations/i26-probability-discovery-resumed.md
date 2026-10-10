# I26 resumed — probability discovery and the integer-height interface gap

Research date: 2026-10-09. Premise: all proofs in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. **Disposition: completed three-target screen and constructive scoped gap record. The joint integer-height/SLE₄ theorem is not proved.** No finding, acceptance, or priority claim is made.

The strongest route has an exact, useful discrete construction: an oriented zero-interface transcript pins actual heights, its completed components are independent constant-boundary height problems, and its conditional-mean martingales are bounded. This resolves the discrete conditioning issue, but not uniform harmonic approximation in the evolving slit. Crucially, the decisive exploration operation already occurs inside the accepted two-arc source proof. Its specialisation here is technical machinery, not a substantial new bridge. A second attempt through conditional Gaussian laws reaches a separate, explicit uniform slit-covariance/characteristic-function gap. Neither missing input is assumed in a claimed theorem.

## 1. Scope, frozen evidence, and source conventions

The [full brief](../sources/i26_probability_discovery_resumed/full-brief.txt) preserves both the original task and the overriding resumed paths. The original task stopped after preparation; its cancellation cause is unestablished. This completion does not turn that preparation into a historical theorem or seal. No agents were started; no shared indexes, original I26 files, other research paths, staging area, commits, or remotes were changed.

The [original read-only manifest](../sources/i26_probability_discovery_resumed/original-readonly-manifest.json) hashes all 266 files in the two original I26 directories. The 249 original pinned texts were checked against their recorded SHA-256, Git blob identity, and the complete preprint tree before copying. Thirteen original input snapshots were likewise checked. Current rules, ledger and inventory were frozen separately; original and current ledgers are not conflated. Fourteen additional texts for the directly cited balanced-six-vertex companion were selectively copied from the verified read-only corpus cache. There was no whole-cache copy or use of the truncated root-tree cache.

The resulting [pinned manifest](../sources/i26_probability_discovery_resumed/pinned-manifest.json) contains 263 texts from 21 manuscripts, with immutable raw URLs, Git blob hashes, byte counts, and SHA-256. The [statement inventory](../sources/i26_probability_discovery_resumed/statement-contracts.json) retains exact formal environments. The narrower [read-passages record](../sources/i26_probability_discovery_resumed/read-passages.json) identifies the statement and proof passages actually used. An extracted statement is not represented as an independently checked upstream proof. All upstream proofs remain accepted premises.

Short source names below refer to these pinned manuscripts:

- **VC:** *Cardy's formula for critical Poisson Voronoi percolation*, September 23.
- **VP:** *A Pivotal Amplitude for Voronoi Percolation from Cardy's Formula*, October 5.
- **VN:** *From critical crossings to quenched near-critical universality in Voronoi percolation*, October 5.
- **IR:** *Logarithmic Relative Fluctuations in the Weakly Disordered Planar Ising Model*, October 5.
- **IG:** *Quenched SLE3 limits for general weak random-bond Ising models*, October 5; the binary spin-interface and FK-interface companions are also retained.
- **HW:** *Gaussian free-field limits of weighted integer Lipschitz heights*, October 6.
- **H2:** *The Gaussian free field limit of integer Lipschitz heights with two-arc boundary data*, October 6.
- **HR:** *Uniform real Lipschitz surfaces on the triangular lattice*, October 6.
- **SV:** *The Gaussian free field limit of the balanced six-vertex model with variance multiplier 1/arcsin(c/2)*, September 23.

The September versions of HW/H2/HR are retained as direct historical companions; conclusions use the October versions. The other originally selected cubic-percolation and random-map families are retained inventory, not additional fully screened targets.

The negative contexts impose real constraints on this work. I09's binary response does not extend to a matrix response merely by analogy. I13's qualitative mixing does not imply a central limit theorem. I17's common-disorder marginal laws do not identify their joint transform. I20/I23 require normalized, signed, uniformly summable histories, not positive-component surrogates. I15/I17's final reviews require comparison with the operations inside source proofs. None of those parked targets is reopened here.

## 2. Three concrete targets and their dispositions

### A. Birth–death geometry dynamics for Voronoi crossings

**Target.** Start a stationary full-plane marked Poisson process of intensity ε⁻², with independent fair colors attached to nuclei. At microscopic rate aε kill each nucleus; independently introduce new fair-colored nuclei with intensity aε ε⁻² dz dt. Recompute the tessellation after each birth or death. Let rε=1/E Nε(Q*) for the critical unit-square color-pivotal count. Seek one deterministic cgeo>0 such that, with aε=cgeo rε, for every T<∞ and every finite family of rational polygonal quads, the conditional law of their crossing-indicator paths on [0,T], given the **initial uncolored geometry**, converges in probability to the triangular critical color-refresh limit, in the finite-vector Skorokhod J₁ topology. In the triangular reference, each site refreshes to a fair color at rate rδ=1/E Nδ(Q*). The same cgeo must work for all the quads and T. Conditioning here does not freeze future geometries or average them under a partition-function tilt.

**Available contracts.** VC `thm:cardy` gives scalar annealed crossings for every fixed bounded Jordan quad. VP `thm:main` gives ε^(3/4) E Nε(Q*)→cV∈(0,∞). VN `thm:main` already gives convergence in probability of the entire conditional **monotone threshold-vector law** on the compact product of extended real lines indexed by rational polygonal quads. Thus a proposed new joint quenched near-critical threshold theorem would duplicate an accepted result.

There is more machinery than that headline: VN `prop:expansion-bound` permits arbitrary mass-zero signed weights on finite color-history spaces, bounds degree k by C^k k^(-(1−g/2)k) times their total variations, and controls two color replicas on a common geometry; `lem:location-ui` gives insertion-location Lᵖ control; `prop:replacement` preserves signed weights under site-to-square replacement on separated configurations. These are already substantial normalized signed estimates. Frozen-geometry color-refresh finite-dimensional extensions are consequently poor substantial-discovery candidates: replacing the local history weight is largely an application of this existing machinery. No such finite-time variant is submitted here.

**Remaining bridge.** VN explicitly says that adding a nucleus in its Mecke formula represents a sum over existing sites; the signed operation changes colors, not geometry. A real birth or deletion changes neighboring cells and can move several interfaces at once. The missing object is a signed local replacement theorem for this geometric generator, calibrated by one common cgeo and compatible with two replicas conditioned only on their initial geometry. A path theorem also needs tightness controlling rapid back-and-forth crossing changes. Neither a color-pivotal amplitude nor a two-time decorrelation scale identifies those kernels.

**Primary comparison and decision.** Vanneuville's `arXiv:1906.12256v3`, Theorem 1.7, identifies the frozen-color decorrelation scale n²α₄(n); Theorems 1.1–1.3 concern exceptional times. Bhattacharjee–Peccati–Yogeshwaran's `arXiv:2407.13502v1`, Theorem 1.4, already proves sharp noise stability/sensitivity for Voronoi birth–death (OU) dynamics at that scale. These are stronger comparisons than an absence-of-search-hits argument, but neither quoted statement supplies the proposed common continuum path law or its quenched initial-geometry version. The target is worthwhile because geometry dynamics, unlike recoloring, changes the microscopic connectivity itself. **Not selected:** a calibrated geometric insertion identity is missing; the height route below offers an exact conditioning mechanism that can be developed further within this task.

### B. A central limit law for the logarithm of a quenched Ising correlation

**Target.** For every sufficiently small fixed ε>0, take iid fair ξe∈{−1,1}, Je=1+εξe, at the physical critical inverse temperature. First take the free thermodynamic limit at each integer separation r, giving Cε,ω(r)>0. Seek

\[
 \frac{\log C_{\varepsilon,\omega}(r)-\mathbb E\log C_{\varepsilon,\omega}(r)}
 {\sqrt{\tfrac14\log\log r}}\Rightarrow N(0,1),
 \qquad
 \frac{\operatorname{Var}(\log C_{\varepsilon,\omega}(r))}{\log\log r}\to\tfrac14.
\]

These are proposed disorder statements, not assertions proved here. The log is integrable for each fixed r: comparison with a nearest-neighbor path and the strictly positive minimal coupling supplies a deterministic positive lower bound on C(r). The limits do not take ε→0 with r.

**Available contracts.** IR `thm:main` proves log(E C²/(E C)²)/log log r→1/4 and identifies the binary self-dual critical temperature by sinh(2β(1−ε))sinh(2β(1+ε))=1. Its proof is stronger than a second-moment black box: `mark:moments` yields A(j,q)=j^(binom(q,2)/8+o(1)) for each q in a fixed finite collection of even source powers chosen before the small-disorder threshold; `mark:kernel` controls the complement of the marked charge, and `read:moments` controls the physical two-point readout in L¹/L². This is not a statement uniform in real or complex q near zero. Positivity of the even moments of the auxiliary αj is not pathwise positivity of αj.

IG already covers quenched SLE₃ interface laws for each fixed bounded mean-zero iid bond law with positive variance. Its conclusion concerns an interface law after averaging spins, not fluctuations of log C over bonds. The binary and FK companions likewise do not identify that log-law.

**Remaining bridge.** One would need either a positive scale-by-scale factorization of the physical correlation with a martingale bracket and Lindeberg control, or a uniform small-complex-parameter expansion of E exp(z(log C−E log C)) at z=O((log log r)^−1/2). Substituting a noninteger q into a finite tensor power, or taking logarithms of an L² approximation without a small-value estimate, is invalid. The scale recursion for **averaged** marked moments is not already an independent-increment representation of log C.

**Adversarial check.** Let m→∞, L=m⁴, and take X=1/2 with probability 1−1/m and X=(m+1)/2 with probability 1/m. Then E X=1 and E X²=(m+3)/4, so log E X²/log L→1/4. Yet (log X−E log X)/sqrt(log L)→0 in probability, and its variance divided by log L tends to zero. Multiplying by exp(−exp(L)) makes X a correlation-sized variable in (0,1] without changing either the relative second moment or the centered logarithm. This is an exact countermodel to the **headline second-moment inference**, not a counterexample to Ising or to all IR proof-level estimates.

**Primary comparison and decision.** Dotsenko–Picco–Pujol `hep-th/9501017v1` uses a perturbative replica/RG computation for critical averaged correlations; Davis–Cardy `cond-mat/9911083v1` studies mixed spin/energy moments to one loop near Q=2, with an additional (2+ε)-dimensional Ising calculation. Neither is substituted for a fixed-strength planar probabilistic CLT. Their existence also prevents treating multifractal/lognormal heuristics as a new discovery. **Not selected:** the positive logarithmic representation is absent. Unlike I13, the issue is not merely a missing mixing rate, and unlike I17, the proposed novelty is a logarithmic disorder fluctuation law, not a joint extension of known marginals.

### C. Joint zero-interface and integer-height convergence — selected

**Exact target.** Let D be any bounded smooth simply connected planar domain, with distinct marked a,b. Let Dδ be simply connected triangular-cell approximations with uniformly convergent marked boundary parametrizations and marks at edge midpoints. Choose uniformly an odd integer height hδ with values +1 and −1 on the two boundary arcs and |hδ(u)−hδ(v)|∈{0,2} on each edge. Interpolate affinely. Let γδ be its unique boundary-to-boundary zero contour, oriented from a to b. Seek full-sequence joint convergence

\[
 (h_\delta,\gamma_\delta)
 \Rightarrow(\bar g+\sigma_h\Phi_D,\gamma),
 \qquad \sigma_h^2=8/\pi,
\]

in distributions times uniform curve distance modulo reparametrization, where γ is the canonical zero level line of the limiting field, is measurable from that field, and has chordal SLE₄ law. Here G_D=(−Δ_D)⁻¹, with singularity (2π)⁻¹log(1/|z−w|), and ḡ is the harmonic extension of ±1. The numerical normalization is part of this proposed target, not a consequence presently proved.

**Available contracts.** H2 `thm:main` already gives hδ⇒ḡ+σhΦD with σh>0, convergence of all mixed smooth-test moments, and tightness in distributions. `prop:tightness` strengthens this to local H⁻ᵗ for t>1. The theorem expressly excludes the interface assertion. Its normalization is an absolutely convergent finite-volume series, not the value 8/π. HW gives a zero-boundary field limit for every fixed x∈[1/√2,1], with σ(x) unspecified and no assertion of uniformity in x or loop convergence. At x=1 its loop representation supplies the zero-boundary component model below.

HR proves an SLE₄ interface limit for **real** uniform Lipschitz heights at a tuned boundary amplitude l, with l²=πσ²/8. Its proof supplies general harmonic-observable and analytic trace arguments, but its model-specific comparison inputs involve reflected diffusions on full-dimensional real polytopes. Counting integer points does not satisfy those hypotheses merely because its convex hull is that polytope. SV, including its finite-energy tests and explicit variance, concerns a square-lattice plane state obtained through prescribed balanced-torus limits; it is not a conditional law for the present triangular-lattice slit domain.

**Reason to continue.** A joint field–curve construction and the resulting normalization would resolve a geometric assertion explicitly left outside H2 and identify information not continuous in the distribution topology. This is not transfer of an SLE exponent from an existing curve theorem. The exact exploration below makes this route the strongest concrete attempt, but its asymptotic gap remains material.

## 3. First method: exact exploration and harmonic martingales

### 3.1 An oriented transcript pins values, not just signs

Work first in an arbitrary finite simply connected triangular cell complex with the stated two-arc boundary. No limit is used. On an edge crossed by the zero contour, oddness, opposite signs, and the bound 2 force the endpoint values to be exactly −1,+1. On entering a triangle across that edge, its third vertex is adjacent to both endpoints, so its value lies in

\[
 [-3,1]\cap[-1,3]\cap(2\mathbb Z+1)=\{-1,1\}.
\]

The third value determines the exit edge. Thus the exploration reveals only exact values ±1 at every newly queried vertex. Triangles contain either no zero segment or one segment, so there is one simple chordal component and possibly disjoint closed components. A prefix record includes the **exit edge in its last triangle**, not just a list of visited triangles. The finite checker initially exposed this distinction; a triangle-only prefix leaves its last turn undecided. The final implementation records the oriented edges and checks the resulting equivalence exactly.

For an admissible prefix transcript s, let Ps be the revealed vertices with their values, together with the original boundary. Then

\[
 \{\text{the exploration begins with }s\}
 =\{h|_{P_s}=b_s\}.
 \tag{3.1}
\]

One inclusion follows from the exploration rule. For the other, replay its deterministic edge-by-edge decisions; every decision depends only on the recorded values. No condition on an unseen closed contour is imposed. At a stopping rule measurable from the prefix, whether the rule has stopped is also already determined by the transcript. This observation matters: an arbitrary extra event involving unseen heights is not allowed.

Because the original law is uniform counting and interactions are nearest-neighbor hard constraints, conditioning on (3.1) leaves the uniform extension law. On deleting fixed vertices, free graph components have product conditional laws; edges from a component to Ps keep the actual pinned values. This is an exact finite Gibbs factorization, including components produced by near self-approaches of the path.

**Source comparison.** This proof is the odd-height specialisation of H2 `08-boundary.tex`, the proof of `lem:boundary-attachment`, especially its paragraph “The mean detects a side of the open contours.” That paragraph follows threshold k−1/2 paths, pins k−1,k, proves transcript/completion equivalence, and preserves unseen loops. We do not label it a newly discovered construction.

### 3.2 Complete-path factorization and an exact projection

Expose the complete chord γ. Its two oriented sides, together with the corresponding original boundary arcs, label the cut-open geometric cells by + or −. The source's deterministic consistency argument applies: an unseen closed contour cannot enclose part of the connected fixed skeleton or intersect an exposed open contour; erase closed contours only for the purpose of assigning side labels, without conditioning on that erasure. Each free primal component has all its adjacent fixed values equal to one sign sj∈{−1,1}. Components may split further when revealed lip vertices are removed; this does not change their boundary label.

On such a component Uj write h=sj+2Hj. Then Hj is an integer 1-Lipschitz height with zero fixed boundary, uniformly sampled. Reflection Hj↦−Hj preserves its conditional law. Therefore

\[
 \mathbb E[h(v)\mid\gamma]=s_\gamma(v)\in\{-1,1\}
 \tag{3.2}
\]

at every vertex, with the recorded sign used on pinned vertices. Conditional on γ, the fields Hj in distinct free components are independent. Let sγ,δ be the **affine interpolation of these vertex labels**. For every deterministic integrable f supported in Dδ,

\[
 \mathbb E[h_\delta(f)\mid\gamma_\delta]=s_{\gamma,\delta}(f),
 \qquad |s_{\gamma,\delta}(f)|\le\|f\|_1.
 \tag{3.3}
\]

This label field is not asserted to equal the discontinuous geometric side indicator inside path triangles. Proving that their difference is negligible in area would itself require control of the path ribbon. We keep the affine convention, making (3.3) exact without any length estimate.

For deterministic vertex weights f,g, splitting their linear statistics into the free components gives the exact identity

\[
 \operatorname{Cov}(h(f),h(g))
 =\operatorname{Cov}(s_\gamma(f),s_\gamma(g))
  +4\mathbb E\sum_j
       \operatorname{Cov}_{U_j,0}(H_j(f),H_j(g)).
 \tag{3.4}
\]

The analogous area-pairing identity follows by using the finite affine basis weights. There are no cross-component covariance terms, and fixed lip values contribute only to the first term. This is the concrete conditional-covariance object to be estimated; replacing it by a Green function is not part of the finite identity.

### 3.3 A bounded martingale and the precise first gap

Let Fδ,t be the prefix filtration, parametrized by any deterministic increasing exploration clock, and set Mδ,t(f)=E[hδ(f)|Fδ,t]. The tower property and (3.3) give

\[
 M_{\delta,t}(f)=\mathbb E[s_{\gamma,\delta}(f)\mid\mathcal F_{\delta,t}],
 \qquad |M_{\delta,t}(f)|\le\|f\|_1.
 \tag{3.5}
\]

Thus optional stopping is legitimate at every finite-mesh bounded stopping rule, and these martingales and their squares are uniformly integrable for each fixed f. No logarithmic point-height bound is needed for this assertion. At a genuine binary reveal let p be the conditional probability of the + branch and F+,F− the two continuation expectations. Then exactly

\[
 \Delta M=(\mathbf1_+-p)(F_+-F_-),\qquad
 \mathbb E[(\Delta M)^2\mid\mathcal F]=p(1-p)(F_+-F_-)^2.
 \tag{3.6}
\]

This supplies a well-defined bracket, but not its asymptotic relation to capacity time.

The required harmonic observable estimate is the following unresolved assertion **H**. For each deterministic smooth f in a fixed protected interior ball and each fixed clearance ρ>0,

\[
 \lim_{\delta\downarrow0}
 \sup_{T\in\mathcal T_{\delta,\rho}}
 \mathbb E\left|M_{\delta,T}(f)
      -\int f(z)m_{\delta,T}(z)\,dz\right|=0.
 \tag{H}
\]

Here T ranges over prefix stopping rules before the path reaches the ρ-neighborhood of the support; mδ,T is the continuum harmonic function in the physical slit component, with ±1 on its oriented lips and original boundary arcs. The analogous reverse-direction assertion is needed for whole-curve control. Lip values are prescribed at prime ends, so two sides of a thin slit remain distinct.

H2's ordinary smooth-domain mean convergence proves neither this supremum nor its random-domain version. Its actual boundary-arch theorem fixes positive macroscopic scales, a locally smooth limiting boundary, and a fixed finite family of small boundary replacements **before** the mesh limit. A typical stopped slit is not such a family. Its local smearing proposition *does* tolerate irregular boundaries and bounded data, so lack of moments is not the obstruction. The obstruction is identifying the harmonic mean with the correct trace, uniformly over the conditioned slits.

One constructive approach was to cut the slit into fixed polygonal windows and reuse H2's pin-motion, boundary brackets, and arch attachment. This works at the level of a fixed separated arrangement, but its constants and allowable mesh depend on that arrangement. Refining the windows along an adaptive slit produces an unbounded family of pin geometries and unresolved fjords; there is no established summable error or uniform trace estimate allowing the limits to be exchanged. A second possible repair would transfer HR's rough-boundary trace theorem. That theorem requires a W¹,ᵖ response extension, zero Frostman trace on observed sets, and a uniform weak flux equation. H2's reflection-null identity and smooth moment harmonicity do not supply these response estimates for the integer conditional law. Thus this repair has not been completed.

The finite harmonic-explorer shortcut is false even before taking a limit. Take the radius-one triangular hexagon, prescribe +1 at one boundary vertex and −1 at the other five. The sole interior height is uniformly ±1, so its mean is 0. The discrete harmonic extension at the center is −2/3. This rejects an exact discrete-harmonic identity, **not** asymptotic harmonicity or SLE₄. It also explains why boundedness of (3.5) alone does not identify its bracket or driver.

H2 plus (3.3) does prove the limited integrated passage identity

\[
 \mathbb E s_{\gamma,\delta}(f)\longrightarrow\int_D\bar g f
 \quad(f\in C_c^\infty(D)).
 \tag{3.7}
\]

This is a technical consequence of the available mean limit. It does not assert pointwise passage probabilities, curve tightness, conditional harmonicity at random times, or joint convergence. In particular the zero contour is not a continuous mapping on the distribution space.

## 4. Second method: conditional field laws and the local-set construction

This approach starts from the entire finite Gibbs kernel instead of trying to identify a driver from its first moment. For a transcript s, put

\[
 \chi_{\delta,s}(t;f)=
 \mathbb E_s\exp\{it(h_\delta(f)-\mathbb E_s h_\delta(f))\}.
\]

The kernel exists by (3.1). For a complete chord, (3.2) factorizes χ into the characteristic functions of independent zero-boundary component fields evaluated with weights 2tf. These factors are physical conditional laws, not annealed replacements. At prefixes the uncompleted component still has two-sided data; closed-off components have their actual fixed traces.

To pass this construction to the continuum, the missing assertion **C** is a sequentially uniform conditional Gaussian limit: for every fixed compact family of smooth tests protected from the transcript, every fixed bounded set of real t, and every admissible deterministic sequence of oriented transcripts sδ whose observed sets and marked slit components converge in an appropriate kernel topology,

\[
 \chi_{\delta,s_\delta}(t;f)
   \longrightarrow
 \exp\{-t^2\sigma_h^2\langle f,G_{D\setminus K}f\rangle/2\},
 \tag{C}
\]

jointly for finite test families. For application to random stopping rules, either prove this uniformly over a specified compact geometric class and prove that the explored slits lie in that class with high probability, or prove the directly averaged conditional error uniformly over stopping rules. Neither version is established here. The limiting means must also satisfy H. Calling C a reduction does not make the target an accepted finding.

**Attempt through component GFF limits.** HW gives a zero-boundary GFF limit in fixed C² domains. Conditional components Uj depend on γδ; their boundary may have arbitrarily narrow fjords and a number of segments growing with δ⁻¹. Substituting these components into a fixed-domain theorem has no justified uniformity. Sandwiching them by smooth domains does not repair this automatically: restricting an outside height sample to a smooth inner boundary gives random, unbounded height values, not the desired zero boundary law. Simple monotonicity in boundary values consequently does not identify the conditional covariance. The plane local comparison fixes local increment covariance in a disk separated from all pins, but leaves the boundary-dependent harmonic part of the Green kernel undetermined.

**Attempt through tilted responses.** In a finite conditional law, differentiating log E_s exp(t h(f)) is legitimate and its second derivative is the tilted variance. This suggests HR's response proof of C. Its `t:covariance` theorem explicitly requires three model-specific inputs, uniformly over deterministic sign strings: exponential moments, controlled filled response extensions with common-wall errors and trace anchors, and a common weak flux equation. HR proves these using real reflected dynamics. An integer heat-bath coupling would preserve counting measure and exact pins, but its difference is not the real source's composition of linear averaging projections. No comparison-energy estimate or stiffness identification for that new dynamics has been proved here. The analytic trace theorem remains available once its hypotheses are met; the missing work is not an upstream theorem audit.

For clarity, conditioning itself is a genuine limit issue. On an n-point probability space with uniform J, each deterministic coordinate error Xj=1{J=j} has E Xj=1/n, while the adaptively selected XJ equals one. Every variable is bounded. This countermodel does not refute C, but shows why deterministic fixed-test convergence and uniform integrability do not imply adaptive uniform convergence. Likewise, tightness of hδ and tightness of curves, even if separately obtained, would only give subsequential couplings; their correct conditional characteristic functions would still require proof.

The needed limiting order is: first fix the protected test disks, clearance, finite time horizon, and geometric tolerances; then take δ→0 with uniform errors at those fixed values; next remove geometric cutoffs with a proved probability bound; finally remove test and time discretizations. The source's mesh-first/window-second boundary proof cannot be silently diagonalized against the random slit.

## 5. What a completed bridge would determine, and what is still missing

The normalization provides a useful adversarial consistency check. Suppose, only for this calculation, that the joint conditional field property has been established in the half-plane and that its driver is Wt=√κ Bt. Put Zt(z)=gt(z)−Wt and

\[
 m_t(z)=1-\frac2\pi\arg Z_t(z),\qquad
 d\log Z_t=(2-\kappa/2)Z_t^{-2}\,dt-\sqrt\kappa Z_t^{-1}\,dB_t.
\]

Requiring all protected harmonic averages of mt to be martingales forces κ=4 in this proposed SLE family. This calculation alone does not prove that a discrete driver is a semimartingale or that its law is SLE. HR `h:driving` and Schramm–Sheffield supply the genuine approximate-martingale criterion once H and its geometric hypotheses are verified.

At κ=4 the cross variation of the mean is

\[
 d\langle m(z),m(w)\rangle_t
 =\frac{16}{\pi^2}\Im\frac1{Z_t(z)}\Im\frac1{Z_t(w)}\,dt.
\]

For our GFF convention,

\[
 -dG_{\mathbb H\setminus K_t}(z,w)
 =\frac2\pi\Im\frac1{Z_t(z)}\Im\frac1{Z_t(w)}\,dt.
\]

Conditional Gaussian covariance and total variance would equate these coefficients, giving σh²=8/π. The calculation uses smooth protected averages when taking expectations, not the undefined pointwise variance of a GFF. It agrees with HR `h:normalization` and Schramm–Sheffield's λ=√(π/8) for a unit GFF. Thus this normalization argument is available source machinery, not a new theorem. Deriving it from the actual integer kernels still requires H, C, and limit passage.

The target remains open in this record because all of the following material tasks remain:

1. Prove H for the actual integer prefix law, uniformly over protected stopping rules in both directions.
2. Prove the relevant conditional covariance or full characteristic-function assertion C, with the same bulk normalization and enough moment control to pass conditional second moments. H alone does not identify the joint field–curve law.
3. Establish curve/driver compactness with the required no-return, boundary-landing and tip-control estimates. A bounded martingale has no automatic modulus in capacity time. H2's loop estimates and smooth-arc arches are usable inputs, but no unproved identification with HR's real-height geometry estimates is made.
4. Show convergence of the actual filtrations/conditional kernels on a determining set, apply the continuum coupling characterization, and use its uniqueness to remove subsequences. If a canonical field-measurable interface is claimed, that measurability comes from the verified continuum characterization, not from a general rule that limits preserve measurability.

These are gaps in the attempted bridge, not a disproof of Schramm's integer-interface conjecture, a lower bound against all methods, or an assertion that the accepted corpus cannot imply the result by another argument.

## 6. Current primary literature and exact hypothesis comparison

The first literature search occurred before choosing the route. Six retained search batches record later focused queries; the first broad exploratory batch is not retained and is not part of the reproducible evidence. Search responses, including irrelevant hits, are discovery records rather than premises. Eleven primary works were retrieved as abstract pages and version-pinned PDFs; their exact bytes, retrieval times, headers, versions and extracted text are under [literature](../sources/i26_probability_discovery_resumed/literature/retrieval-manifest.json). [Version dates](../sources/i26_probability_discovery_resumed/literature-versions.json) come from the retrieved submission histories, not search-engine recency labels. The arXiv histories identify the latest versions displayed at retrieval; no exhaustive coverage of unpublished or unindexed work is claimed.

- **Schramm, math/0602151v2 (2006-02-10), Problems 2.2 and 2.3.** Problem 2.2 asks separately for the odd-integer interface and field limits; Problem 2.3 is the real-valued model with a tunable amplitude. This distinction matches the accepted H2/HR scope. [Primary text](https://arxiv.org/pdf/math/0602151v2).
- **Schramm–Sheffield, math/0605337v3 (2008-04-24), Theorem 1.1.** The model is the discrete Gaussian field. At its distinguished boundary amplitude the contour tends to SLE₄; larger amplitudes give SLE₄(ρ₁;ρ₂). Its Gaussian Markov conditional mean cannot be assumed for the integer hard-constraint model; the radius-one diagnostic explicitly distinguishes their finite observables. [Primary text](https://arxiv.org/pdf/math/0605337v3).
- **Schramm–Sheffield, 1008.2447v1 (2010-08-14), Theorems 1.2 and 1.3.** The continuum theorem identifies the level line and field measurability. Theorem 1.3 assumes the conditional field law in each Loewner complement is the specified harmonic function plus an independent zero-boundary GFF. It concludes λ=√(π/8), SLE₄, and uniqueness of the coupling. That hypothesis is precisely the missing model-specific bridge, not a consequence of a marginal GFF limit. [Primary text](https://arxiv.org/pdf/1008.2447v1).
- **Miller, 1010.1356v1 (2010-10-07), §1.1 and Theorem 1.1.** Assumptions include a real C² symmetric potential with 0<a≤V″≤A<∞ and Lipschitz V″. Neither an integer-valued law nor a potential which is flat inside a hard interval and infinite outside meets them. Taking a formal smooth-potential limit without uniform estimates is not an application. [Primary text](https://arxiv.org/pdf/1010.1356v1).
- **Glazman–Manolescu, 1810.05592v3 (2023-02-27), Theorem 1.1.** The uniform integer Lipschitz model has logarithmic variance bounds and a full-plane gradient limit; these do not identify a two-arc contour law. Its two-spin representation is already part of H2's machinery. [Primary text](https://arxiv.org/pdf/1810.05592v3).
- **Glazman–Lammers, 2306.01527v3 (2023-10-27; published 2025), §1.2.4 and Theorems 2–3.** The relevant results are logarithmic delocalisation/loop estimates; the inspected passage explicitly distinguishes these from GFF convergence. H2/HW are accepted stronger field inputs, but that does not add an interface conclusion to this primary work. [Primary text](https://arxiv.org/pdf/2306.01527v3).
- **Duminil-Copin–Kozlowski–Lammers–Manolescu, 2603.06268v1 (2026-03-06), Theorems 2.2 and 2.8.** The six-vertex model is on the square lattice, in its infinite-volume state, with a=b=1 and √3≤c≤2 for the stated GFF theorem. The explicit stiffness and negative-regularity convergence are substantial precedents. They do not identify conditional triangular integer-height fields in an adaptively exposed bounded slit. The accepted SV companion has a wider parameter range but retains the different plane-state contract. [Primary text](https://arxiv.org/pdf/2603.06268v1).
- **Vanneuville, 1906.12256v3 (2021-02-12), Theorems 1.1–1.3 and 1.7; Bhattacharjee–Peccati–Yogeshwaran, 2407.13502v1 (2024-07-18), Theorem 1.4.** The frozen and moving-geometric noise statements were compared in §2A. A sharp scale is not a complete universal path kernel. [Vanneuville](https://arxiv.org/pdf/1906.12256v3), [Poisson spectra](https://arxiv.org/pdf/2407.13502v1).
- **Dotsenko–Picco–Pujol, hep-th/9501017v1 (1995-01-07); Davis–Cardy, cond-mat/9911083v1 (1999-11-05).** The retrieved primary introductions and methods specify perturbative replica calculations, with the regime distinctions recorded in §2B. They are neither rigorous fixed-disorder log-CLT inputs nor evidence that the proposed statement is new. The generated date in the Davis–Cardy PDF differs from its arXiv submission date; the retained version is identified by the latter and its hash. [Dotsenko et al.](https://arxiv.org/pdf/hep-th/9501017v1), [Davis–Cardy](https://arxiv.org/pdf/cond-mat/9911083v1).

The strongest **internal** prior-art comparison is especially decisive: the exact integer exploration in §3 is already available inside H2, while the harmonic-observable, conditional-covariance, and normalization templates are explicit in HR and the continuum primary literature. What would be substantial is proving their missing integer, adaptively conditioned hypotheses. No such proof is disguised as an elementary corollary here.

## 7. Deterministic diagnostics, verifier, and handoff

The [diagnostic program](../experiments/i26_probability_discovery_resumed/diagnostics.py) exhaustively enumerates every odd-height extension of all ordered two-arc boundary assignments on radius-one and radius-two triangular hexagons. It uses integer arithmetic and exact rational expectations. The [retained output](../experiments/i26_probability_discovery_resumed/diagnostics.json) reports:

- 162 boundary experiments and 25,620 height configurations;
- 67,892 exact oriented-prefix/pinning equivalences;
- 9,612 complete-path component-product checks;
- 3,516 free-site terminal-mean identities and 1,286,708 bounded-martingale/tower identities;
- the explicit 0 versus −2/3 finite harmonic counterexample;
- six exact adaptive-coordinate countermodels, six relative-second-moment countermodels, and eight rational checks of the Itô normalization coefficients.

The component-product checks compare the number of complete joint configurations to the product of the numbers of distinct component projections. With uniform counting this verifies the asserted finite independence on those domains. These computations do not estimate continuum errors or prove H, C, an SLE limit, or an Ising CLT. General proofs of the finite identities are in §3; the checks are adversarial diagnostics, not replacements for them. The Itô checks verify coefficients after removing π factors; they do not simulate Brownian paths.

From the project root, reproduce the mathematical diagnostics with

```bash
python frontier/experiments/i26_probability_discovery_resumed/diagnostics.py
```

Regenerate only the exact statement/passages metadata with

```bash
python frontier/experiments/i26_probability_discovery_resumed/contracts.py
```

Run the read-only verifier with

```bash
python frontier/experiments/i26_probability_discovery_resumed/verify.py
```

The verifier checks the resumed artifact seal, every original-file hash, original snapshot identities, pinned Git/SHA identities against the frozen complete tree, exact contract/passages text, and primary retrieval hashes. Live shared-ledger changes are reported separately from immutable mathematical dependencies. The [verification receipt](../experiments/i26_probability_discovery_resumed/verification.json) is deliberately excluded from its own seal; the report, scripts, diagnostics, manifests, and retained evidence are sealed. The seal itself has a detached digest and does not claim impossible self-hashing. Network retrieval scripts record historical retrieval events and are not byte-reproducibility tests.

The handoff is a completed research screen with useful exact source-relative deductions and a sharply specified unproved geometric bridge. It is ready for parent provenance/diagnostic verification as a gap record. It is **not** a complete positive candidate for proof/significance acceptance, and the technical deductions do not advance the substantial-finding goal.
