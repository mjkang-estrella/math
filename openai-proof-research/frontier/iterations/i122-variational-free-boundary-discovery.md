# I122 — Original I119 audit and fresh variational/free-boundary discovery

2026-10-10. All source theorems **and lower proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. No upstream truth audit or ex-falso synthesis. No children, shared edits, staging, commits or publication. Only the three assigned I122 paths are owned. Active I120/I121 outputs are not dependencies.

**Original I119 verdict, before repairs: PASS without repairs at the stated scopes** for L119, F119, DEF, the sample-basis-flag counterexample, W119, SR, SC, BUD, PIV and EX. XI passes as an exact definition and explicit statement of an **unpaid** estimate, not as a bound. The complete weighted chain is independently checked below. The prior independent I116/I113 passes are preserved as inherited; this is not another full audit of those originals. General R113 remains parked, unproved and unrefuted.

**Fresh discovery: no substantial nomination.** Four exact screens lead to a Dini-coefficient sharp-packing target. Two developed routes give a frozen-ellipsoid radial-defect estimate with a conditional covariance bound, and an exact coordinate-change subclass with explicit obstructions to extending it. Current primary literature already contains the first route's local monotonicity mechanism. Sharp packing for the full target is not proved. Eight accepted findings remain eight; technical deductions and counterexamples do not fill either remaining slot.

## 1. Evidence, scope and chronology

The original I119 report is bound at SHA-256 `37ac921d7e30f6da188c65a6cbc0a6b3121cc0f4ba538f81a42289c8b7d38a8a`. The required recursive task record is bound at `417f8386d54303348d2bfa6747163f8ebf196cf8cefe640a9135eddb5eadf961`. Its **entire brief field**, including recursive originals, objections and responses, is extracted verbatim and read through its ending. The finalized parent receipt is frozen separately. `original-audit-verdicts.json` was written after the audit and before fresh discovery; no repaired claim substitutes for an original verdict.

AGENTS, the pin and four current ledgers were consulted. Frozen copies bind their input states; only the four live ledgers may drift. The complete inherited map has 13,223 tree entries, 749 manuscripts, 10,373 original positions (9,340 I14 originals plus 1,033 additional originals), and 776 inherited PDF-text representations. It is reused by reference, with no corpus recopy. The new exact lexical scan has 62 variational matching lines and zero matches for the narrower coefficient/packing expression. Expressions, ordered lines and every matched substring/offset are preserved. This is lexical evidence, not semantic coverage or a novelty proof.

Independent overlap checking found a qualification to the proposed fresh direction: I07 already explored constrained/inverse Ball–Evans approximation and its correction-cost obstruction. That alternative is therefore not fresh. No developed planar Mumford–Shah or Bernoulli packing branch was located in the ledger/catalogue screen. This statement does not assert exhaustive semantic absence across unrelated history.

Actual reading ranges, LF versus `splitlines` conventions, full source hashes, passage hashes without appended newlines, original-position URLs and extraction provenance are recorded in `read-manifest.json`. Complete relevant P sections, both marked-pivot sequences, the safety proof through its ending, and the common-generator telescope were read. The relevant companion proofs were read through their endings, not inferred from abstracts. For fresh discovery, the planar manuscript's full reduction, blow-up, interaction and completion proofs; the Bernoulli statement, history, reductions and consequences; the **entire** Edelen–Engelstein and current Deangelis papers; and the entire Sobral v2 paper were read. The variable-matrix companion was read through the complete coordinate-change Lemma 2.1; its subsequent Lipschitz proof is not claimed as read or used to grant Dini Lipschitz regularity. The pinned Bernoulli classification is an accepted premise: no fresh audit of its cone-certificate arithmetic is asserted.

Four relevant new PDFs were selectively extracted: Edelen–Engelstein v3, David–Engelstein–Smit Vega Garcia–Toro v2, Deangelis v2, and Sobral v2. Inherited PDF extractions were not repeated. Failed/truncated reads and the unavailable BeautifulSoup conversion are retained in the history. The latter was followed by a successful PDF extraction, not erased.

## 2. Original I119 audit — no repairs

The original probability model is unchanged: a known finite labelled rank-oracle matroid; exactly one independent sample S_e~Q_e and online value V_e~D_e per label; all 2n variables independent; nonnegative finite observations; D_e/K ≤ Q_e ≤ K D_e as measures, known K≥1 and finite expected OPT. Orders may depend on full data and seed. Worst-case polynomial rational bit/oracle cost is required when an implementation is asserted. Likelihood ratios in proofs are analysis variables, never supplied to the algorithm.

### L119 — PASS without repairs

For any finite nonempty downward-closed family, fix a single ordering of feasible sets for ties. Conditional on V_-e, the best containing-e weight is v+A and the best excluding-e weight is B. Their internal tie winners do not vary with v. Consequently g_e(v)=v 1_{e in I*(v,V_-e)} is nonnegative and nondecreasing, including the crossing point, zero and forbidden labels. The empty set supplies the excluding alternative. No oracle for arbitrary downward-closed optimization is asserted.

Two-sided domination gives F_Q(v)≥ψ(F_D(v)), where ψ(u)=max(u/K,1-K+Ku). Its crossing is K/(K+1), and its integral on [0,1] is 1/(K+1). For the generalized D-quantile G, F_D(G(u))≥u even at atoms. Both g_e(G(u)) and ψ(u) increase. Their covariance double-integral is nonnegative; truncate g and then apply monotone convergence. Independence of S_e from all V gives

E[g_e(V_e)1_{S_e≤V_e}|V_-e] ≥ E[g_e(V_e)|V_-e]/(K+1).

Deleting failing coordinates of I*(V) preserves feasibility. Summation proves L119 at its full scope. Every feasible singleton's mean is bounded by EOPT; upper domination gives its sample moment. Forbidden labels need no moment assumption. Empty ground sets, loops, rank zero, ties and atoms introduce no exception.

Sharpness is for this filter only. With one label, D uniform on [1,1+ε] and Q quantile-density 1/K below K/(K+1), K above, the density integrates to one and both measure inequalities hold. The reward ratio tends to ∫ψ=1/(K+1) as ε↓0. An unrestricted one-label online rule accepts V, so this is no online impossibility.

### F119, DEF and the flag example — PASS without repairs

Under the common positive support interval [a,αa] on feasible labels, the stated rule accepts positive passing labels whenever independence permits. Every rejected candidate remains spanned by the growing set. The final set is a maximal independent subset of the positive candidates, hence has their full rank for **every data vector and every order**. Its value is at least candidate OPT/α, giving 1/[α(K+1)] after L119. The algorithm need not know a or α. It makes at most n rank queries, uses polynomial storage and rational comparisons, and has no seed or loop of length K. Loops fail the rank test; zeros are rejected. This covers nonrepresentable oracle matroids and the full-data adversary.

For any independent A in the candidates C, weighted matroid greedy and layer cake give

OPT_C(V)-V(A)=∫_0^∞ [r(C∩{V≥x})-|A∩{V≥x}|] dx.

The integrand is nonnegative. Level endpoints do not affect the integral. With deterministic rank-one weights ε,1 and the smaller label first, Q=D and both pass: the rule earns ε. Thus DEF locates a genuine unpaid scale cost for that rule, not for all algorithms.

For the sample-basis flag, nested flats make at most one selection per rank-one layer feasible: any chosen label of layer i lies outside F_{i-1}, which contains all previous choices. The advertised rank-query construction is polynomial. In U_{r,r³}, r≥3, independent Bernoulli(1/r) samples and values satisfy K=1. The first r-1 layers are sample-basis singletons, independent of their online coordinates, and the final layer has capacity one. Any rule confined to these layers earns at most (r-1)/r+1<2. For N positive online values, EN=r², Var N≤r², so P(N<r)≤(r-1)^-2 and EOPT≥r[1-(r-1)^-2]. This is an actual unconditional instance, not a posterior artifact. It refutes the layer restriction; F119 works on the same family.

### W119 — PASS without repairs, including adaptive selection

Before exposing the focal product mask, fix a family of N≥1 residual sets. With independent inclusion probabilities 1-ω_e,

P(R⊂O)=∏_{e∈R}(1-ω_e)≤exp(-Σ_{e∈R}ω_e).

Union bounding and integrating P(Z>log N+x)≤e^-x gives EZ≤log N+1. A residual chosen after exposure is allowed because the maximum already ranges over the fixed family. This does not allow the family itself to depend on the focal mask. Endpoint rates follow by deleting forced coordinates or a limit; the application uses interior rates.

The source family is fixed conditional on W,H, parity and nonfocal Dmask/Cguard/T bits. One must not additionally condition on the focal listing outcome. The two complete marked-pivot sequences encode **all** such outcomes, with q=floor(n_i/κ) and

N_i≤S_q(n_i)^2 [4^(2q)S_(2q)(n_i)]²,
log N_i≤1000 n_i logκ/κ.

Conditional focal O=Dmask∪Cguard has independent memberships and complements ω_e=a/B_e, where a=3(1-t)/4 and B_e=a+(1-a)r_e. In the low-rank listed branch the actual residual belongs to this family; setting it empty elsewhere is legitimate adaptive selection. No selected-set independence or extreme lower bound on ω is inserted.

### SR/SC/BUD — PASS without repairs for the complete weighted chain

Fix W,H and then the full Dmask when applying safety. The density paths and per-label baseline are now fixed. The source query-once reverse exposure leaves independent heterogeneous guards on unqueried coordinates; transcript-conditioned hybrid exit is dominated when s≤c_-. The deterministic hybrid containment is separate from this probability comparison. The squared-exit proof, birth accounting and fair parity work per label; the same T across endpoint analyses is allowed by linearity. Multiply these valid inequalities by ω_e, which is already fixed by W,H, then sum.

The weighted baseline is at most |Dmask∩U_i|/κ: weights are ≤1, the source baseline hits fewer than |Dmask∩U_i|/κ members of the independent optimum slice Y, and the baseline is independent of the guard exposure. Averaging Dmask produces d_e=r_e/(4B_e). Thus

E[σ_i^ω|W,H]≥(η/4)Σ_{e∈Y_i}ω_e d_e -n_i/κ.

On the low-rank listed branch, safe labels spanned by the witnesses have weighted mass ≤ their unweighted count ≤κz_i. All remaining safe labels lie in the encoded residual. W119 costs 1000 n_i logκ/κ+1; n_i≥κ pays the final 1 by n_i/κ. On the high-rank branch σ_i^ω≤n_i<κz_i. On an unlisted branch the associated statistics vanish. These exhaustive branches give exactly

κ E[z_i|W,H] ≥ (η/4)Σ_{e∈Y_i}ω_e d_e -[(1000 logκ+2)/κ]n_i. (SR)

No weighted density optimizer has been substituted for the source's unweighted one.

For fixed W and fixed nonnegative v_e supported on I*(W), Bayes gives P(H_e=0,Dmask_e=1|W)=r_e/(8Z_e), Z_e=1-p+pr_e, p=1-a/2. Therefore

E[Σ_{e∈I*(W)\H}v_e ω_e1_{Dmask_e=1}|W]=Σ_e v_e a r_e/(8B_e Z_e). (SC)

The polynomial BZ/r is a convex combination of 1/r,1,r: its coefficients are a²/2, a(1-a/2)+a(1-a)/2, and (1-a)(1-a/2). They are nonnegative and sum to one. Since both r and 1/r are ≤K, SC is ≥aΣv_e/(8K). This is valid for the full optimum, before excluding small groups; a path-dependent coefficient cannot silently replace v_e.

The source common-generator telescope and all-order greedy comparison give Eλ_i≥sE(z_i-c_i). Combining with SR and the factor 1/2 for cumulative level conversion gives precisely

E min_π u(A_main) ≥ s/(2κ) { (η/4)EΣ_large b_iΣ_{Y_i}ω_e d_e -[(1000logκ+2)/κ]EΣ_large b_i n_i -κEΣ_large b_i c_i }. (BUD)

The large-group set depends on W,H, so this combination is taken after the valid conditional bounds. Neither the negative cardinality term nor c_i becomes weighted. Small-group losses and the maximum branch still require separate accounting. The test rate s≤t/[K(1-t)+t] and the division by κ remain. Thus the leading mass cancellation in SC is **not** a one-K payoff theorem.

### PIV and XI — PASS at their exact paid/unpaid boundary

Freeze the ordinary reverse input and condition on a complete predictable transcript. Surviving guards retain their product law; the departing coordinates J are the ones changed by the hybrid. For the decreasing exit event E, increase only δ_j=(t-c_j)_+ on J. This product law dominates the actual hybrid guard set. Its probability of E is a multiaffine polynomial of the rates, whose derivative in coordinate j is minus its pivotal probability. Integrating along q_j(z)=c_j+zδ_j gives

h_τ≥p_τ-∫_0^1Σ_{j∈J}δ_j P_{q(z),-j}(j pivotal for E) dz =p_τ-Δ_τ. (PIV)

The pre-step p_τ is constant on its input cylinder, not a new independent output. Multiplication by the actual ordinary-exit indicator and averaging gives the squared-hazard positive term minus E[1_exit Δ_τ]. The source transcript conditioning justifies this step; no ordinary/hybrid output independence is asserted.

XI is exactly the weighted sum of these latter losses over valid birth endpoints and sampled-optimum labels. Its definition is paid. A bound saying XI, baselines and small groups consume only a fixed fraction of ηa EOPT/(32K), **while** BUD's residual, path and rank costs incur no further K, is unpaid. A coordinatewise Σδ_j union bound has no required rank/welfare budget. Original I119 explicitly says so. No tuning of this parked bridge is undertaken here.

### EX — PASS without repairs, only the stated invariant obstruction

Condition on distinct unordered endpoints, with θ=P(sample high)=r(high)/(r(low)+r(high)). The actual two-atom laws attain odds K². For a processed exchange, state-0 mass is 1-θ, its accepted incumbent has conditional probability β and cannot be displaced. A rejected state-0 incumbent flips with probability A; state 1 flips with B. Marginal preservation requires (1-θ)(1-β)A=θB. Requiring acceptance probability β for the new processed basis member in state 1 requires B=β; hence A=θβ/[(1-θ)(1-β)]. Feasibility A≤1 for all permitted θ implies β≤1/(1+K²). This concerns a fixed-thinning, marginal-preserving invariant. Nonstationary/weighted invariants are not excluded. Even a fixed-prefix repair would not establish a full-data/full-seed simultaneous-order guarantee.

### Full-source-operation technical disposition

P's actual chain is density residual counting, common path generators, heterogeneous predictable disjoint certificates, deterministic hybrid containment, two marked-pivot encodings, rank transfer, one common-generator telescope, simultaneous all-order rank, and geometric cumulative welfare. SR uses the same chain with weights added after the per-label argument; SC is Bayes algebra; W119 is the same finite-family union-bound operation with a weighted exponent. PIV is finite-product differentiation, EX local mass balance. L119 is a sharper scalar CDF envelope in the same quantile association/deletion proof; F119 adds full rank of maximal independent sets and a bounded-spread comparison. No new general online mechanism results.

The I22/IFF operation implements the largest density optimizer with cardinality-perturbed integer SFM; no enumeration of flats or residual families is executed. ABHM's complete refresh proof uses fair orientations and a fixed prefix; EX tests precisely its biased replacement. FSZ's complete chain and thinning proof require product activations plus the appropriate rank-polytope budget, which the censored/sample-dependent candidates do not supply. Fu's Appendix C is a CRS balance obstruction, not a universal welfare lower bound. Dütting–Kesselheim's proofs give fixed-recursion/additive-error or full-vector TV-coupling controls, not a dimension-free unknown-prior multiplicative guarantee against the new adversary. These full operations confirm **technical** status. The inherited I116/I113 passes are not enlarged into new audits or all-algorithms impossibilities.

## 3. Four exact fresh screens and primary-literature comparison

**Screen A: sharp interior singular packing in the standard one-phase problem.** For nonnegative local absolute minimizers of ∫(|∇u|²+Q²1_{u>0}) in B_4, Q positive C^α, bounded coefficient norm and a local Lipschitz normalization, ask |N_r(Sing u∩B_1)|≤Cr^7 and H^{n-7}/rectifiability bounds for n≥7. This is technical after the accepted d*=7 classification: Edelen–Engelstein, *Quantitative stratification for some free-boundary problems*, [arXiv:1702.04325v3](https://arxiv.org/abs/1702.04325v3), already prove the sharp effective-stratum packing/rectifiability machinery and singular-set consequences in terms of the critical dimension. Their Theorem 1.15 also covers specified power-gauge almost-minimizers and related two-phase/vector problems. Replacing d* by 7 or lifting a cone by a product is not a substantial target.

The full lower proof matters: Weiss defect control feeds compactness and cone splitting; the covariance eigenvalue estimate controls L² beta numbers; a centered-density-drop packing lemma uses discrete Reifenberg; alternating good and bad trees control overlap; finitely many density drops close packing. Rectifiability is a further local small-drop argument. A bare Hausdorff dimension bound is not doing this work.

**Screen B: polynomial complexity of planar Mumford–Shah graphs.** For reduced absolute compact-change minimizers in B_2⊂R² of ∫_{B_2\K}(|∇u|²+|u-g|²)+H¹(K), with ||u||∞+||g||∞≤M and energy≤E, ask for universal exponents a,b and C such that the number of endpoints plus triple junctions in B_1 is ≤C(1+E)^a(1+M)^b. This is an exact stronger quantitative target, not proved here. The pinned completion and current [Deangelis v2, 5 October 2026](https://arxiv.org/abs/2609.26732v2) give locally finite C¹ graphs, not such polynomial constants. The latter's complete new lower argument optimizes the second variation over outer corrections, sums two perpendicular translation inequalities, forces equality in planar Hodge projections, and uses regular-arc Cauchy data plus harmonic separation to exclude a compact component. The pinned manuscript instead uses the scalar harmonic interaction of translated compact pieces. Neither proof as read pays a quantitative isolation scale. Standard compactness might give a nonexplicit uniform modulus in a properly normalized class; that would not prove this polynomial statement. This screen was not selected for a forced nomination.

**Screen C, selected: sharp packing for Dini matrix coefficients.** Fix n≥8, 0<λ≤1≤Λ, L<∞, and a specified nondecreasing modulus ω on [0,1] with ω(0)=0 and ∫_0^1ω(t)dt/t<∞. On B_4⊂R^n let A=A^T, λI≤A≤ΛI, λ≤q≤Λ, and ||A(x)-A(y)||+|q(x)-q(y)|≤ω(|x-y|) for |x-y|≤1. Let u≥0 be L-Lipschitz and an **absolute local minimizer**: for every O compactly contained in B_4 and every nonnegative v with v-u∈H¹_0(O),

J_{A,q}(u;O)≤J_{A,q}(v;O),  J_{A,q}(v;O)=∫_O[∇v^T A(x)∇v+q(x)²1_{v>0}].

There is no boundary conclusion and no almost-minimizer gauge. Let S be the free-boundary points where the free boundary is not locally a C¹ hypersurface with the positive phase on one side. The target is

|N_r(S∩B_1)|≤C(n,λ,Λ,L,ω) r^7, 0<r<1/10,

with finite H^{n-7} bound and countable (n-7)-rectifiability as a possible stronger completion. The constant may depend on the **entire specified modulus**, not merely its Dini integral. These conclusions are **unproved here**. Normalizing at a center uses ellipsoids of radius below 1/(20√Λ), wholly inside B_4. This is genuinely outside the Hölder/power-gauge interfaces read, but that fact alone does not establish novelty or substantiality.

David–Engelstein–Smit Vega Garcia–Toro, [arXiv:1909.05043v2](https://arxiv.org/abs/1909.05043v2), formulate Hölder matrix coefficients and prove Lipschitz regularity for their almost-minimizers. Their full coordinate-change lemma explains the frozen ellipsoid. I assume L in the target rather than extrapolate their regularity theorem to Dini coefficients. Crucially, a current search located Sobral, [*On a Weiss-type Almost Monotonicity Formula*, arXiv:2604.12712v2](https://arxiv.org/abs/2604.12712v2). Its complete §5.1 already treats Dini A and phase weight with a growth hypothesis, using the same homogeneous comparison and coefficient error. Thus the local calculation below is **not a new mechanism or nomination**. Its full §4 concerns Alt–Phillips rather than the requested sharp Bernoulli singular packing; its §5 does not supply the complete covariance/packing tree at the proposed matrix-Dini scope. I do not audit or broaden its statements, and do not use its remarks to infer a missing Dini Lipschitz or flatness theorem.

**Screen D: constrained Ball–Evans approximation.** On the cube in R³, p>3, ask whether an orientation-preserving W^{1,p} homeomorphism with det Du=1 a.e. and a fixed smooth compatible boundary trace has smooth diffeomorphic approximants with exactly the same trace and determinant one, strongly in W^{1,p}. This meaningful invariant-preserving formulation cannot be inferred from unconstrained approximation. It overlaps the I07 investigation and its unpaid distortion cost for a Jacobian correction. Rejected as the fresh direction before proposing a theorem; no claim to a new complete reading/audit of the long unconstrained manuscripts is made.

Named significance evidence is concrete: the planar source and Deangelis identify the Mumford–Shah conjecture; the Bernoulli source identifies the critical-dimension question; Edelen–Engelstein identify sharp quantitative stratification, Minkowski estimates and rectifiability as their subject. No numerical ranking, worldwide priority, human-validation or formal-proof claim is made.

## 4. Route I: frozen ellipsoids, radial defect and the exact packing debt

### A paid local calculation, already present in the companion mechanism

Use Screen C's class, or the same class with continuous ω for a finite annulus. Fix x₀∈∂{u>0}∩B_2. Put T=A(x₀)^{1/2}, q₀=q(x₀), v(y)=u(x₀+Ty)/q₀. Then v(0)=0, Lip v≤√Λ L/λ and the exact transformed energy has the common positive factor det(T)q₀² and coefficients

Ã(y)=T^{-1}A(x₀+Ty)T^{-1},  Q̃(y)=q(x₀+Ty)/q₀.

Thus Ã(0)=I, Q̃(0)=1 and on B_r, ||Ã-I||+|Q̃²-1|≤C(λ,Λ)ω(√Λr). Local minimality is preserved for every Sobolev competitor by the linear change of variables. This does not require differentiating A.

Write E(r)=∫_{B_r}(|∇v|²+1_{v>0}), H(r)=∫_{∂B_r}v², W(r)=r^{-n}E(r)-r^{-n-1}H(r). For almost every r use the cone competitor z_r(sθ)=(s/r)v(rθ). It is nonnegative, has the same trace and satisfies ∫|∇z_r|²≤C(n)Lip(v)²r^n. Minimality and the two coefficient comparisons give

E(r)≤E_0(z_r;B_r)+C₀ω(√Λr)r^n,

where C₀ depends only on n,λ,Λ and 1+L². The exact cone identity is

E_0(z_r;B_r)=(r/n)∫_{∂B_r}(|∇_τv|²+v²/r²+1_{v>0}).

Coarea and H'(r)=(n-1)H(r)/r+2∫v∂_rv imply the exact identity

W'(r)=n r^{-n-1}[E_0(z_r;B_r)-E(r)]+r^{-n}∫_{∂B_r}(∂_rv-v/r)².

Consequently, after increasing C₀,

W'(r)≥r^{-n}∫_{∂B_r}(∂_rv-v/r)²-C₀ω(√Λr)/r. (WE)

All derivatives are a.e.; W is absolutely continuous on compact subintervals of positive radii. Let Ω(r)=∫_0^rω(√Λt)dt/t. Dini continuity makes Φ(r)=W(r)+C₀Ω(r) finite and nondecreasing. Integrating (WE) gives

∫_{B_R\B_s}|v-y·∇v|²/|y|^{n+2} dy≤Φ(R)-Φ(s). (RD)

This proof pays the radial-defect term, not just existence of a Weiss limit. Lipschitz normalization bounds W above and below; Dini correction gives a finite limit. Blow-up homogeneity additionally uses convergence of the relevant energies, not solely convergence of values. No power rate is inferred.

The operation is precisely Sobral's coefficient-freezing/homogeneous-extension proof, with explicit ellipsoid/amplitude normalization and a Lipschitz assumption ensuring both competitor and solution energy bounds. Numerical exponents printed in extracted PDFs are not substituted for the independently differentiated formula above. This is an author-level technical deduction, not a source repair or new monotonicity claim.

### Why the correction must be charged by annuli

For fixed 0<a<b, a dyadic family of annuli (a2^{-j},b2^{-j}) overlaps a bounded number of times. Hence

Σ_j[Ω(b2^{-j})-Ω(a2^{-j})]≤C(a,b)Ω(b).

Charging Ω(b2^{-j}) anew at every scale is invalid under ordinary Dini continuity. For ω(r)=1/[log(e/r)]², Ω(r)=1/log(e/r), so Σ_jΩ(2^{-j}) diverges, whereas the annular increments are summable. This calculation identifies an actual bookkeeping requirement for a Dini adaptation of the packing proof; it does not itself close the tree.

### A conditional covariance bridge with a complete algebraic proof

Let μ be a finite positive measure supported in B_r(x), with mass m>0 and barycenter X. Let its unnormalized covariance matrix be M=∫(y-X)⊗(y-X)dμ, with decreasing eigenvalues λ_i and orthonormal eigenvectors e_i. Define

β^k_μ(x,r)²=r^{-k-2}Σ_{i>k}λ_i.

For a.e. z, put f_y(z)=u(z)-(z-y)·∇u(z). Since ∫(y-X)dμ=0,

∫[(y-X)·e_i] f_y(z)dμ(y)=λ_i e_i·∇u(z).

Cauchy–Schwarz yields λ_i|e_i·∇u(z)|²≤∫|f_y(z)|²dμ(y), with the zero-eigenvalue case automatic. Suppose, as an **additional explicit hypothesis**, that on a common annulus A=B_{4r}(x)\B_{3r}(x),

∫_A Σ_{i=1}^{k+1}|e_i·∇u|² dz≥c r^n. (ND)

Sum the preceding inequalities and integrate to get

λ_{k+1} c r^n≤(k+1)∫dμ(y)∫_A|f_y(z)|²dz.

For y∈B_r(x), A lies in an ellipsoidal annulus centered at y with normalized radii ar,br, where a=2/√Λ and b=5/√λ. The radial scalar u(z)-(z-y)·∇u is affine invariant; changing to the normalized coordinates at y and using (RD) bounds the last inner integral by C r^{n+2}[Φ_y(br)-Φ_y(ar)]. Assume these ellipsoids lie inside the domain and μ is supported at free-boundary centers. Since Σ_{i>k}λ_i≤(n-k)λ_{k+1},

β^k_μ(x,r)²≤C(n,λ,Λ,L,c)r^{-k}∫[Φ_y(br)-Φ_y(ar)]dμ(y). (CB)

This pays the covariance calculation even when center metrics differ; it needs no derivative of A and no unjustified identification of the different ellipsoids. **ND is not proved uniformly for the desired singular set.** In the source proof a quantitative nonsymmetry condition, compactness and strong gradient convergence pay that hypothesis. Here it is displayed rather than smuggled into the conclusion.

### What remains unpaid

To deduce the target one must establish, for this precise Dini class, a uniform effective-stratum inclusion of the geometric singular set, including the flat-implies-C¹ theorem, phase/energy compactness and the quantitative nondegeneracy needed for ND. Then one must implement the full center-changing good/bad-tree packing argument with the corrected Φ and pay only annular coefficient increments. Its constants must be uniform below a radius chosen from the entire modulus. The finite macro-scale cover and the discrete Reifenberg summation must both be quantified. Neither RD nor conditional CB supplies those facts.

A Hausdorff dimension reduction, or compactness saying a bad scale eventually disappears, cannot be substituted for this complete summation. I have not completed it. No estimate |N_r(S)|≤Cr^7, power decay of flatness, or rectifiability theorem is claimed for Screen C.

One attempted shortcut was to compare each solution strongly with a frozen minimizer using only its small energy excess. Nonconvex phase energies need an additional selection/stability argument. On (-R,R), boundary trace h=R/2, the constant h has J=2R. The function (|x|-(R-h))_+ has J=4h=2R and squared gradient distance R from the constant. Both minimize: an everywhere-positive competitor has phase cost 2R, while a competitor vanishing somewhere costs at least 2h on each side by ∫(v'²+1)≥2∫|v'|. Thus zero energy gap alone gives no strong-distance estimate to an arbitrarily chosen minimizer. This is a one-dimensional method counterexample, not a counterexample to the selected high-dimensional target.

## 5. Route II: exact coordinate transport and its limitations

### The entire compatible subclass is paid

Let F:Ω→Ω' be an orientation-preserving C¹ bi-Lipschitz diffeomorphism, J_F=det DF>0, and let U≥0 be an absolute local minimizer of J_1 on Ω'. Set

u=U∘F,  A_F=J_F DF^{-1}DF^{-T},  q_F²=J_F.

The Sobolev chain rule and change of variables give, for every O compactly contained in Ω,

J_{A_F,q_F}(u;O)=J_1(U;F(O)).

Composition is a bijection on the corresponding H¹ competitors with fixed trace. Hence u is a local absolute minimizer. The converse follows by F^{-1}. No sample or numerical evidence is involved. The energy identity also holds for a bi-Lipschitz map smooth off a null set, using the a.e. derivative and area formula.

For C¹ F, geometric C¹ regularity and its failure are carried exactly by F. If S'=Sing U, S=F^{-1}(S'), and F has Lipschitz constant L_F while F^{-1} has L_I, then for interior sets with sufficient margin,

|N_r(S∩K)|≤L_I^n |N_{L_Fr}(S'∩F(K))|.

The source sharp-packing estimate therefore gives ≤C L_I^n L_F^7 r^7 on this subclass, after a finite interior cover in Ω'. Rectifiability passes through the bi-Lipschitz map; H^{n-7} gains at most L_I^{n-7}. The constant also records the source normalization and the finite-cover margin. No C¹,α regularity of F is needed for this transport statement; to belong to Screen C its induced A,q must additionally have that specified modulus. This is a fully proved technical composition of change of variables and accepted packing, not a new substantial theorem.

### General coefficients cannot be flattened this way

To realize prescribed A,q by this exact transport, one needs DF^T DF=q²A^{-1} and det DF=q². Thus det A=(q²)^{n-2} is necessary. For n≥3, A=I and nonconstant q already violate it. Even determinant compatibility does not suffice. With q=1 and

g=q²A^{-1}=diag(e^{2x₁},e^{-2x₁},1,…,1),

det A=1 but g is not flat: substituting t=e^{x₁} gives dt²+t^{-2}dx₂² in the first two coordinates, with Gaussian sectional curvature -2/t². A smooth pullback of the Euclidean metric has zero curvature. This rules out the proposed flattening for that smooth uniformly elliptic local example. It obstructs this route, not sharp packing itself.

### An exact non-Dini test with rotating flat blow-ups

This construction tests how far coefficient continuity can be weakened; it is not a refutation of the Dini target. In any n≥2, let J generate rotations in the (x₁,x_n)-plane and R_θ=exp(θJ). On B_1 set, for r=|x|>0,

t(r)=log(e/r), θ(r)=log t(r), b(r)=rθ'(r)=-1/t(r), F(x)=R_{θ(r)}x, F(0)=0.

F preserves radius and is a homeomorphism with inverse R_{-θ(|y|)}y. For e=x/r,

DF=R_θ(I+b Je⊗e), det DF=1, (I+b Je⊗e)^{-1}=I-b Je⊗e,

because e·Je=0. Both derivative norms are ≤2, so F and its inverse are 2-Lipschitz, including across 0 by continuity and integration on segments. Define q=1 and

A=DF^{-1}DF^{-T}=I-b(Je⊗e+e⊗Je)+b² Je⊗Je.

Then 1/4 I≤A≤4I, A extends continuously as I at 0, and A is smooth off 0. Its modulus is at most C/log(e/ρ). To see this uniformly, if the smaller radius is ≤√ρ and the two points are at distance ≤ρ, both matrix deviations from I are O(1/log(e/ρ)). Otherwise the connecting segment stays outside a fixed multiple of √ρ and |∇A|≤C/[r log(e/r)] gives an O(√ρ) difference. Along a unit direction with |Je|=1, the off-diagonal part is of order 1/t; thus no Dini modulus is possible. A square-Dini modulus is possible because ∫_0 ω(ρ)²dρ/ρ<∞.

The half-space U(y)=(y_n)_+ is a local absolute J_1 minimizer. For nonnegative competitors, |∇w|²+1_{w>0}≥2∂_n w a.e.; equality holds for U and integration of a compactly supported difference's derivative is zero. This calibration proves minimality. Exact transport makes u=U∘F an L≤2 local absolute J_{A,1} minimizer, including domains containing 0.

For every fixed x≠0, θ(r|x|)-θ(r)→0 as r↓0. Uniform compact convergence follows by first excluding a small ball about x=0 and then using the common Lipschitz bound there. Along sequences with θ(r)→θ_* modulo 2π,

u(rx)/r → (R_{θ_*}x)_n,+.

Different sequences give different half-space normals, since θ(r) is unbounded and continuous. The free boundary at 0 has no unique tangent and is not C¹. All its blow-ups are flat. This distinguishes the geometric singular set from “no flat blow-up” below Dini regularity, even in the plane; it does not disprove packing for a nonflat-blow-up stratum. In this twist family, Dini control of b forces ∫|θ'(r)|dr<∞ and rules out this unlimited rotation. The example is an explicit technical coefficient/coordinate construction; no priority or all-coefficient impossibility claim is attached.

## 6. Disposition and validation

Original I119 claims pass without repair, including the complete weighted safety/residual/rank chain at its paid scope. XI and the final one-K payoff remain unpaid exactly as originally stated. R113 is not resumed.

For discovery, the strongest selected statement remains unresolved. The deepest retained bridge is (RD) together with the conditional estimate (CB) and the annular Dini accounting, with their hypotheses fully exposed. Sobral already supplies the local monotonicity operation; Edelen–Engelstein supply the constant/Hölder sharp-packing mechanism; the missing work is the complete uniform geometric and multi-scale passage for general matrix-Dini coefficients. Route II completely handles only an integrable coordinate-change subclass and supplies concrete tests showing why generic flattening and mere continuity do not close the gap. No substantial finding is nominated.

`diagnostics.py` uses exact rational/integer arithmetic for selected cone-derivative identities, shear determinant/inverse and ellipticity checks, covariance inequalities, equal-energy phase competitors, and Dini-tail bookkeeping. It also replays the inherited I119/I116/I113 finite suites. Finite cases certify neither the universal proofs above nor novelty. Reading memberships and hashes certify identities, not theorem truth.

The verifier checks the exact owned inventory and all bound immutable artifacts before executing diagnostic code. It reuses the flat I113 corpus replay once, through the hash-bound I119 evidence core; it does not invoke I116's recursive core. It postpones **all** inherited diagnostic execution until all inherited corpus/reference/passage checks have completed, then runs them and the new suite. Four live ledgers alone may drift. Verification is offline and read-only, with no subprocess, network, bytecode, extraction, writes, repair or resealing. The final seal is an inventory envelope, not a self-hash or signature.

Run from the repository:

`PYTHONDONTWRITEBYTECODE=1 python3 -B frontier/experiments/i122_variational_free_boundary_discovery/verify.py`

The validation history preserves development failures and the preseal replay. The seal is generated once after successful preseal validation and final report completion. See the machine-readable preseal result for exact counts; the subsequent sealed replay must pass unchanged. This evidence handoff does not convert the unresolved discovery target into a theorem or increment the accepted count.
