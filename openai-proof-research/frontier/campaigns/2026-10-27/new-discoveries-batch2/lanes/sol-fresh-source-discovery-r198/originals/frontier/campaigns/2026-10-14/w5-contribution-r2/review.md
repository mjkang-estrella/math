# W5 independent contribution review, recovery round 2

**Verdict: TECHNICAL.** The complete frozen W5 conjunction is preserved. Its independent full-proof PASS is a separate gate and remains intact. I found no operative historical exclusion or primary theorem containing the whole conjunction, so I do not classify it INELIGIBLE or SUBSUMED. The added bounded embedding follows by a canonical scalar-projection construction and classical finite generation with its norm control made explicit below. That positive reduction, rather than the length of the proof or absence of a search hit, determines this verdict. No acceptance count or public action is authorized by this report.

Myeongjin Kang, no affiliation. Original review prose: CC BY 4.0. Original verification code: MIT. Third-party texts remain private. Reviewer: the native `/root/structural_discovery_r19` worker, which authored TS132 and earlier unrelated manuscripts/reviews, but no W5 author or proof artifact. This is a contribution assessment, not another full proof audit or an upstream truth audit.

## Exact scope and authenticated inputs

The same nonempty contractible domain M⊂C³ has a smooth geodesically complete Kähler metric g and finite 0<A≤B with −B≤K_g≤−A on **every real tangent two-plane**; admits a bounded holomorphic embedding into C⁵; and every bounded holomorphic G:M→C³ has **some point** where det dG=0. Embedding includes injectivity, immersion and the subspace topology. The last clause does not say det dG is identically zero. No properness, C⁴ obstruction, optimal target dimension, or general theorem for all negatively pinched manifolds is assessed.

Reviewed author directory: `fresh-analytic-discovery-r25`.

- Manifest: `10665dc832a51bca7651cbb091951b8b3ae3a7442339a64fd3b69e4b9743c606`.
- Original scope: `bda045b928a2f5b4ea52b96eb1ae6f3ea17146a575cefd955461994399d19f03`.
- Candidate: `2fd9649ae04c531eca486848917cbc3dc7ddfffdac9881ff1742594d2060147d`.
- Separate proof-review manifest: `737694d87ffd5c65ca7c9efe5ea2f54c0f6daf8a0168abbbc6875d624863b552`.

The author verifier was read and independently run with its supplied external anchor. It authenticates 69 payloads, 11 captured context inputs, 35 pinned source blobs and five retained primary files. The stipulated source revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; this review does not question its theorem truth. See `input-hashes.json` for exact local dependencies and `reading-and-comparison.md` for actual reading limits.

The previous Claude worker terminated with the documented rate-limit failure. Its directory contains an unfinished `review.md` with a TECHNICAL heading and a finite coefficient checker, but no completed authenticated verdict. I read those partial files after reading the candidate, source interfaces and DLS proof, and preserve them unchanged. Their asserted reading extent is not mine. Their proposed Hörmander boundary-loss calculation and informal infinite-tensor/Blaschke analogies are not premises of this verdict. No partial text is silently promoted into a prior accepted gate.

## What the source already supplies

The actual source Introduction and Section 2 state both the real-sectional geometry and C³ obstruction. Section 6 permits every sufficiently large **finite** amplitude L, so choosing an integer L before choosing the metric parameter is within the source construction. Its controlled potential is

    φ = ψ + L Σ U_j,     ψ = −log(1−|z|²),
    U_j = log((|1−aP_j|²+ε²)/(1+ε²)),

on B², with a,ε>0, P_j=P_(Q^j), P_j(0)=0 and |P_j(z)|≤C|z|^(Q^j). The source proves local smooth convergence and the required global chart control. It supplies M={e^φ|w|²<1}, contractibility, the metric and the Jacobian obstruction. The one-sided Liouville companion has different hypotheses and a different manifold; it supplies no extra bounded coordinates here.

The extra claim is meaningful: the source's statement about two bounded base coordinates does not itself give separation of fibers or a bounded finite-dimensional embedding. General Stein embedding theorems do not supply boundedness. Nevertheless the *explicit weight*, not only the source headline, already has an elementary norm structure that pays this interface.

## Concrete reduction of the residual operation

This comparison stays on the identical source potential, source manifold and full target. It does not repair or replace the frozen candidate. It exhibits why the operation required by that target is routine once the stated source factors are available.

Put V_j=(1−aP_j,ε)/sqrt(1+ε²), e=(1,ε)/sqrt(1+ε²), c₀=a/(1+ε²), and b_j=1−c₀P_j. Then ||V_j||²=e^(U_j), e is a unit vector, and the scalar projection of V_j onto e is b_j. The other available unit-coordinate projection is the **constant** δ=ε/sqrt(1+ε²)>0. These are two separate unit linear functionals, not an orthonormal coordinate decomposition; an orthogonal companion to e would give a multiple of P_j instead. Consequently

    |b_j|² ≤ e^(U_j),       δ² ≤ e^(U_j).

The zero-loss coefficient is thus projection onto the normalized vector at the origin. It is not an independent weighted-estimate theorem. The author's exact coefficient identity is the corresponding completed square; its quadratic perturbation cost and the convergence of ∏(1+const·|c_j−c₀|²) explain the candidate's ℓ² choice.

More decisively, the moving-parameter family and the quadratic perturbation budget are not needed to obtain the same basepoint-free weighted interface. For **every finite** subset S⊂N define

    q_S(z) = δ^|S| ∏_(j∉S) b_j(z).

Local normal convergence follows immediately from the source bound Σ_j |P_j(z)|<∞ locally uniformly. For N≥max S, multiply the preceding per-factor inequalities, using δ at indices in S. Passing to the limit gives the exact global estimate

    |q_S(z)|² ≤ exp(Σ_j U_j(z))                          (1)

with constant one, uniformly over all finite S and the entire base. This comparison does not omit the normalized factors at the changed indices; their second coordinates are precisely δ.

For each fixed z, b_j(z)→1, so only finitely many factors vanish. Put all those indices in S. All other factors are nonzero and their deviations from one are absolutely summable, so their infinite product is nonzero. Thus some q_S(z)≠0. The countable family {q_S} is basepoint-free. This uses finite changes of tensor coordinates and the source's own convergence estimate, rather than an additional global analytic construction. It handles points near the boundary without any boundary-dependent constant.

Raise to the same positive integer L: h_S=q_S^L. From (1), |h_S|≤E, where E=exp((φ−ψ)/2). Enumerate the finite subsets and, for c∈ℓ¹, set h_c=Σ_S c_S h_S. The series is locally uniformly convergent, hence holomorphic, and

    |h_c(z)| ≤ ||c||₁ E(z).                              (2)

Each evaluation c↦h_c(z) is continuous and nonzero. Its zero hyperplane is therefore closed with empty interior in the complete space ℓ¹. One may rescale any selected coefficient vector to have norm at most one, without changing its zero set.

Take h₁=h_empty, which is not identically zero since h_empty(0)=1. Its analytic zero set in B² has countably many irreducible components of dimension at most one. Choose one point on each component. Baire in ℓ¹ gives h₂ nonzero at all those selected points. Hence {h₁=h₂=0} is a zero-dimensional analytic set and is discrete and countable. A second Baire choice gives h₃ nonzero at every point of that set. Empty zero sets cause no problem. These three globally weighted functions have no common zero. This is the classical component-avoidance proof of finite generation, with norm preservation supplied explicitly by (2), rather than falsely inferred from Cartan B.

Finally (z₁,z₂,wh₁,wh₂,wh₃) has bounded image because |w h_l|²≤e^(−ψ)=1−|z|² after the harmless norm rescalings. The two base coordinates and a nonzero h_l give point separation, injective differential and the local inverse w=Y_l/h_l(Z). This is the ordinary fiber-coefficient construction. It changes neither M nor its inherited metric or C³ obstruction.

This reduction covers the complete conjunction. It does not merely produce one weighted function, a local cover, or compact-subset estimates. It also explains why the candidate's stronger presentation as three individual parameter products does not add a substantial contribution to its **frozen theorem**, which asks for an embedding and does not prescribe the factor form of its coordinates.

## Primary comparison and contribution judgment

Demailly–Lempert–Shiffman, [alg-geom/9212001v3](https://arxiv.org/abs/alg-geom/9212001v3), Lemma 2.5, supplies n+r generators for a rank-r holomorphic bundle outside a coherent exceptional set. Its proof successively lowers rank-defect dimensions, using sections nonzero at selected component points. Cartan B provides those choices in its setting. Neither its statement nor that proof gives a prescribed global weighted sup norm. The explicit ℓ¹/Baire argument above is the norm-preserving version of that same dimension-drop operation, after the basepoint-free family has been supplied. Thus the number three is classical; applying the lemma alone without the weight argument would be insufficient.

Forstnerič's [1709.05630v5](https://arxiv.org/abs/1709.05630v5), §§2.1–2.2, constructs proper Euclidean embeddings through compact-open approximation, growth on an exhaustion and fiberwise projections. It does not produce this bounded embedding. Its dimension-five conclusion for general Stein threefolds is not a subsumption: properness into Euclidean space and bounded image are different requirements. The original Forster 1970 body was not available in the inherited retrieval and is not asserted read.

Jarnicki–Pflug's [2022 survey, §2.1](https://doi.org/10.1007/s12220-022-00970-8) makes the Hartogs coefficient/weight interface explicit in Example 2.1 and subsequent envelope statements. It does not construct a basepoint-free family for this source weight or the frozen bounded C⁵ embedding. Its [2024 correction](https://doi.org/10.1007/s12220-024-01546-4) is a duplicate-publication notice and identifies the 2022 article as the version of record; it does not alter the mathematical comparison used here.

The strongest case for substantiality is the same-manifold contrast between bounded higher-codimension embedding and absence of bounded coordinates in intrinsic dimension, together with the genuine necessity of norm control. I preserve that qualitative information. But its norm control is paid by unit scalar projections of the source's explicitly normalized two-coordinate vectors. Finite coordinate substitutions already remove every basepoint with a uniform constant; no new cancellation, geometric construction, global PDE estimate, or quantitative boundary repair remains. Classical finite generation then finishes the exact target. This is an actual reduction, not an argument that an elementary proof can never be substantial.

I therefore classify the retained full proof as **TECHNICAL**, not SUBSTANTIAL. No read primary theorem was identified as a duplicate of the full conjunction, and I make no worldwide priority claim. The verdict does not require proving that no unlocated paper exists, nor does it infer novelty from unsuccessful searches.

## History, chronology and disposition

Independent bounded searches covered proposals, iterations, reviews, campaign records and findings, excluding recursively copied inputs/private bodies. Exact hits and commands are retained. The Kähler proposal is the compact fourfold minimal-model chain; I98's developed targets concern relative K3/Oka flexibility, punctures and splitting; I135's uniformization target is planar circle-domain geometry; I31's Hartogs use is algebraic extension across a vertex. These do not contain this weighted-product bounded-embedding operation. Generic scalarization hits also include the old complete-Crouzeix chain, which concerns matrix functional-calculus witnesses, not these holomorphic weights. No operative older developed match was found in this bounded history screen. This is not a claim to have reread every archived proof.

The author openly performed feasibility reasoning before freezing, as `mechanism-checkpoint.md`, `pre-freeze-comparison.md` and `freeze-receipt.json` show. This is not a blind preregistration; the recorded chronology is consistent and there is no observed post-review scope reduction. The full proof remains useful retained work. Recommend closing this contribution gate as TECHNICAL, leaving the proof PASS and exact frozen artifact untouched, without a new counted result or a publication recommendation from this review.
