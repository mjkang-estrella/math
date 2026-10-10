# I98 — Complex and Kähler geometry: relative K3 flexibility

**Disposition: developed gap report; no substantial finding nominated.** The main target R98 below is unproved and unrefuted. Two routes give actual holomorphic constructions, A98 and W98, with proofs in this report. Both are **author-level technical consequences**, not independently audited theorems. W98 is a full relative result for an explicitly described class of families, but reduces to the complete-flow operation of Xie–Zhao and the classical subelliptic Oka principle. A98 has a finite spray-radius quantifier which cannot be exchanged with its base-neighborhood quantifier. Neither increments the eight accepted findings.

The global-ellipticity proposal E98 is rejected by a current external primary preprint, rather than by combining stipulated corpus assertions into a contradiction. Its counterexample is not a counterexample to R98. Q90 and Q91 remain closed technical branches; no topology construction or active I97/scout output is used. No shared ledger, staging area, commit, or publication was changed.

## 1. Premises, history, source scope

All theorems and lower proof operations of openai/math at **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are stipulated true. This is not an audit of that corpus. The project rules, upstream metadata, complete tree and four current ledgers were frozen before research. The history review used the current acceptance summaries, continuation rules, and lexical context concerning geometry, K3, Oka, Hodge/Kuga–Satake, nonconical rings and the closed later branches. The 487,049 bytes of ledgers were not all semantically reread: the precise context passages and snapshots are retained. There is no claim of a full semantic corpus review.

The inherited search domain contains all 10,373 original blob positions: 9,340 I14 originals, 257 other original byte files, and 776 original PDFs represented by inherited text extractions. The complete tree has 13,223 entries and 749 manuscript directories. Three full-domain, case-insensitive lexical searches retain their exact regular expressions and the ordered line-hit multisets, including false positives and repeated representations. Searches use Python splitlines, not LF-only numbering; source theorem slices separately record LF ranges. No recursive corpus copying or bulk redownload occurred.

The selected title families and 423 selected representations are an early companion screen, not 423 full readings. Read records distinguish complete used proof units from theorem-only screens. Only five primary PDF bodies (six files because the Xie–Zhao current/fixed-version bytes agree) and a few selected inherited PDFs are re-extracted by the final verifier; all 776 inherited extraction hashes are checked without claiming universal re-extraction.

### Exact pinned interfaces

The following paths are all relative to the pinned repository's preprints directory. Full URLs, original Git blob identities, SHA-256 hashes and passage locators are in the evidence files.

* **K3:** Every-complex-K3-surface-is-Oka-September-23-2026. Introduction, thm:main is CAP for every complex K3, every source dimension, every nonempty compact convex K, every local holomorphic map and every positive error. It includes nonprojective K3s. The dense-immersion corollary is already present. local.tex, loc:deformation deforms maps on **relatively compact Stein source domains**, by horizontal lifts on a Stein graph neighborhood. loc:spray uses a trivial pulled-back tangent bundle. dense.tex already gives ellipticity of **projective** K3s and Enriques surfaces, and explicitly does not claim it for nonprojective K3s.
* **K3 lower constructions:** projective.tex, prj:prepare/prj:transverse/prj:flow/prj:strips constructs two transverse complete directions from proper genus-one source families with distinct ample degrees. The map to the K3 need only be generically finite, not proper. Full proper source fibers are retained for complete flow. degeneration.tex, deg:open and its ending construct an unrestricted open region by deforming a finite raw atlas and repeating the uniformly controlled sewing construction. dynamics.tex treats three rationality types of a single marked period. None of these statements is an asserted Oka-map theorem for an arbitrary moving target.
* **Shafarevich surface:** A-surface-counterexample-to-Shafarevich-holomorphic-convexity-September-23-2026, thm:main and complete 06-surface.tex. Its smooth projective surface has a connected nodal union of rational curves whose **union** has infinite fundamental-group image. A lifted connected component is a locally finite, closed, noncompact union of compact rational curves. The source does not say that this union is a tree. Its construction explicitly explains that lifted tails can join different lifted main components and create graph cycles. The compactification uses finite detection of all commuting local meridian groups, including exceptional meridians after resolution.
* **Semialgebraic covers:** Semialgebraic-universal-covers-of-normal-projective-varieties-September-24-2026, thm:main gives U ≅ D × C^m × F for a connected normal projective X, bounded symmetric D and simply connected normal projective F. Its **existing** cor:remmert-semialgebraic proves properness of U → D × C^m, the sheaf identity, holomorphic convexity and the exact Stein iff F is a point statement. Its Singer corollary is also already present. No new hull/Stein deduction is nominated.
* **Special Kähler:** The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026 proves virtual abelianity in every dimension. Its corollaries already include special-manifold holomorphic convexity and analytic compactifiability. A normal compact-complex compactification gives the deck-group statement; the stronger compact-Kähler compactification gives, after finite étale cover, an Albanese bundle with simply connected compact Kähler fiber and universal cover F × C^q. That F need not be projective.
* **Splitting:** Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026, thm:main requires a specified pair of positive-rank **integrable** holomorphic summands on a compact Kähler manifold. It identifies their lifts with factor tangents. Its factors may be noncompact, and it makes no finite-cover product assertion. The non-uniruled projective and nef-and-big consequences are included. The rationally-connected companion already proves integrability and a compatible projective product for that class.
* **Bounded domains:** Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026 allows a connected bounded semialgebraic open subset of a complex affine variety, even initially singular, and a properly discontinuous action with compact quotient, without freeness. Smoothness and bounded symmetry are the conclusion. Its final proof constructs a bounded intrinsic-dimensional realization of the quadratic model and checks Vey's hypotheses. These conclusions cannot be renamed as a new classification.

The October 6 ordinary Kähler fourfold MMP, conditional good models, log abundance and numerical semiampleness revisions, and October 7 generalized-lc termination, were screened at their actual statements. In particular, conditional good models retain orbifold-Iitaka/effective-abundance hypotheses; log abundance retains its displayed log-Iitaka hypothesis; numerical semiampleness produces a line bundle with the same Bott–Chern class, not automatically the original line bundle. Generalized-lc termination fixes the same nef b-divisor and actual canonical representatives throughout the specified small projective diagrams. None supplies the holomorphic map-space lifting needed here. These papers are not premises of A98 or W98.

## 2. Four exact targets screened

**R98 — selected.** For every surjective proper holomorphic submersion π: X → B of complex manifolds whose fibers are complex K3 surfaces, prove that π is an Oka map. There is no projectivity, isotriviality, polarization, global volume-form trivialization, or compactness assumption on B. Proper submersion gives the Serre-fibration part. The missing analytic assertion is POPAI, with the base map fixed. Explicitly, for every reduced Stein space S, closed complex subspace A, compact O(S)-convex K, compact Hausdorff pair P0 ⊂ P, continuous family of holomorphic maps g: P × S → B, and continuous lift f0 which is holomorphic for P0 and near K and on A, find a lift homotopy ft with πft=g, fixed on P0 × S and P × A, arbitrarily close to f0 on P × K throughout, ending holomorphic on S for every p. This is the K3 case of Lárusson's proper-Oka-fiber question, not fixed-target parametric Oka.

**P98 — deferred.** For every complex K3 surface X and every finite A ⊂ X, prove that X minus A satisfies CAP in **all** source dimensions. The pinned K3 theorem concerns the compact target, and approximation into X need not avoid A when the source dimension is at least two. One-dimensional transversality/Oka-1 removal does not prove this target. In the projective source construction, if each of the two evaluation maps is finite over A, deleting the finitely many source-family parameters whose fibers hit A preserves complete elliptic flows; this is only a restricted lower-operation route. No claim for all projective punctures, all nonprojective punctures, or blowups is made here.

**E98 — rejected.** Every complex K3 surface admits a global dominating holomorphic vector-bundle spray. The projective part is already in the corpus, via Forstnerič–Lárusson v6. Kusakabe–Matsumura, arXiv:2610.12175v1, Theorem 1.2(2)/Example 2.10 gives Kummer surfaces of algebraic dimension zero with **no local** dominating vector-bundle spray. The entire used obstruction proof and its Example 2.9 hypersurface-construction dependency were read through their endings. This is an external author theorem, not an independent audit by I98. It rejects E98 on its stated nonprojective scope. It does not contradict fixed-target Oka, convex ellipticity over Stein sources, or R98.

**S98 — deferred.** Let π: X → B be a proper holomorphic submersion over a contractible polydisc, with compact connected Kähler fibers and a relative Kähler form. Suppose T_(X/B)=E1⊕E2 has specified positive-rank holomorphic summands integrable in the fibers. On the ordinary universal cover of X, whose fiber restrictions are universal covers by Ehresmann and contractibility of B, construct holomorphic submersions Yi → B with simply connected fibers and a compatible biholomorphism X~ ≅ Y1 ×_B Y2. This asks for simultaneous analytic leaf spaces, not just a product on each fiber. The pinned splitting theorem and its rationally-connected companion do not state this parameter theorem. No proof or counterexample, and no novelty verdict, is claimed; it was not pursued instead of R98.

The first and third targets have direct named Oka-problem significance in primary sources. Searches for a matching MathDB K3/Oka page did not produce a verified page; no MathDB ranking is invented. Lárusson's 2011 introduction and §4 explicitly formulate the proper-family question, and Kusakabe's 2020 introduction describes classification of submersions satisfying POPAI as a fundamental problem. That is observed significance evidence, not a claim that solving a restricted subclass would settle the whole question.

## 3. Current literature and strongest reductions

Primary sources were fetched as complete PDFs and their relevant proof units read:

1. Finnur Lárusson, *Deformations of Oka manifolds*, [arXiv:1106.5300v1](https://arxiv.org/abs/1106.5300v1) (2011), all nine pages. Theorem 7, Lemma 11, Corollary 10 and Theorem 16 are decisive. On any compact subset of a proper family all of whose fibers are Oka, the fibers are already uniformly Oka in his quantitative finite-window sense. Thus the specialization of that uniformity to K3 fibers is a **known reduction**. It cannot count as a new substantial estimate.
2. Yuta Kusakabe, *Elliptic characterization and unification of Oka maps*, [arXiv:2003.03757v1](https://arxiv.org/abs/2003.03757v1), published Math. Z. 298 (2021). Definition 1.2 has a global C^N spray variable on one neighborhood of a convex source compact, preserving π exactly. Theorem 1.3 equates this with POPAI. The local spray/right-inverse lemmas and the complete CAP-to-convex-ellipticity proof of Proposition 5.3 were read; its recentering operation is a direct antecedent of A98. We do not claim to independently reprove the full parametric Oka principle.
3. Song-Yan Xie and Shengyuan Zhao, *Periods of Oka K3 surfaces are dense*, [arXiv:2608.24392v2](https://arxiv.org/abs/2608.24392v2), 17 September 2026. Current version metadata was checked; a separate fixed-v2 PDF retrieval equals the initially fetched current PDF byte for byte. Full Lemma 3.1, Propositions 3.2/3.3, Corollary 3.4 and Proposition 4.4 through its ending were read. Their complete-flow construction is the direct precursor of W98. Their period-density theorem does not supply arbitrary-family POPAI. The deformation retaining the three pencils lies on the specified lattice-polarized period locus.
4. Yuta Kusakabe and Shin-ichi Matsumura, *Atiyah classes and ellipticity of Oka manifolds*, [arXiv:2610.12175v1](https://arxiv.org/abs/2610.12175v1), 8 October 2026. Introduction and complete Examples 2.9/2.10 with their conclusions were read. The obstruction uses meromorphic Taylor coefficients of a squared displacement, algebraic reduction of P(E), and a branched-cover calculation along an actual hypersurface mapped into an exceptional curve. It is not a deduction from absence of global vector fields.
5. Franc Forstnerič, *From Stein manifolds to Oka manifolds: the h-principle in complex analysis*, [author's 24 September 2025 PDF](https://users.fmf.uni-lj.si/forstneric/papers/2025hprinciple.pdf), used only as a current overview/check of terminology. The original research sources above, rather than the survey, support the proof reductions.

Forstnerič–Lárusson's arXiv:2502.20028 metadata lists v6, 5 May 2026, matching the pinned bibliography. The complete-body argument is not a dependency beyond the already accepted pinned projective-spray corollary. Chen–Gounelas's metadata lists v3, 5 November 2022; its genus-one input is used only as the stipulated operation already exposed in pinned projective.tex, not as a newly audited external theorem.

A search-index author snippet suggested another relative K3-family statement. The current author-index page did not expose an identifiable matching primary paper; that snippet was not promoted to a theorem or a novelty conclusion. This bounded search limitation is retained.

## 4. Route A: an actual finite-radius holomorphic family with exact first jets

All vector norms below are maximum norms, and matrix norms are their induced operator norms. Write Δ_R^d for the open polydisc of radius R in C^d.

### A98 (author proof; technical)

Let π: X → B be a holomorphic submersion of complex manifolds of relative dimension two, where B is a neighborhood of 0 in C^q. Assume X0 is Oka. Let K ⊂ C^m be compact convex, U a neighborhood, and f: U × B → X holomorphic with πf(z,b)=b. After shrinking U to a convex neighborhood U0 of K and B about 0, choose a holomorphic frame

    L(z,b): C² → T_(X/B),f(z,b).

There are a convex neighborhood V of K with closure contained in U0 and a holomorphic map

    S0: U0 × C² → X0,
    S0(z,0)=f(z,0),  d_w S0(z,0)=L(z,0),

such that for every finite R>0 there are δ_R>0 and a holomorphic map

    G_R: V × Δ_R² × Δ_(δ_R)^q → X

satisfying, on its whole domain,

    πG_R(z,w,b)=b,
    G_R(z,0,b)=f(z,b),
    d_wG_R(z,0,b)=L(z,b),
    G_R(z,w,0)=S0(z,w).

V and S0 are fixed before R. No positive lower bound on δ_R as R grows is asserted. Properness and the K3 assumption are not needed for the finite lemma except to guarantee, in the intended application, that X0 is Oka.

**Construction of S0.** Apply fixed-target convex ellipticity to f(·,0) near a slightly larger convex compact containing K. This is the pinned CAP theorem followed by Kusakabe Proposition 5.3, with target X0. It gives a spray T(z,ξ), entire in ξ∈C^N, with core f0 and surjective derivative A(z): C^N → f0*TX0. Shrink to a Stein convex neighborhood U0 where A is surjective. Cartan B splits the exact sequence of vector bundles: there is a holomorphic R0(z): C² → C^N with A(z)R0(z)=L(z,0). Then S0(z,w)=T(z,R0(z)w) has all asserted properties. The initial frame exists because U0 × B can be chosen contractible and Stein, so Oka–Grauert trivializes the rank-two pulled-back vertical tangent bundle.

**Finite deformation.** Fix nested convex neighborhoods of K whose closures lie in U0; the smallest is V, fixed once for all R. For any finite R and η>0, apply the complete horizontal-flow proof of pinned loc:deformation on a slightly larger relatively compact Stein source product containing the larger neighborhood times the closed polydisc Δ_(R+2η)². It produces a jointly holomorphic map S~(z,w,b), defined on that product for b near 0, with πS~=b and S~(z,w,0)=S0(z,w). The base radius can depend on R.

One must correct its core: S~(z,0,b) need not equal the prescribed moving f(z,b). On the graph of f, construct vertical chart sprays E(z,b,v) with E(z,b,0)=f(z,b) and derivative L(z,b), by extending the frame as vertical vector fields on a Stein graph neighborhood and composing short flows. This is the relative version of loc:spray; the fields lie in ker dπ, so E preserves b exactly. It is used only near the compact graph over the retained z and b margins. Define

    H(z,w,b)=E(z,b,·)^(-1)(S~(z,w,b))

for small w,b. Then H(z,0,0)=0 and D_wH(z,0,0)=I. Holomorphic inverse-function/contraction arguments give a holomorphic a(z,b) with H(z,a(z,b),b)=0 and a(z,0)=0. Let

    A(z,b)=d_wS~(z,a(z,b),b),
    C(z,b)=A(z,b)^(-1)L(z,b).

A maps into the tangent at f(z,b), so this is a well-typed matrix. At b=0, C=I. Set

    G_R(z,w,b)=S~(z,a(z,b)+C(z,b)w,b).

This is the requested family once its domain is paid. Both the core and derivative are exact identities, rather than limits of approximate identities. At b=0 the affine change is the identity, preserving S0 on the entire retained w-disc.

**A quantitative domain payment.** The following gives actual sufficient constants, though they depend on the chosen finite deformation. Choose r,β>0 so the chart expression H exists for z near closure(V), |w|≤r, |b|≤β, while S~ exists for |w|<R+2η and |b|<β on a larger z-domain. On slightly smaller compact margins choose M,N≥1 with

    |H(z,0,b)| ≤ M|b|,
    ||D_wH(z,w,b)-I|| ≤ N(|w|+|b|).

These follow from holomorphic derivatives and H(z,0,0)=0, D_wH(z,0,0)=I; the vector b norm and q-dependent derivative sums are included in M,N. Put c0=2M and c1=2N(2M+1). It suffices to take

    0 < δ_R < min{ β/2, r/(4M),
                    1/[4N(2M+1)], η/[2(c0+c1R)] }.

Indeed, the equation w=-H(z,0,b)-[H(z,w,b)-H(z,0,b)-w] contracts the closed ball |w|≤2Mδ_R: the derivative of its nonlinear part is at most N(2M+1)δ_R<1/4, and the image has norm at most Mδ_R+(1/4)2Mδ_R<2Mδ_R. Uniform contraction gives holomorphic a and |a|≤c0δ_R. At its root, E has derivative L, so C=(D_wH(z,a,b))^(-1). The Neumann estimate yields

    ||C-I|| ≤ 2N(2M+1)δ_R = c1δ_R.

Consequently |a+Cw| ≤ R+(c0+c1R)δ_R < R+η/2, inside the deformation domain. The fixed compact margins justify uniform holomorphy in z and b. This proves A98.

This calculation pays a new explicit interface in the report. Its ingredients are nonetheless the source's finite-domain horizontal flow and classical analytic recentering. It does not provide a bound for β,M,N as R→∞, nor domination for w away from zero.

### Why finite windows and uniform Oka norms do not close R98

Lárusson's Corollary 10 bounds, on compact parameter sets, the cost of approximating each derivative-bounded input map on K by a map on a larger **finite** V. The approximant can be selected separately for each parameter. R98 requires one holomorphic family and a domain common to all spray radii. A98 has quantifier order

    for each R, there exist δ_R and G_R,

whereas convex ellipticity requires, for each input lift, a fixed source neighborhood and one spray on all C^N. Taking an intersection of neighborhoods or a diagonal subsequence does not supply this.

Here is an exact obstruction to that inference even for a trivial Oka family. Let E=C/Λ be an elliptic curve and let brackets denote its quotient map. For every R≥1 put

    F_R(w,b)=[w/(1-bw)]    (|w|<R, |b|<1/(2R)).

The maps agree wherever both are defined, have core 0, derivative 1 in w at 0, and central map [w]. Nevertheless the resulting compatible family cannot extend holomorphically to C × Δ_δ for any δ>0. Fix 0<|b0|<min{δ,1/4}. The invariant holomorphic one-form θ on E pulls back, wherever the formula is defined, to

    d_wF*θ = dw/(1-b0w)².

If an extension existed, its pullback form would be holomorphic on all C and, by the identity theorem, would have this coefficient away from w=1/b0. The displayed genuine double pole rules that out. This argument uses a differential on E, so a pole of an affine coordinate is not incorrectly treated as a singularity of a map to P¹. The example refutes the **inference from compatible finite-radius extensions**, not the Oka-map property of E × Δ → Δ, which does hold. R98 is not refuted.

## 5. Route B: a full relative construction on families with enough curve maps

The following theorem constructs actual sprays with parameter and twisting control, including non-isotrivial families. It is deliberately stated beyond one fixed Wehler equation so that every hypothesis used in the construction is visible.

### W98 (author proof; technical)

Let π: X → B be a surjective proper holomorphic submersion of complex manifolds with connected K3 fibers. Suppose there are finitely many smooth complex curves C1,…,Ck and holomorphic maps fi: X → Ci such that

    T_(X/B),x → ⊕i T_Ci,fi(x),  v ↦ (dfi(v))i

is injective for every x. Then π is a holomorphically subelliptic submersion, and therefore an Oka map. No global trivialization of the relative canonical bundle or of the Hodge line on B is assumed. The maps, curves and base are complex analytic data; no continuous marking is substituted for them.

In particular this applies to any smooth proper family of smooth (2,2,2) hypersurfaces in (P¹)^3 supplied with its relative embedding in B × (P¹)^3. It allows holomorphically varying coefficients. It applies also to a family on which the three pencils of Xie–Zhao Proposition 4.4 actually extend.

**The Hodge-line twist.** Since every fiber has one-dimensional H^0(K), proper cohomology and base change gives a line bundle L=π_*K_(X/B). Evaluation π*L → K_(X/B) is an isomorphism: it is an isomorphism on each fiber because a nonzero K3 two-form is nowhere zero, and hence at every point. Contraction therefore gives an isomorphism

    T_(X/B) → Ω¹_(X/B) ⊗ π*L^*,
    v ↦ (ω ↦ ι_vω).

For hi=(π,fi): X → B × Ci, take Mi=pr_Ci*Ω¹_Ci ⊗ pr_B*L^* and Ei=hi*Mi. Define

    Ai: Ei → T_(X/B)

by pulling back the one-form along fi and inverting the contraction above. Locally, if ω is a frame of L and λ=a du⊗ω^*, the formula is ι_(Aiλ)ω=a dfi^*u. Changing ω to g(b)ω multiplies its dual by g(b)^(-1), and changes the coefficient of the same λ by g(b). These factors cancel. Thus Ai is globally well defined. The dual L^*, rather than L, is essential.

**Tangency, including singular level fibers.** Certainly dπAi=0. On a surface an alternating form identifies a covector α with a vector v satisfying α(v)=ω(v,v)=0. Applying this to α=dfi^*du gives dfiAi=0. The equation is valid also at critical points of fi, where α=0. Therefore dhiAi=0 everywhere. No smoothness of a level fi^(-1)(c) is needed.

**Complete flow and holomorphic parameters.** Regard Ei as the fiber product X ×_(B×Ci) Mi. On it define the vector field

    Vi(x,λ)=(Ai,xλ, 0).

The tangency identity makes this a globally defined holomorphic vector field. An integral curve through (x,λ) stays in hi^(-1)(hi(x)) × {λ}. This is compact: it is closed in the compact π-fiber X_(πx). A holomorphic vector field cannot escape in finite complex time while its orbit stays in a compact subset of its manifold of definition. More explicitly, a finite coordinate cover of this compact set gives a uniform small complex-time existence radius. Successive compositions of those local flows give the solution on every finite time disc; uniqueness makes the continuations agree and gives a jointly holomorphic C-action. This argument is locally uniform near any given initial point and finite time, so the time-one map is holomorphic on all of Ei, not merely separately holomorphic on its individual fibers.

Let si: Ei → X be projection of that time-one flow. At λ=0 the vector field vanishes, so si(0x)=x. Its first variation is Ai,xλ: along λ=0 the initial point stays x, and differentiating the ODE in λ and integrating time from 0 to 1 gives exactly Ai,x. Both π and fi are preserved by si.

**Domination and the Oka-map conclusion.** The injective vertical differential of the product of the fi has surjective dual. Hence the images of dfi^*Ω¹_Ci span Ω¹_(X/B) at every point. Tensoring by L^* and applying the contraction isomorphism shows that the images of Ai span T_(X/B). Thus the finite family (Ei,si) is a dominating family of global fiber sprays for π. This is subellipticity. The classical parametric Oka principle for subelliptic submersions gives POPAI; proper-submersion Ehresmann gives the topological fibration. Together these prove W98, with all the parameters in R98's formulation on this restricted class.

**Full-scope reduction / contribution decision.** The flow above is exactly the operation in Xie–Zhao Lemma 3.1 applied to hi, whose fibers are compact. Their Proposition 3.2 supplies the cotangent-contraction/spanning mechanism. Passing from a fixed symplectic form to the relative Hodge line only changes the source line bundles by L^*. The subelliptic Oka implication already works for submersions. This is a concrete reduction covering all hypotheses and all parameters of W98; it is **technical**, even though the exact family theorem is not asserted in the pinned title statement. No independent worldwide novelty inference follows from absence of a duplicate title.

### Why this construction stops on the full K3 deformation space

Here is a precise obstruction for the proper-curve route. Let B be a simply connected small base in a K3 Kuranishi family, q: C → B a proper holomorphic submersion with connected compact curve fibers, and F: C → X a holomorphic map over B, nonconstant on every fiber. Identify the integral H² local system with the K3 lattice, and use Poincaré duality to regard α_b=F_(b)*[C_b] as an integral H² class. Ehresmann trivializations of q and π and the global continuous map F show that this class is locally constant: the fiber maps are homotopic along any small base path. Thus it is one class α on B. It has type (1,1) in every fiber. Equivalently, for a local nonzero holomorphic period vector ω_b,

    (α,ω_b)=0.

Indeed, integration of a (2,0)-form over a complex curve is zero, as is integration of its conjugate. The class is nonzero: its pairing with a Kähler class of the fiber is the positive area of the nonconstant map, with positive multiplicities. These assertions require no algebraic parameterization of C or F.

The local period map of the Kuranishi family is a local biholomorphism onto the period quadric. At a period with α of type (1,1), its tangent space is naturally H^(1,1). The differential of the equation above is pairing with α. It is nonzero: the intersection form restricted to H^(1,1) is nondegenerate, since the (2,0)⊕(0,2) plane is nondegenerate and its orthogonal complement is H^(1,1). Thus α cuts out a genuine complex hypersurface near that point. No full open subset of the 20-dimensional Kuranishi base can support that fixed nonzero curve class.

This pays an obstruction to extending the **particular proper-curve-family mechanism** over unrestricted deformations. The maps in W98 have the same obstruction without needing their singular level curves to form a submersion. A nonconstant map from a compact connected K3 to a connected curve is surjective, so that curve is compact. Pulling back its integral orientation class gives the nonzero effective class of a regular fiber; its positivity follows by integrating a Kähler form on that fiber. A global fi makes this class locally constant along B, by the same homotopy argument. At least one fi is nonconstant by the injectivity hypothesis, and remains so near a given fiber since its nonzero class persists. Thus W98's maps cannot persist across a full Kuranishi neighborhood. This does not rule out relative entire maps or sprays over Stein graph sources. It also explains precisely why the source's projective genus-one construction and Xie–Zhao's retained-pencil deformation do not by themselves settle R98.

The unrestricted raw-atlas region in the pinned degeneration proof is a different mechanism and is not excluded by this curve-class obstruction. Transporting it to all fibers by individual period-orbit choices still does not construct a single holomorphic family of maps through arbitrary input lifts. No blanket negative assertion about that route is made.

## 6. Remaining gap and counterexample checks

The missing geometric statement can be expressed without altering quantifiers: for each compact convex K ⊂ C^m and holomorphic lift f near K into a K3 family (with its possibly nonconstant prescribed base map), construct on **one** neighborhood V of K a holomorphic map

    S: V × C^N → X,
    S(z,0)=f(z),  πS(z,w)=πf(z),

whose vertical derivative at w=0 is surjective for every z∈K. N may depend on the input. Kusakabe's criterion then gives R98. This is an exact restatement of the remaining analytic requirement, **not** an additional theorem established by the finite-radius lemma.

A98 handles neighborhoods of a constant base value and every finite spray ball, with exact moving core/derivative; its paid bound exposes the unbounded-radius dependence. W98 constructs global fiber sprays for relative immersions into products of curves. The arbitrary-family gap is a new construction that either prevents base-radius collapse in Route A or replaces the persistent proper-curve data in Route B. Holomorphic convexity, properness of π, finite étale passage, and passive parameters in maps into one K3 do not supply this construction.

Checks against overstatements:

* Isotrivial holomorphic bundles with Oka K3 fiber are already Oka maps by the bundle theorem. That case is not nominated.
* A98 uses a Stein **source graph**, while E98 asks for a spray based on a whole compact K3. The nonelliptic Kummer example therefore does not refute A98 or R98.
* The torus moving-pole example refutes a proof step, not a K3 theorem, and not the true trivial-family Oka property.
* W98 does not require X or B themselves to be Oka. The base can be a hyperbolic disc.
* W98 does not construct algebraic sprays. Its complete complex-time flows are holomorphic; their algebraicity is neither needed nor claimed.
* No compatibility with an arbitrary extra group action is asserted. A marking is continuous/cohomological information and is not used as a holomorphic trivialization.
* The Shafarevich source has an actual infinite lifted rational-chain obstruction to holomorphic convexity. It is not identified with a Stein or bounded domain. The semialgebraic-cover and special-Kähler results are used only in their own hypotheses, with no ex-falso synthesis.

## 7. Evidence, validation and handoff

The owned evidence contains frozen snapshots, exact queries/hits, the inherited hash mapping by reference and metadata, selected-family inventory, exact theorem slices, read-passage hashes, primary response bytes and version metadata. Only README.md, frontier/README.md, frontier/TEN-FINDINGS.md and frontier/iterations/README.md are permitted live drift; their frozen snapshots cannot drift. The verifier binds no active I97 or other new scout files.

The finite diagnostics check the A98 rational inequalities, the two-dimensional symplectic contraction/twist identities, the moving-pole derivative, and the preserved Wehler-pencil Gram matrix. They are diagnostic algebra, not proof of POPAI or of any geometric theorem. The proofs above carry those claims.

Run, from the project root:

    python -B frontier/experiments/i98_complex_kahler_discovery/verify.py

The verifier is offline and read-only. It checks exact owned inventory/seal bytes, immutable references, every original Git blob/SHA-256 identity, all 776 inherited extraction hashes, three exact lexical search multisets, selected PDF stdout re-extractions, source passage conventions, fixed-version bindings, and the finite diagnostics. It has no download, write, repair, reseal or bytecode operation. Preseal validation was run before the single final seal; preparation failures and extraction warnings remain documented in evidence-notes.md and preseal-events.json. Source replay is not universal proof or contribution certification.

**Parent handoff:** retain R98 as unproved and unrefuted. The deepest reusable paid items are the exact-core/first-jet finite-radius family A98 with its displayed domain budget, and the global relative Hodge-line spray construction W98. Both have full author proofs and explicit technical reductions; neither has a fresh independent analytic verdict. E98 is rejected on current primary-source evidence. P98 and S98 are deferred, not claimed solved. No R-number or count increase is requested.
