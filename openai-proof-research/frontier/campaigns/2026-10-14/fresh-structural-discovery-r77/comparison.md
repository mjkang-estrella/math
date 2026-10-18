# T296O operational contribution comparison

This is author-side comparison for separate independent review, not a contribution verdict. Worldwide priority and exhaustive literature coverage are not asserted.

## Pinned source: what is already paid

OpenAI, *Relative generation and the generator problem for finite factors*, immutable revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, is the sole corpus family used. The complete tree and catalogue give one manuscript in family 296. All nine non-PDF blobs are retained and verified; all five mathematical sections were read completely, including their proofs. The introduction's references to free-group-factor isomorphisms and W*-bundles are not additional premises and those separate bodies were not read here.

Source `prop:perturbation` already supplies the coordinated long-word construction, small trace norm, the exact alpha/2 linear response, positive free-group coefficient majorization, and a geometric bound on every nonlinear degree. Source `lem:free-haar-extension` and `lem:haar-absorption` supply all freeness. Source `lem:projection-continuity` and `thm:relative-generation` supply the Baire conversion. None of these mechanisms is newly claimed.

**The unconstrained operator-norm upgrade is also paid.** The source's unchanged h is alpha/ell times a sum of ell free Haar imaginary parts. Haagerup's length-one bound gives ||h||≤sqrt(2)alpha/sqrt(ell), by the faithful-trace moment argument in candidate §5. Clipping representatives to this bound leaves the same tracial-ultrapower element and enforces the bound at every coordinate. Applying the source's original left perturbation, then its Baire argument on the norm-complete U(M), yields norm-dense generic unconstrained relative generators. This is an elementary strengthening of the source proof, not an independent substantive contribution. Parent author feedback highlighted this reduction after the scope freeze; the frozen norm-conjugacy target is unchanged, and the final comparison credits the reduction explicitly. The freeze's preliminary mention of clipping as proposed new control is not a novelty claim maintained here.

The remaining target restricts the added generator to **each exact nonscalar unitary orbit**, with arbitrarily norm-small changes of a prescribed conjugator. Substitution of an arbitrary norm-dense subset of U(M) into that orbit is invalid: a dense set need not meet a given orbit at all. The source's left perturbation does not preserve the spectrum. Our replacement e^{ih}u e^{-ih} introduces 2ell ordered exponential rows. Their first-order terms partially cancel, leaving beta=1−|tau(u)|², and their nonlinear words contain non-Haar u-coefficients. The source coefficient isometry no longer applies to those words. Candidate §2 proves only orthogonality of different free-group degrees, then uses triangle bounds within a degree; §4 redoes the full coefficient estimate with a doubled positive envelope. This exact constrained response and its remainder are the residual contribution for review. They may still be judged a technical adaptation of paid operations; statement novelty alone does not settle substance.

## Primary: prescribed projection encodings and the norm topology

M. Ma, R. Shi and S. Yang, *The similarity of irreducible operators in factors*, arXiv:2604.21482v2, observed PDF dated 29 April 2026. Actual passages read: extracted lines 1–220; 670–890. These include Theorem 1.1, the graph-projection construction of Lemma 2.2, complete Lemma 3.7 and Proposition 3.8 proofs, Theorem 1.1 proof, and Proposition 3.10 proof/Remark 3.11.

Theorem 1.1 under G(M)=0 gives, for a masa A and a suitable nonzero projection P∈A, a unitarily equivalent projection which, together with A(1−P), generates M. Proposition 3.8 treats a prescribed projection partition with the comparison relations P_j≾P_0≾1−P_0. Proposition 3.10 says a nonscalar self-adjoint operator is the real part of a generator. The pinned source already gives G(M)=0 for all separable II1 factors, so these hypotheses are paid. They must not be repackaged as new results.

Their **actual construction has norm flexibility** even though the theorem is phrased existentially. In Lemma 3.7 one can replace every positive corner generator A_n by δ A_n. Its range projection and generated algebra are unchanged. Then A_0=(P_0−Σ A_n²)^(1/2) tends in norm to P_0 and V=A_0+Σ A_n E_12^(n) tends in norm to P_0. Hence P_0'=V*V tends in norm to P_0 while retaining the generation conclusion. For close projections the polar part of P_0'P_0+(1−P_0')(1−P_0) gives a conjugating unitary tending to 1. Thus this primary already supplies norm-small constrained perturbations **when the initial projection belongs to the prescribed partition**. Our comparison does not dismiss it as a trace-norm-only theorem.

What is not supplied by that read operation is norm-density at an arbitrary projection or unitary orbit point relative to an independently fixed irreducible P. Its recovery uses the fixed partition projections P_n, including P_0, as members of the auxiliary generated algebra. For an arbitrary q∈M there is no assumption q∈P, nor a prescribed projection partition in P containing q. Replacing P by W*(P,q) inside that construction would change the retained coefficient algebra and does not prove generation by P and the perturbed q alone. Nor does the fixed-real-part result keep both the spectrum of the added element and the existing coefficient algebra fixed. This identifies an operational missing interface, not a worldwide non-implication theorem.

Primary URL: https://arxiv.org/pdf/2604.21482 . Private receipt records the exact observed v2 bytes.

## Primary: norm-dense irreducible operators

R. Shi, *Normed ideal perturbation of irreducible operators in semifinite von Neumann factors*, arXiv:1911.07696v2, observed 21 June 2020. Extracted lines 1–140 were read, including the introduction's precise Theorems 3.5 and 4.1 and definitions. Its subsequent proofs were not read or used as premises.

These results give small norm/ideal-norm perturbations that make an operator generate an irreducible subfactor. The perturbation is unrestricted; the target is irreducibility rather than equality with M, and no independently fixed P plus exact unitary orbit is retained. A normal operator alone remains normal under unitary conjugation, so unrestricted irreducibility perturbations cannot directly be substituted for the present relative orbit perturbation. This is an adjacent norm-topology comparison, not proof that no stronger primary result exists elsewhere.

Primary URL: https://arxiv.org/pdf/1911.07696 .

## Primary: generation invariant and finite-index relative generation

Dykema–Sinclair–Smith–White, *Generators of II1 factors*, arXiv:0706.1953v2, observed 2 November 2007. Extracted lines 1–145 and 1050–1080 were read. The extraction drops some ligatures; the statements in these passages are legible. No claim of reading the whole paper is made.

The paper develops generator invariants and amplification; its Lemma 6.2 uses the downward basic construction, identifying a finite-index extension with one obtained by adjoining a Jones projection. This already pays one-projection relative generation in that setting. It gives neither an arbitrary trace/spectrum orbit nor norm density at every prescribed conjugator. The pinned source itself credits these facts and classical matrix encodings. Primary URL: https://arxiv.org/pdf/0706.1953 .

## Rejected pre-freeze trace-norm target

The 2-norm orbit question was exploratory, never frozen, and was discarded before the present norm statement was frozen. Here is the substantive reason rather than a mere label.

For any II1 subfactor P⊂M, choose in P a rational-trace projection e of very small trace ε and matrix units splitting e into equal halves. A single generator x of the half-corner, supplied by the source, can be recovered from the graph projection

    Q=[[a,a x*],[x a,x a x*]],  a=(1+x*x)^(-1),

in eMe, by multiplying its entries with those matrix units and inverting a. It has trace ε/2. Given any projection p with trace t and ε<2min(t,1−t), there is a projection p0≤1−e of trace t−ε/2 within O(sqrt(ε)) of p in 2-norm. Indeed the range s of (1−e)p has trace between t−ε and t and ||p−s||₂²≤2ε; add or remove a subprojection of trace at most ε/2 inside 1−e to obtain p0. Then q=p0+Q has trace t and is 2-close to p, while P and q recover Q and the corner generator, hence M. Equal-trace projections in a finite factor are unitarily conjugate. This is classical encoding plus a small-corner modification; it proves no operator-norm closeness because ||Q||=1 independently of ε.

For full unitary orbits, any nonscalar u has a nontrivial spectral projection p=f(u). A small 2-norm conjugator carrying p to a nearby equal-trace q also gives a 2-near conjugate of u, and generation follows from q∈W*(vuv*). The near conjugator follows from standard projection alignment, or by matching the overlap and defect corners. This supporting screen is not a second nominee, and its omitted routine alignment details are not premises of the norm proof.

## History and limits

The full canonical path catalogue was parsed to bind all nine source blobs. Bounded semantic searches of actual iteration/finding/campaign Markdown used relative generation, generator problem, prescribed projection/spectrum, norm-generic and unitary-orbit phrases; copied private/input/reproduction/catalogue material and pending source-133 review directories were excluded. The matching parent-r10 family-289 path-lifting screen was read completely: it is a technical continuous selection theorem for conjugate varying algebras, not the present generation problem. Broad early searches also located developed 095/096/097 chains, which were not pursued. One rg invocation included a nonexistent frontier/proposals path and reported that error; the existing paths were still searched. No missing path is treated as an empty semantic archive, and no exhaustive history eligibility certificate is asserted.

All external source bodies are retained privately. Only the stated passages were read. Search results and secondary course pages were navigation, not theorem premises. The full new theorem is proved in candidate.md relative to the precisely stipulated source interfaces; literature absence does not form part of that proof.
