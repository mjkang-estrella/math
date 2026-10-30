# Research r81 — almost-isotropic log-concave lattice extensions

Date: 2026-10-29. Disposition: **UNRESOLVED, credit 0**. No complete ordinary result, PROOF.md, Lean, manuscript, acceptance, or novelty clearance is claimed. All work is solo. The parent supplied the integrating tally 8 additional / 38 total; this lane makes no change. The on-disk ledger still has 7 / 37 and is not modified.

## Full attributed question and exact scope

Matthieu Fradelizi, Lampros Gavalakis and Martin Rapaport, *On the Monotonicity of Discrete Entropy for Log-Concave Random Vectors on Z^d*, Discrete & Computational Geometry 76 (2026), 1111–1149, published 26 May 2026, DOI 10.1007/s00454-025-00813-7. Journal Definition 10, Definition 13, Remark 14, and Question 42 were read from the actual public journal body. Latest arXiv:2401.15462v4, submitted 17 December 2025, has the same surviving extension question as **Question 40** in Section 4. The article number containing 2025 does not make the publication date 2025. Initial search wording suggesting that year is superseded here.

The question concerns every fixed dimension d and every almost-isotropic family of log-concave-extensible probability mass functions p_s on the literal lattice Z^d, as the covariance scale s tends to infinity. Log-concave-extensible means that -log p has a convex extended-real extension, with zero probabilities represented by +infinity. Almost isotropic means covariance s^2 I + O(s) in operator norm, with constants independent of s. The source also describes the parameter intrinsically as det(Cov)^(1/(2d)); these formulations must be reconciled when constructing an extension family. It asks for continuous log-concave extensions f_s with **f_s(k)=p_s(k) at every lattice point**, positive finite integrals and finite second moments, whose normalized continuous covariances are almost isotropic as their determinant scale diverges. It does not require integral f_s=1: scaling a function for covariance does not alter its covariance, but would alter the interpolation values. No fixed-small-variance example or bounded-condition-number estimate alone answers this asymptotic question.

The sentence of the question does not explicitly require that continuous and discrete determinant scales agree to O(1). Our investigated sufficient target is the stronger same-scale estimate Cov_R(f_s)=Cov_Z(p_s)+O(s). Failure of that stronger estimate for one construction would **not** refute the literal existence question. The absence of this distinction would be a serious scope error.

Primary URLs:
- https://link.springer.com/article/10.1007/s00454-025-00813-7
- https://arxiv.org/html/2401.15462v4
- https://arxiv.org/abs/2401.15462

## Early duplicates and screened source bodies

Before proof investment, report-filename-first `rg -l` searches covered all campaign dates, including case variants of FINDINGS/SUMMARY, discovery and provenance. `duplicate-screen.json` records 1,858 report files and zero matches for the precise FGR source/name/extension patterns, cone/cylinder source, and Madiman source. Earlier broad screens returned false positives; bounded actual sections of r44/r47/r48/r69 were read. For example r44's 2608.00813 is a different fractional-moment source, and r69's continuous convolution discussion is not this lattice interpolation problem. Zero filename matches establishes only bounded project freshness, not worldwide novelty. No family excluded by the task is reopened; r80's finite/arithmetic domain is avoided.

Three candidate source bodies were screened, plus the selected source's companion and a classical comparator:

1. **FGR journal and v4, selected extension question.** The adjacent iid convolution question is excluded immediately. Remark 12 gives the Reeve tetrahedron support obstruction in dimension 3. The v4 abstract explicitly says the old convolution question and Gaussian example were removed. Reproving that obstruction would be a public proof/domain inconsistency, not a discovery. Only the distinct extension question is pursued.
2. **Dan, Math.StackExchange 5011394, 14 December 2024**, cone/cylinder acute-triangle maximizing aspect ratios. Actual question, sampling definitions and existing answer were read through the public web reader. The answer already supplies extensive coupled simulations and opposite-side evidence near squared ratio 5. A new numerical replay would not be a fresh rigorous source resolution, and the necessary global optimization/integration argument is substantial. Excluded from investment. Direct HTTP returned 403; no retry or challenge bypass occurred. https://math.stackexchange.com/questions/5011394/conjecture-about-random-triangles-inscribed-in-cones-and-cylinders
3. **Madiman–Melbourne–Roberto, arXiv:2512.19003v2, 20 October 2026**, *Four Function Theorems Through Optimal Transport and Entropic Analogs*. Actual introduction and theorem statements show the Gaussian/log-concave-product convolution question is recovered from Karlin–Rinott Proposition 3.7, and the paper itself proves its sharp power-mean range. This is already public, not a nominated question. https://arxiv.org/html/2512.19003v2

The FGR ISIT 2024 companion, *Dimensional discrete entropy power inequalities for log-concave random vectors*, actual approximation propositions, concluding questions and definitions were read. Its Question 2 is the earlier extension formulation; its self-convolution support assertion predates the correction. It supplies no converse to the continuous-to-discrete approximation theorem. https://www.dpmms.cam.ac.uk/~lg560/EPIdISIT.pdf

## Closest prior theorem bodies before substantial computation

FGR journal Proposition 32 and Corollary 33 show approximation of discrete moments/covariance for a **centered continuous isotropic** log-concave density. Remark 38 relaxes this to continuous almost-isotropic families. Their proofs estimate sums of slice maxima using the continuous geometric concentration lemma. They cannot simply be reversed to manufacture an almost-isotropic extension: continuous shape control is an input. The companion's Propositions 1–3 have the same direction of implication.

Cule–Samworth–Stewart, *Maximum likelihood estimation of a multidimensional log-concave density*, arXiv:0804.3989, actual Theorem 2 proof and Theorem 3/Section 4 were read. They supply the classical least-concave tent over prescribed heights and an optimization description of the log-concave MLE. Maximizing likelihood changes the pole heights; no theorem in these read bodies asserts interpolation of every prescribed lattice probability together with the requested covariance approximation. The tent construction below is classical, receives no credit, and is not by itself a new theorem. https://arxiv.org/html/0804.3989

## Sustained proof attempt: canonical extension and moment transport

Work first with finite full-dimensional support A and extend later only if uniform estimates can be proved. Put h(k)=log p(k). Define the concave roof on conv(A) by

    H(x)=sup { sum_i lambda_i h(k_i) : lambda_i>=0,
               sum_i lambda_i=1, sum_i lambda_i k_i=x },

and H=-infinity off conv(A). This is concave: concatenate nearly maximizing convex combinations for two points. At lattice k, extensibility gives a concave extension L with L(k)=h(k); hence every admissible combination at k has sum lambda_i h(k_i)<=L(k)=h(k), whereas the single-point combination attains h(k). Thus H(k)=h(k). Hole-freeness ensures that a lattice point of conv(A) belongs to A, so exponentiating also interpolates zeros off A. f=exp H has positive finite integral and finite moments because support is compact and H is bounded above by max h. Boundary continuity on all of R^d need not follow for finite supports; the term continuous in the source must not be silently discharged by this construction. Even allowing the standard upper-semicontinuous log-concave convention, covariance control is unproved.

For a simplicial subdivision of this polyhedral roof, let vertices v_i and barycentric coordinates lambda_i(x) describe the simplex containing x (choose boundaries measurably; they have zero volume). Normalize f to a probability law for a random X. Conditional on X=x, choose a vertex Y=v_i with probabilities lambda_i(x). Then

    E[Y|X]=X,
    Cov(Y)=Cov(X)+E[sum_i lambda_i(X)(v_i-X)(v_i-X)^T].

This identity follows directly by expanding (Y-E X)(Y-E X)^T, conditioning, and using sum lambda_i(v_i-X)=0. Thus the covariance increment is positive semidefinite; its trace is at most E[D(X)^2], where D(X) is the diameter of the active simplex. This is a rigorous classical coupling identity, not a source resolution.

The fatal missing identification is the vertex law:

    w_i = (integral lambda_i(x) exp H(x) dx)/(integral exp H).

It is **w**, not p. Fixing H(v_i)=log p(v_i) does not impose w_i=p(v_i). Even on the interval [-m,m] with equal lattice heights and the unit-interval triangulation, w gives endpoint weights 1/(4m) and interior weights 1/(2m), while p gives every point weight 1/(2m+1). The uniform continuous interval has variance m^2/3; the lattice uniform has m(m+1)/3, and the barycentric vertex law has variance m^2/3+1/6. Therefore ignoring the mismatch gives a plainly wrong moment identity, despite bounded cell diameters. This calculation also shows why an O(s) error may be the right size rather than O(1).

One sufficient route would control both (i) E[D(X)^2]=O(s), and (ii) a weighted second-moment discrepancy between w and p, after centering at the discrete mean, of O(s), together with a first-moment discrepancy O(1). Expanding covariances would then give the stronger same-scale estimate. Neither estimate has been proved for arbitrary extensible lattice laws. Regular subdivisions can have long edges, and large discrete covariance does not directly furnish the continuous slice-maxima bounds used by FGR. Infinite support introduces additional integrability, compact-exhaustion, and uniformity requirements. They are not waved away as a limit.

## Two failed alternative constructions and exact corroboration

**Cube jitter** has covariance Cov(p)+I/12, but its density need not be log-concave. For p(-1)=p(1)=1/4, p(0)=1/2, the centered-unit-cell jitter density has values 1/2 at x=49/100, 1/4 at y=53/100, and 1/4 at their midpoint 51/100. Thus f(mid)^2=1/16<1/8=f(x)f(y). All three points lie strictly inside cells; this is not a boundary convention issue. This defeats a proof method, not the source question. The same discontinuity defect persists under products and in nonuniform broad lattice families.

**Gaussian smoothing** of a lattice law does not preserve its prescribed lattice values. Already p=(2/3,1/3) on {0,1} gives smoothed ratio (2a+b)/(a+2b), where a=g(0), b=g(1)>0; equality with the required ratio 2 would imply -3b=0. Nor is a mixture of translates of a Gaussian automatically log-concave. Subsequent affine whitening changes the literal lattice interpolation constraints unless an appropriate lattice-preserving map is available. These observations eliminate direct jitter/smoothing/whitening proofs, not all possible extensions.

**Exact diamond diagnostic.** For uniform p on A_m={(x,y) in Z^2: |x|+|y|<=m}, the canonical uniform continuous diamond has covariance (m^2/6)I, whereas exact summation gives

    Cov_Z(p)= [m(m+1)(m^2+m+1)/(3(2m^2+2m+1))] I.

The difference is m(2m^2+3m+2)/(6(2m^2+2m+1)), between 0 and (m+1)/6, hence compatible with O(s) at s comparable to m. The checker verifies the counts, zero cross moment and rational formulas at m=1,2,3,4,8,16,32,64. This symmetric subclass already has isotropic continuous extensions and receives no nomination or parameter credit. Finite tests do not prove a general interpolation theorem.

## Live registry and access reconciliation

The complete root snapshots at 18:13:38Z were decompressed and checked: Omega 350,197 entries, OpenAI 174,524 entries; hashes agree with the supplied CURRENT-REGISTRIES.json. The saved Omega 222-line delta was included by hash. Refined path search found no exact target Omega path. OpenAI near matches were body-read: LogConcaveQuery is an oracle-sampling comparator, LatticeCovering/LogConcavity proves continuous Prékopa and radial shell bounds, KLS/Convexity/LogConcavity gives the ordinary continuous definition and rpow inequalities, and JetEstimates/Extension concerns cumulant tensor submatrices. None of those actual statements constructs the required lattice interpolant.

Live lawful GitHub HTTP observed OpenAI unchanged at 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Omega had advanced to e50b06adbf73bc8eaa5ae905ad0d7b0d178fe377 (commit 18:21:43Z). The old-to-new public compare returned 5 commits and 2 changed documentation paths, both recorded in live-delta-summary.json; this is below the 300-file API cap. No new matching source path appears. This reconciles the supplied complete tree with a bounded later path delta; it is not a semantic audit of all registry bodies or a worldwide priority claim. Search queries found the original/companion and classical tent literature, not a located full answer; novelty remains unestablished.

Direct StackExchange HTTP 403 was respected; the source body had been available through the ordinary web reader. No browser tab, login, account, posting, contact, upload, proxy or access-control bypass was used. Exact HTTP dates, response hashes, sizes, URLs and failures are in http.json. Sources and read text are preserved locally.

## Remaining gap, objection and falsifier

The full question is unresolved. We have neither an all-family construction with the requested asymptotic covariance control nor a legal family for which **every** interpolating continuous log-concave extension fails almost-isotropy. A bad covariance for the canonical tent alone cannot refute existence, and a well-behaved symmetric finite family cannot prove existence in general.

Strongest mathematical objection: the proposed tent-coupling route lacks control of the induced vertex weights, cell geometry and infinite-support limits; invoking the source's continuous-to-discrete theorem here is circular. Strongest eligibility objection: a general convex interpolation/discrete isotropic-position theorem may already provide the missing estimates, making any eventual short proof routine. The inspected MLE theorem does not supply that bridge; a comprehensive classical literature clearance was not obtained.

A decisive falsifier for the positive claim would be a fixed-dimensional family satisfying the exact lattice log-concavity and diverging almost-isotropic covariance assumptions, plus a proof quantifying over all legal extensions that their continuous covariance condition numbers or relative anisotropy cannot have the source's O(1/s) behavior. A decisive repair of the attempted proof would establish the two transport estimates above uniformly, handle source continuity and infinite support, and reconcile the determinant scales. No such result is claimed.
