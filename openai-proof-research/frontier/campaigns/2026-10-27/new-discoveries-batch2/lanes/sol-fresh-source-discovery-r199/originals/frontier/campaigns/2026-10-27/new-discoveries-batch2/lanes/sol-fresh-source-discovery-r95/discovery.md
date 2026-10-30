# r95: hyperbolic minimizer route remains unresolved

29 October 2026. Solo, assigned lane only. No complete source outcome, nomination, Lean, paper, or credit. Campaign counts remain 8 additional / 38 total. MMPP historical review and r93 finite/arithmetic work were not pursued.

## Screening, sources, and chronology

The initial all-date screen covered 7,169 files whose names contained SUMMARY, discovery, FINDINGS, PROOF, review, or ledger, without a date restriction. It searched exact authors, identifiers, and family terms before mathematical investment. The expanded final screen covers 7,180 files, without a size exclusion, and records 77 lexical hits in duplicate-screen.json; report-inventory.json hashes every examined file. This is a lexical project audit, not semantic worldwide clearance. The expanded screen also recovers r69's prior exclusion of the planar interior/boundary comparison; it is not a fresh target here. r94's completed Luo Gaussian smoothing lane was read and remains unresolved. Ancestor/batch AGENTS, ledger, NEXT, prior campaign context, upstream identity, catalogue, r86/r90/r93/r94 summaries and root freeze registry record were consulted. No old hold is cleared by these reads.

Three attributed source leads were screened:

1. Holevo–Utkin, arXiv:2603.24017v2, equations (1)–(7): the sharp ratio of the p and 2 norms on real zero-sum vectors, in every dimension and for every positive p. **Exclude public proof.** Zhang, arXiv:2605.05243v2 (21 May 2026), Theorem 2 and the actual proofs in Sections 3–4 give the full endpoint. The multiplier classification excludes three coordinate values through one-variable inequalities, rather than merely testing dimension 200. Both actual PDFs were read. No phase-transition/root wording issue is nominated.
2. Gusakova–Zaporozhets, as attributed in Tokmachev arXiv:2607.08869v1 equation (5): every planar convex body with interior has boundary mean distance strictly greater than perimeter/6, with sharp constant. **Exclude public proof.** Shen arXiv:2608.06470v3 (3 September 2026), Theorem 5.1 and Propositions 5.2–5.3/Lemma 5.4 prove this using tangent-angle measures, projected Gini concavity, and median-of-three comparison. Actual latest proof body read, including strictness and rectangle sharpness. This is in addition to the already excluded interior/boundary comparison; no repetition is credited.
3. **Selected full geometric question:** Hong arXiv:2606.01771v4 (9 October 2026), Question 5.5: for every prescribed positive surface area, characterize all compact convex surfaces in hyperbolic three-space minimizing total mean curvature. Degenerate double surfaces are allowed; mean curvature is the trace convention, extended by curvature measure. Question 5.6 separately asks regularity, strict convexity and axial symmetry. No restriction to smooth, rotationally symmetric, or drum-shaped bodies is assumed here.

Exact URL requests and source bytes are retained in sources and the fetch logs. Latest abstract version histories were fetched. The PDF is the operative source for the numbered questions; no abstract promise is substituted for a theorem. Hong's original Santaló inequality and Guan's sphere/disk envelope are already publicly refuted and were not reinvestigated as discoveries.

## Closest classical and successor mechanisms

Ghomi–Spruck's actual author PDF, Theorem 1.1 and its proof on pages 4–6, evolves a smooth strictly convex surface by harmonic mean curvature flow and makes M²−16πS−2S² nonincreasing in curvature −1. Gauss–Bonnet and Cauchy–Schwarz yield the bound. Hong arXiv:2603.19646v3 (22 June 2026), Theorem 1.1 and Section 3 proof, retains the volume term by iterating auxiliary functions. It supplies

    M² >= 16πS + 2S² + 2 S0(V)²,

where S0 is the sphere area at enclosed volume V. These proof bodies do not identify the minimizing fixed-area shape: eliminating V by its nonnegative lower bound leaves a strict gap. Thin convex neighborhoods of a fixed-area planar disk have volume approaching zero, so a positive area-only lower bound on V cannot repair this step. The theorem is sharp on spheres for the joint area/volume data; that does not make spheres fixed-area minimizers. Hong's selected paper proves this latter distinction explicitly.

Hong's Proposition 1.1, Theorems 1.2–1.3, Section 4 formulas and the curvature-measure appendix were read. Existence, the degenerate disk classification, the C2 positive-curvature sphere classification, the explicit intermediate-area drum improvement, and absence of 0-singular points are already supplied there. None is a new result of this lane. The global shape problem remains a genuinely larger quantifier than optimizing its two-parameter example.

## Sustained route: unequal-cap drums and fixed-area variation

The concrete attempt was to obtain a global minimizer comparison from geodesic-ball truncations. Before asserting any symmetrization, enlarge the source family to independent upper/lower parallel cuts.

Write z=sinh²r>0 and let 0<c_+,c_-<1. In the Klein model take the ball of Euclidean radius tanh r, cut by x3<=tanh(r)c_+ and x3>=−tanh(r)c_-. This is a genuine compact convex body with nonempty interior. Its planar faces are geodesic disks. Put

    D(z,c)=sqrt(1+z−zc²), u(c)=sqrt(1−c²),
    A(z,c)=atan(sqrt(1+z) u(c)/c),
    f(z,c)=zc+D(z,c)−1,
    g(z,c)=2sqrt(z(1+z))c+sqrt(z)u(c) A(z,c).

The curvature-measure calculation is additive over the two faces, two seams, and spherical belt. It gives exactly

    S=2π[f(z,c_+)+f(z,c_-)],
    M=2π[g(z,c_+)+g(z,c_-)].

Indeed each flat face contributes 2π(D−1) to area and zero smooth mean curvature, the belt contributes 2πz(c_++c_-) to area and 4πsqrt(z(1+z))(c_++c_-) to M, and each seam contributes 2πsqrt(z)u A to M. Equal cuts recover the source formulas. This extension pays no source-outcome credit.

At a symmetric drum c_+=c_-=c, make the antisymmetric perturbation c_±=c±e. We have

    f_z=c+(1−c²)/(2D)>0,
    f_cc=−z(1+z)/D³<0.

The analytic implicit function theorem therefore gives a unique even local z(e) preserving the *exact* surface area, with z(0)=z and

    z(e)=z−f_cc/(2f_z)e²+O(e⁴).

It follows directly that

    M(e)−M(0)=2π H(z,c)e²+O(e⁴),
    H=g_cc−g_z f_cc/f_z.

All functions are analytic on the displayed open parameter domain, so these are genuine local geometric variations, with valid Taylor remainders, rather than formal numerical extrapolations.

There is an exact sign obstruction to a universal claim that equal caps minimize M at fixed area. At the fully interior point

    c=5/6, z=14/11,

we have A=π/4, and the Hessian coefficient is

    H=−(266733/590359)sqrt(14)π
      +(2700/53669)sqrt(7)π
      +(308016/1341725)sqrt(14)
      +(875664/590359)sqrt(7) < −1/10.

The strict sign is proved with rational intervals in check.py. Machin's formula and 32-term alternating arctangent sums enclose π; integer-square-root brackets enclose sqrt7 and sqrt14. An independent Taylor expansion of u, D and atan about its argument 1 reconstructs the coefficient. Thus for every sufficiently small nonzero e, the unequal-cap body has the same area and strictly smaller M. The area of the reference drum is 4π(2/33+5sqrt2/6). This is an intended-hypothesis geometric example, but **only a counterexample to our stronger symmetrization route**, not to Hong's question or any stated author conjecture. Its reference symmetric drum was never shown to be globally minimizing. Both perturbed and unperturbed bodies remain axially symmetric, so this does not refute the axial-symmetry question either.

A second attempted reduction imposes stationarity within the symmetric family:

    J=g_c f_z−g_z f_c=0.

stationary-identities.txt eliminates the atan term under this necessary condition. A bounded exploratory scan uses 61 z values and 180 c intervals per z, obtaining six approximate stationary points; their antisymmetric Hessians are positive. This scan is neither exhaustive root isolation nor a stability theorem. It explains why the negative-H witness above cannot simply be advertised as a failure of the optimized candidate. No generic symmetrization theorem, global envelope comparison, all-parameter Hessian sign, or minimizer classification has been proved.

## Exact gap and strongest objection/falsifier

The full missing statement is an area-preserving comparison from **every** compact hyperbolic convex body to an explicitly classified minimizing family, or another argument identifying every global minimizer. Finite-dimensional drum stationarity does not provide it. Even a complete minimization over all unequal-cap drums would not resolve Question 5.5. No known theorem read here forces a global minimizer into that family.

Strongest objection: the entire calculation can be irrelevant to true global minimizers, since it restricts to ball truncations. The rigorous negative-H point only defeats a universal proof shortcut. A concrete same-area convex body below a proposed global envelope would falsify that envelope. A theorem giving all-convex fixed-area domination by a justified model family would close the main structural gap. Neither is obtained here. There is no full source proof or intended-source counterexample, and no PROOF.md.

## Registry scope and honest holds

Fresh default commits/HEAD requests at approximately 19:22–19:23 UTC give Omega a5a8bcdf56019e58c398f6f6d27a3620b896d001 (commit time19:17:38Z), OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a unchanged. The current pinned raw bodies of the baseline lexical matches were fetched; Gini entries concern scalar mean inequalities, and Holevo entries concern other quantum functionals. They do not supply a hyperbolic minimizer classification. These are selected actual body comparisons, not a whole-repository audit. Blueprint is not a Lean certificate.

The complete 18:13 root freeze tree has 350,197 Omega paths and174,524 OpenAI paths. Its later r86/r90/MMPP chain reaches2130bf5… at19:01. r94's d2b0ee6… comparison has90commits/300file cap and55,878-path truncated tree. This lane's d2b0ee6…→a5a8bc… comparison reports2commits/1changedfile; it does **not** fill the inherited missing delta. No git operation or full fresh recursive inventory was performed. Accordingly current registry completeness and global priority remain HOLD; no clearance is asserted.

Offline reproduction: `bash run.sh`. Every Python helper was run through the assigned improved helper_guard.py: AS/group RSS512MiB, CPU210s, wall230s, nominal40ms, BLAS1, with no raised caps. check.py is the exact bounded offline certificate; stationary.py's finite exploratory scan is separately labelled. Logs retain guard exits. No browser, account, contact, posting, upload, git, shared/candidate/ledger mutation occurred. Source bytes and final files are hashed after final writes.
