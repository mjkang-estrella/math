# T338N full-scope proof-correctness review (round 1)

Reviewer role: independent full-scope proof-correctness review of candidate T338N
(frozen author packet `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r89/`).
Review date: 2026-10-18. Scope: correctness of the deduction only. Contribution/novelty
assessment belongs to a separate gate and is not decided here.

## Target statement (verbatim, unchanged)

Every connected, simply connected, complete, noncompact Kähler manifold of finite
complex dimension n >= 1 with nonnegative holomorphic bisectional curvature is
biholomorphic to C^k x (a finite product of irreducible compact Hermitian symmetric
spaces), with k >= 1, the empty compact product allowed. No hypotheses at infinity
(no curvature bound, no volume growth, no pinching).

## Verdict

PASS_FULL_T338N.

The full deduction passes this review. Numbered REQUIRED objections: none (see the
dedicated section; the list is empty, stated explicitly so that "no objections" is a
positive finding rather than an omission).

The verdict is conditional, as the campaign rules mandate, on:
- the stipulated truth of the pinned upstream source theorems (openai/math at
  fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb), in particular the source338 main
  theorem, applied here only at its original hypotheses (complete, strictly positive
  bisectional curvature);
- the named classical theorems the packet invokes as black boxes: de Rham splitting
  (complete case), Berger's holonomy list, Bonnet–Myers, the Hörmander L² estimate,
  the Demailly–Skoda tensor-with-determinant inequality, and the Ni–Tam, Gu/Mok,
  Cao–Chen–Zhu, and Brendle–Schoen results whose statements and relevant proof
  bodies I read directly from the packet's hash-verified private extractions.

No unconditional priority or novelty claim is made or reviewed here.

## Integrity verification performed before reading

1. All nine external frozen anchors from the brief were recomputed byte-identically:
   - MANIFEST.json db21b9d8682eda3a53c240e946fd807c2de1d232b46826c93c52154f6993abfd
   - candidate.md 0d2f59e7f54e6eea77ae28f83430d01cca49c9c5e453a0613741136f848b252a
   - scope-status.json 64591c1c20d8996c30ba3bc7cbd64aee30f4e69a180bbe9157470fde20e24420
   - completion.json 3486d9b23b18f6e1332a487453e8a66ec9d8477a2e41a0c34ce911711280106d
   - nonnegative-flow-bridge.md 1a7b6c8f0e65035146c74e9abd86b7b414be24937997d43a117b8acde5bba882
   - local-null-propagation.md 206a22792d9b3b18af3fe094dcf0fa2fd38da14aca0172cc962533c233a30ba4
   - fixed-time-factorization.md 9aa46f4604251d1cc56ce5fdcd527afc23fd00ae3007469fc311c565ac4ebc9c
   - comparison.md d0908c8396735bf6fe497d73696a3c0464c67593e90f52aacf8a51bbdd51de64
   - reading-limits.md df9063e4226ba2d1a323971a075e7cf6e8afa90076c8b5ba3fe141923b045d88
2. sources/preprints-tree.json matches its external anchor
   eeecc1da… (full hash recorded in the author packet receipts); 13223 entries,
   truncated=false. All private source bodies used below are hash-verified against
   pinned Git blobs through this tree.
3. The author's `verify.py` was read in full before execution, then run with the
   exact prescribed command (`--manifest-sha256 db21b9d8… --repo … --private`):
   PASS_IDENTITY_ONLY, 16 public files, exit 0.
4. Canonical-tree provenance: exactly one uniformization manuscript family in the
   pinned source tree (13 text blobs + paper.pdf); source338 build/main.tex confirms
   the section inclusion order audited below.

## What the deduction is (as audited)

1. Ni–Tam Thm 4.2(i) applied to the given manifold M: M = N x M' with N compact
   simply connected Kähler and M' complete noncompact simply connected Kähler
   carrying a smooth strictly psh function psi with bounded gradient. Nonnegative
   bisectional curvature descends to both factors.
2. Gu Thm 1.1 (compact generalized Frankel, via Howard–Smyth–Wu reduction) applied
   to N: N is biholomorphic to a finite product of irreducible compact Hermitian
   symmetric spaces (CP^{N_i} rank 1 and higher-rank factors). Compactness kills
   the Euclidean factor in Gu's conclusion.
3. On X = M': the nonnegative-flow-bridge module. Replace the source's strict-psh
   Busemann/Richberg weight by the Ni–Tam psi; run the source338 initial-data,
   localized flow, joint-positivity, and Harnack machinery with strict inputs
   removed; obtain a complete Kähler–Ricci flow h_t on X x [0, infinity) with
   nonnegative bisectional curvature, h_0 = g, plus scalar/matrix Harnack control.
4. Local null propagation (Brendle–Schoen Prop 1 localized to compact chart covers
   of parallel-transport paths; CCZ Thm 2.8 reaction inequality on the all-ordered-
   nonzero-pair bundle): the zero set of u(X,Y,t) = R_t(X,Xbar,Y,Ybar) is invariant
   under parallel transport at interior times.
5. Fixed-time factorization at an interior t0: de Rham split (X,h_{t0}); eliminate
   symmetric factors (Ric = lambda h forces lambda = 0, i.e. flat, or lambda > 0,
   i.e. compact, and psi excludes compact complex factors by the Laplacian integral
   contradiction); eliminate SU/Sp holonomy (Ricci-flat forces flat under
   nonnegative bisectional curvature); remaining irreducible nonflat factors have
   holonomy U(d); stabilizer averaging forces any zero pair orthogonal; the CCZ
   reaction vanishing plus the two-plane rotation gives strict bisectional
   positivity of each nonflat irreducible factor at t0.
6. source338's main theorem (complete + strictly positive bisectional curvature,
   no growth hypotheses, per introduction.tex) applies to each such factor: each is
   biholomorphic to C^{d_i}. With the Euclidean factor, X is biholomorphic to C^k;
   noncompactness of X gives k >= 1. The flat-X case is C^k directly.
7. M = N x X gives the target.

## Module-by-module audit findings (changed standing hypotheses)

Standing change: nonnegative (not positive) bisectional curvature; Ni–Tam psi in
place of the source's Busemann/Richberg strictly psh function. I read the full
operative bodies (not statements) of the reused source338 modules from the
hash-verified private copies: preliminaries.tex (479 lines), flow.tex (878),
charts.tex (1070), discs.tex (703), variation.tex (895), ellipsoids.tex (522),
introduction.tex (258).

Strict-curvature input census (full-body reads plus a targeted grep for
strict/positive curvature usage across all five reused modules):

- Exactly one strict input is load-bearing and replaced: the Busemann/Richberg
  strictly psh exhaustion with bounded gradient (preliminaries.tex lines 59–94).
  The Ni–Tam psi supplies exactly this. I verified the one place strictness of the
  weight is actually consumed: the Hörmander L² jet-interpolation step needs, per
  compact set K, a strict psh weight on a neighborhood of K (k dd psi >= c omega
  there for large k). Ni–Tam psi is globally strictly psh, so the per-compact
  requirement is met with room to spare. Demailly–Skoda is used in its
  Griffiths-nonnegative => Nakano-nonnegative (E tensor det E) form; the
  anticanonical bundle has nonnegative curvature from Ric >= 0. No strictness
  needed in either.
- Exactly one strict block is intentionally discarded and not reused: the
  strict-Ricci power contraction and the strict covector bound in charts.tex
  (strict-Ricci contraction in the 80–87 region; static-distortion strict covector
  bound around lines 340–355). The author's retained chart package (moving-frame
  monotonicity, matrix/scalar Harnack, basepoint bound, exit-distance completeness
  argument) was re-derived line by line and uses only nonnegativity.
- All other grep hits for "strict/positive" in the reused modules are unrelated
  (contact strictness in ellipsoids.tex, Fejér kernel positivity, etc.).

Flow module (flow.tex) under Ric >= 0:
- The "initial Ricci positivity" at line 86 needs only Ric(g) >= 0: the displayed
  bound P_t(0) = -R_g + n Delta_g f <= C/L^2 uses R_g >= 0 and the cutoff Laplacian
  bound. Verified.
- The largest-eigenvalue estimate discards -sum lambda_i^{-1} R_g(i,ibar,1,1bar)
  using bisectional nonnegativity only. Verified.
- The cutoff lemma and the scalar comparison proposition are explicitly stated and
  proved on compact domains without any completeness assumption on h_t. Verified;
  this is what the bridge's completeness argument legitimately consumes.

Joint positivity chain (discs/variation/ellipsoids) under nonnegative curvature:
- Cotangent norm plurisubharmonicity uses Griffiths nonnegativity of (T^{1,0}X, g),
  which is exactly nonnegative bisectional curvature. Strictness is unnecessary
  (verified at discs.tex).
- Disc compactness uses completeness of the INITIAL metric g, the finite
  immersion F, global spanning fields, and a removable-puncture lemma assuming
  nonnegative bundle curvature. All available. Verified.
- Deformation-estimate constants depend only on the boundary compacta K_j
  (variation.tex); the supercaloric Q and rho_j tails come from the flow.
- The John-optimizer/contact-resolution and Alexandrov/inf-convolution steps
  (ellipsoids.tex) are compact-domain and curvature-sign-free; the scalar gap
  comparison is applied via the flow module's comparison proposition (no
  completeness). The spatial block of the joint-psh conclusion gives nonnegative
  bisectional curvature of h_t; the time/mixed blocks give the matrix and scalar
  differential Harnack inequalities. Verified.

Completeness of h_t (charts.tex retained portion), re-derived:
- The division steps in the integrated Harnack need R > 0 at positive times. The
  bridge supplies this by the scalar strong maximum principle: R >= 0 solves
  (d_t - Delta_{h_t}) R = |Ric|^2 >= 0 on compact cylinders; if R(x0,t0) = 0 for
  some t0 > 0 then R vanishes on the whole earlier slice, and a finite
  compact-cylinder chain along a path forces R identically zero for all earlier
  times, hence at t = 0, i.e. g flat. For nonflat X, R(·,t) > 0 for all t > 0.
  The chain is finite because the path image and the time interval are compact;
  coefficients are locally bounded since h_t is smooth on X x [0,T]. Valid.
  (Flat X is handled separately and is C^k.)
- Exit-distance ODE: with l_L(t) the h_t-first-exit length from the initial ball
  B_g(o,L), the author uses only interior-supported variations of a minimizing
  first-exit segment (the "contained-variation convention"), so the index form
  needs no boundary terms; existence of the minimizer follows from compactness of
  the closed initial ball and local uniform equivalence of h_t and g (I checked
  the first-exit subsegment argument: interior points lie in D_L, else a shorter
  first-exit subpath contradicts minimality; limit endpoints lie on {d_g = L}).
  The curvature bound R(x,t) <= C_T(1 + d^2)/t along the segment uses the global
  Harnack with d <= l_L; the summed X/JX index form gives
  0 <= ∫ phi^2 Ric(gamma',gamma') <= C/a + C_T(1+l_L^2) a/t; the backward
  difference quotient of l_L against the FIXED minimizer gamma_t yields
  l_L'(t) >= -C_T(1+l_L(t))/sqrt(t) a.e. (l_L locally Lipschitz by local metric
  equivalence), hence 1 + l_L(t) >= (1+L) e^{-2 C_T sqrt(t)}. Every finite h_t-ball
  then has compact closure; Hopf–Rinow gives completeness. No positive-time
  completeness is assumed anywhere upstream; no circularity. Verified.
- Metric monotonicity h_t <= h_s <= g (s >= t) used in the energy estimates comes
  from d_t h = -Ric <= 0 and the flow theorem's cofactor bound. Verified.

Null propagation on the all-pair bundle:
- Gu's compact argument uses the ORTHONORMAL 2-frame bundle; CCZ's Theorem 2.8
  uses the bundle P of ALL ordered nonzero pairs {X,Y}. I confirmed this
  distinction in the survey body (survey.txt 650–1069); it matters because the
  author's zero-set invariance is needed on all pairs, and CCZ's reaction
  inequality is derived for all pairs with no orthogonality or independence
  hypothesis (collinear pairs included). Verified.
- The CCZ reaction inequality d_t u >= L u + c1 min{0, inf_V D^2 u} has c1 > 0
  depending on a curvature bound. The author runs it only on relatively compact
  spacetime regions, where curvature is bounded (h_t smooth), so global
  unboundedness is irrelevant. Brendle–Schoen Prop 1 is local (Omega open in R^n,
  compactly supported field coefficients); the author covers a compact
  parallel-transport path image in P by finitely many coordinate regions, which is
  exactly the permitted localization. BS Prop 2 (compact base) is not used.
  Verified against brendle-schoen.txt 1–240.

Fixed-time factorization (the step I re-derived with the most care):
- de Rham at the single complete slice (X, h_{t0}), holomorphicity of the
  splitting: a parallel off-diagonal (1,0)-component between distinct irreducible
  factors would be a fixed vector of an irreducible nonflat holonomy
  representation; none exist. Sound. (Note: this argument is needed for the
  nonflat factors; on the Euclidean factor the complex structure is parallel
  modulo the flat holonomy and constant complex coordinates are chosen directly.)
- Symmetric-factor elimination: an irreducible locally symmetric Kähler factor has
  parallel Ricci; irreducibility of the parallel Ricci eigenspace decomposition
  forces Ric = lambda h with constant lambda >= 0. lambda = 0: summing the
  nonnegative bisectional components over a unitary basis forces all to vanish and
  polarization gives flatness, excluded. lambda > 0: Bonnet–Myers gives
  compactness, and psi restricts to a strictly psh function on the compact complex
  factor, whose Laplacian has simultaneously positive and zero integral
  (Stokes). Contradiction. Sound; no Helgason-type classification needed.
- SU(d)/Sp(d/2) holonomy implies Ricci-flat (Beauville statement, verified), and
  Ricci-flat plus nonnegative bisectional forces flat by the same summation and
  polarization. So every remaining irreducible nonflat factor has holonomy U(d).
- H(X) > 0 on each such factor: if H(X) = 0 at a point, U(d)-transitivity on the
  unit sphere plus zero-set invariance gives H identically zero at that point,
  polarization gives zero curvature there, and pair-zero propagation along factor
  paths spreads flatness, contradicting nonflatness. Sound (propagation is the
  null-propagation module applied to collinear pairs).
- Stabilizer averaging: writing Y = aX + bZ with Z perp X and averaging the zero
  identities over the U(d-1)-orbit of Z uses the sphere moment identities
  ∫ w_i wbar_j dσ = delta_ij/(d-1); mixed terms vanish, leaving
  0 = a^2 H(X) + b^2/(d-1) sum_{j=2}^d u(X,e_j) >= a^2 H(X), forcing a = 0.
  Sound; the moment identity is verified in checks/rotation_check.py.
- The rotation step, audited at the equation level against survey.txt 965–1044.
  CCZ's curvature evolution for u at a zero pair contains
      u_t = Lu + A + sum_{p,q} |R(e1, e2bar, e_p, e_qbar)|^2,
  where A = sum R_{1 1bar p qbar} R_{q pbar 2 2bar} - sum |R_{1 pbar 2 qbar}|^2
  satisfies Mok's algebraic inequality A >= c1 min{0, inf_V D^2 u} (proved in the
  survey by the phase-averaged perturbation F_q(epsilon), lines 893–958). At the
  interior spacetime minimum: u_t = 0, Lu >= 0, inf_V D^2 u >= 0 (so A >= 0), and
  the sum is >= 0; hence all vanish, in particular
      R(e1, e2bar, e_p, e_qbar) = 0 for ALL p,q.        (bullet 2)
  This full vanishing is what kills every mixed term in the two-plane rotation,
  including the cross component R(e1, e2bar, e1, e2bar): the expansion then
  collapses exactly to u(v,w) = (H(e1)+H(e2))/4 > 0, while holonomy invariance
  (the real rotation lies in U(d)) forces u(v,w) = 0. Contradiction.
  I flag for the record that bullet 2 is essential: with only the first-variation
  kernel identities (R(e_i, e_ibar, Y, Zbar) = 0), the cross component R(e1,e2bar,
  e1,e2bar) survives with coefficient -1/16 and the identity fails; the author's
  argument correctly runs the rotation AFTER the reaction vanishing, at an
  interior positive time, which is precisely where bullet 2 is available. This is
  exactly CCZ's order of operations (survey.txt 995–1044). The exact coefficient
  census, with a negative control that omits bullet 2 and must fail, is
  implemented and run in checks/rotation_check.py.
- The author's sentence "The expansion and zero-reaction mechanism are exactly the
  Gu/Cao–Chen–Zhu proof" is accurate verbatim.

Final application boundary:
- source338's main theorem (introduction.tex: connected noncompact complex
  manifold, complete Kähler metric, pointwise STRICTLY positive bisectional
  curvature, no growth or pinching hypotheses, conclusion biholomorphic to C^n) is
  applied only to factors that are complete (de Rham factors of a complete
  metric), noncompact (psi exclusion), and strictly positively bisectionally
  curved (the rotation step, for all nonzero factor pairs — which is exactly the
  strict hypothesis, including collinear pairs via H > 0). The black-box use at
  original strict hypotheses is permitted by the brief. d = 1 factors: every pair
  is collinear, H > 0 already gives strict positivity; the n = 1 target reduces to
  a Riemann surface and the source theorem covers it.
- Simply connectedness propagates: M simply connected and M = N x M' (Ni–Tam)
  force both factors simply connected; de Rham factors of a simply connected X are
  simply connected. Gu's universal-cover conclusion reduces to N itself.
- k >= 1: X is noncompact by Ni–Tam 4.2(i); X = C^k with k = dim X >= 1. If X is
  flat, X = C^k directly and no flow step is needed.

Liu Thm 1.1 (maximal volume growth) is NOT used anywhere in the deduction; the
packet lists it only as a paid-class boundary in comparison.md. Confirmed by
reading candidate.md and the three modules.

## REQUIRED objections

None. The list is empty: I found no step that fails under the stated conventions,
no missing hypothesis in any external application, no residual strict-curvature
input in any reused module, and no circularity in the completeness or strong
maximum arguments.

## OPTIONAL / presentation items (non-blocking)

O1. nonnegative-flow-bridge.md §4 compresses the strong maximum argument to one
    sentence ("finite chain"). A manuscript should write the slicewise
    open-and-closed argument with backward time propagation explicitly, since the
    flow is only one-sided smooth at t = 0 (harmless here: the chains run at
    positive times).
O2. Bridge §1's canonical-section bullet says "upper linear bound on psi"; the
    mean-value step for e^{-k psi} on the unit ball uses the two-sided bound
    |psi| <= C(1+r), which the packet does state elsewhere (bounded gradient).
    Cosmetic wording.
O3. fixed-time-factorization.md compresses "H identically zero at p plus
    propagation gives flatness" into one sentence; the correct chain is
    polarization at p (Rm(p) = 0) separately from zero-pair propagation to other
    points. Content correct as argued; worth one extra line in a manuscript.
O4. The Berger-list sentence "leaves U(d), SU(d), or Sp(d/2)" should note d = 1
    separately (only U(1)); the author's d = 1 case is already handled by the
    collinearity remark. The SU(2) = Sp(1) overlap is immaterial since the
    Ricci-flat elimination is uniform.
O5. comparison.md's novelty boundary (the Ni–Tam Remark 4.1(a) factorization and
    the CCZ bounded-curvature Theorem 2.8 are adjacent literature) is accurately
    drawn; whether the assembled unbounded-curvature statement is new to the
    literature is for the contribution reviewer, not this audit.

## Reading limits (precise statement)

Full-body reads (every line): the nine anchored packet files plus README.md,
source-receipts.json, primary-receipts.json, interface-results.json,
mechanism-checkpoint.md, check_interfaces.py, verify.py; private source338
preliminaries.tex, flow.tex, charts.tex, discs.tex, variation.tex,
ellipsoids.tex, introduction.tex, build/main.tex.
Statement-and-proof-region reads: private/ni-tam.txt lines 1755–1864 (Thm 4.2(i)
statement, proof, Remark 4.1); private/gu.txt lines 1–120 (Thm 1.1 and proof
skeleton); private/survey.txt lines 650–1069 (CCZ Thm 2.8 full proof including
the Mok inequality derivation and rotation); private/brendle-schoen.txt lines
1–240 (Props 1–2 and localization context); private/beauville.txt lines 74–198
(de Rham complete case, Berger list, SU/Sp Ricci-flatness); private/liu.txt
lines 1–120 (statement only; confirmed unused); berger.txt spot check at
line 2032 (Ch III §9 Thm 3, imperfect OCR as the author flags).
NOT read (by design, and not needed for this verdict): source338 dynamics.tex and
uniformization.tex bodies (the source's main theorem is used as a stipulated
black box at its original strict hypotheses; only its statement in
introduction.tex was read); Berger's full classification proof; the original de
Rham and Mok paper bodies (modern statements verified via beauville.txt and the
survey instead). No other source338 module, companion paper, or external reference
was consulted. Detailed file-by-file record: reading-limits.md in this directory.

## Provenance and credits

- Frozen author packet and its evidence: fresh-analytic-discovery-r89 (author
  agent), used under the campaign's read-only convention; all nine external
  anchors verified byte-identical before use.
- Source theorem and proof modules: pinned openai/math at
  fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, stipulated true per campaign rules;
  bodies hash-verified against pinned blobs via sources/preprints-tree.json.
- Primary interfaces: packet's private extractions with receipts (ni-tam, gu,
  survey=CCZ, brendle-schoen, beauville, liu, berger), spot-verified against the
  pinned tree by the author's verifier, which I read and ran.
- This review's seal: MANIFEST.json in this directory (SHA256 of every file);
  verify.py here is an independent read-only re-implementation (not copied from
  the author's script) with positive and reason-checked negative controls;
  checks/rotation_check.py is an independent exact-arithmetic control for the two
  algebraic identities the deduction hinges on. No nested agents were used; no
  commits, uploads, or shared-ledger edits were made; writes are confined to this
  directory.
