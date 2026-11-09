# Independent adversarial review of MathDB 365301

Review date: 2026-11-02 UTC. Recommendation: **HOLD; zero credit**. This is a review, not acceptance. The ordinary counterexample survives. Formalization is plausibly feasible with a literal definition, but it is not a short certificate exercise. Gates: A PASS, B PASS, C QUALIFIED_PASS (planning only), D HOLD, E QUALIFIED_PASS. No child agents, git operations, shared ledger edits, browser tabs, author contact, uploads or publication were used.

## A. Source and MathDB fidelity — PASS

The preserved raw JSONL and results entry identify Conjecture 6.1 of Adlin–Thai–Tiscareno–Tully-Doyle. Both v1 (2024-10-14) and the latest arXiv v2 (2025-11-04), checked live, state the same assertion: for a graph colored z,w and representation computed at vertex i, the contact order equals twice the distance to the closest w vertex. The following paragraph explicitly includes multiple w vertices and predicts equal contact orders on every branch. This is a universal graph/color/root statement, not a particular family. The sentence does not explicitly impose connectedness, nonempty color classes or a z root; the surrounding one-w discussion uses a path-connected z root and w vertex. For fidelity, use the stronger admissibility restrictions in a refutation: finite simple undirected, connected, both colors nonempty, root z. Our graph meets all of these, so the source's degenerate disconnected/root-w cases need not be settled. Arbitrary root selection is authorized by Section 2.3, and color permutations by Lemma 2.4. No extra bipartiteness or tree assumption occurs.

The matrix is M=A-zY-w(I-Y), Y the diagonal indicator of z vertices, and f=(M inverse)_(i,i), not its reciprocal. Section 3 separately denotes 1/f by g. Lemmas 2.1, 2.3 give the inner Pick setting: f is holomorphic on the bi-upper half-plane, has nonnegative imaginary part there and real boundary values wherever defined. For a direct justification, Im(M inverse)=M inverse* diag(Im z,Im w) M inverse is positive definite; the diagonal scalar entry is positive. Use conjugate transpose on the left in this identity. The bidisk inner function is phi=beta composed with f composed with coordinatewise beta inverse, beta(v)=(1+i v)/(1-i v), beta inverse(v)=i(1-v)/(1+v). After reduction its numerator is a unimodular multiple of the reflected stable denominator, with possible harmless monomial factors.

Section 4 studies the singularity at (infinity,0), corresponding to (-1,1) under this beta. Its informal level-curve explanation only writes one branch because that section treats w-degree 1. It does NOT define a competing minimum convention for degree 2. The explicit reference is Bickel–Pascoe–Sola, *Level curve portraits*, Section 3. We independently read its local maximum definition (Definition 2.5) and Theorem 3.1, together with Bickel–Hong Section 3.1 and Remark 3.2 in both the arXiv body and the March 2026 ELA journal body. The convention is maximum local branch order, not minimum or sum. Bickel–Hong's general remark is not restricted to their later one-branch applications. Thus applying maximum here is source-faithful; the source's extra equal-branches expectation is itself contradicted.

The primary geometric definition is infimum distance of the reflected-denominator zero set from the torus, comparable above and below to a power of the first-coordinate distance. Bickel–Hong equation (13) expresses the equivalent lower-half-plane zero-set version. A direct check of that definition below removes dependence on importing the general generic-level theorem into Lean.

## B. Independent mathematics — PASS

`scripts/independent.py` uses its own permutation determinant expansion and a convolution recurrence for the square root of the quadratic discriminant. It does not execute or import either submitted script. Exact SymPy rational expressions are used; all assertions pass (about 55 MiB peak RSS). The installed SymPy is explicitly loaded from its existing local site-packages under `python3 -I`; bytecode writes are disabled. An initial isolated import failed because isolated Python excludes the user site; no package installation was needed.

The matrix obtained directly from the edges and colors gives

N=(wz-w-1)(wz+w-1),
Q=-w^2 z^3+2w^2 z+4wz^2+2wz-w-3z,
f=N/Q.

The polynomial gcd is 1. The two numerator factors are primitive and irreducible as linear w polynomials over Q(z); substituting w=1/(z-1) and w=1/(z+1) into Q gives (2z-1)^2/(z-1)^2 and -1/(z+1)^2. Neither factor cancels. Primitivity also excludes a hidden z-only common factor. This is a genuine degree-2 representation.

Write t=1/z, w=t u and set f=L. Then

F=t(N-LQ)=[L(1-2t^2)+t-t^3]u^2+[-4L-2Lt+Lt^2-2t]u+3L+t.

At t=0, F=L(u-1)(u-3). For every nonzero real L both roots are simple. The square root with initial value 2L supplies convergent analytic branches (the sign choice can be made locally for each L; positivity is unnecessary). The discriminant at zero is 4L^2. The quadratic formula proves exhaustiveness, including that every w root near zero is O(t). Coefficients through degree 6 are independently:

w_(L,1)=t-t^2+t^3-t^4/2-t^5+(17/4-1/(2L))t^6+O(t^7),

w_(L,3)=3t+(3-2/L)t^2+(6-2/L+2/L^2)t^3
 +(9/2-7/L+2/L^2-2/L^3)t^4
 +(15-6/L+9/L^2-2/L^3+2/L^4)t^5
 +(15/4-41/(2L)+8/L^2-11/L^3+2/L^4-2/L^5)t^6+O(t^7).

For distinct nonzero L,H the corresponding differences start with
(1/(2H)-1/(2L))t^6 and (2/H-2/L)t^2. They have orders exactly 6 and 2. Cross-matched branches differ already at degree 1. Ordering by slope gives the source's natural matching. Level 0 and the infinite level are exceptional possibilities, not generic replacements; every finite nonzero real level has the same two branches. Positive levels alone form only an open arc of unimodular levels, not an almost-everywhere set: the submitted write-up should not infer a generic statement solely from that arc. The calculation actually extends to all nonzero real levels and repairs that exposition gap.

Direct geometric check: use the upper-half-plane preserving local chart x=-1/z. The chart t=1/z is fine for jets, but reverses upper and lower half-planes and must not be used silently for domain claims. The reduced local stable denominator is

R(x,w)=x^3[Q(-1/x,w)-iN(-1/x,w)]
 =(1-i x-2x^2+i x^3)w^2
 +(4x-(2+2i)x^2-x^3)w+3x^2-i x^3.

There is no common polynomial component with its conjugate: a common divisor would divide the cleared N and Q; x is not a divisor because R(0,w)=w^2. Consequently this clearing has not introduced a cancellable singularity. The two roots arise by the same analytic construction with L=-i and t=-x. For real x, their imaginary parts are

Im w_1(x)=-x^6/2+O(x^7),
Im w_3(x)=-2x^2+O(x^3).

Thus both roots lie strictly in the lower half-plane for sufficiently small nonzero real x. Their minimum imaginary distance is comparable to |x|^6. This proves contact order 6 by the primary zero-set definition, independent of generic-level semantics. Both roots tend to zero; no other roots are present. Common numerator/denominator vanishing at (0,0), with these different limiting level curves and no common factor, certifies a true rational-inner boundary singularity.

Möbius coordinate changes have nonzero derivatives in the local charts. Explicitly beta(-1/x)=(x-i)/(x+i) has value -1 and derivative -2i at zero, and beta has derivative 2i at w=0. Also 1-|beta(w)|^2=4 Im(w)/|1-iw|^2 in the upper half-plane. Conjugate the lower-half-plane pole roots to numerator roots and apply this formula; denominators and 1+|beta(w)| stay bounded above and away from zero. These identities prove comparability, not merely formal invariance of jets. Output Pick automorphisms relabel real levels; unimodular inner constants do likewise. Multiplying the Pick f by -1 is not an upper-half-plane preserving normalization and is not needed. Reciprocal transforms must use the appropriate sign, e.g. -1/f; they again relabel generic levels.

Other singularities do not lower this local order. The resultant Res_w(N,Q)=-(2z-1)^2 shows the only finite real common zero is (z,w)=(1/2,-2). At z=infinity the only common boundary zero has w=0; for w=infinity the leading z polynomials of N and Q have no common finite root, and the joint infinity chart has nonzero leading Q coefficient. Thus another singular point cannot be mistaken for the one tested. No exact contact order at the other point is needed. If someone instead interpreted contact globally as a maximum over points, it is at least 6 and still cannot equal 2. The source Section 4 explicitly uses the local (infinity,0) interpretation.

Calibration: our code reconstructs Example 4.3 directly as two root-to-w paths of lengths 2 and 3 and recovers the printed rational function and w=2t+2t^3+(2-1/L)t^4+O(t^5), hence order 4. The source's final vertex number in its explanatory sentence is a harmless labeling typo; the displayed matrix/Schur expression is decisive. It also reconstructs Bickel–Hong's initial 4-cycle matrix, recovers their equation (1), and gets w=2t-t^2/L+O(t^3), order 2. Finally the candidate's root is adjacent to both w vertices, so the nearest distance is exactly 1; the entire graph is connected.

## C. Lean feasibility — QUALIFIED_PASS, not a proved endpoint

`SourceContactDefinition.lean` contains proposed literal predicates, definitions only, not a claimed checked theorem. `HasZeroSetContact` expresses the bidisk infimum comparison without an empty-infimum convention: a uniform lower bound for every nearby numerator root and an attained upper bound at some nearby root. It also requires the boundary zero. With q certified to be the reflected reduced stable denominator, this is exactly the source definition. `HasHalfPlaneContact` is its lower-half-plane counterpart for the reduced stable denominator. Neither definition mentions this graph's jets, a selected branch or a presumed answer. The representation-to-polynomial connection is a required theorem, never a free assumption in the final endpoint.

Recommended endpoint: define the universal source conjecture for all finite simple colored graphs and arbitrary roots for which the prescribed local contact is defined, through the actual matrix inverse, reduced bidisk rational-inner representation, and shortest distance. Prove that its restriction to connected graphs with a z root and nonempty w set is false, using this graph. This logically refutes the original universal assertion even if disconnected conventions are left unrestricted. The endpoint must include the chosen graph, coloring, matrix-inverse identity, reduced rational-inner certificate, distance 1, literal HasZeroSetContact at (-1,1) of order 6 and failure of order 2, and hence `¬ SourceConjecture`. A theorem only about F or its jets fails this requirement.

Minimal theorem chain/modules:

1. GraphData: Fin 5 adjacency, simple/connected certificate, colors and root distance 1. MatrixResolvent: adjugate quotient, N/Q, nonvanishing on H^2 and inner Pick behavior, coprimality.
2. SourceContact: the two predicates, uniqueness of the exponent by two-sided comparison, and explicit Cayley transfer from HasHalfPlaneContact to HasZeroSetContact. Define reduced numerator/denominator certificates algebraically so arbitrary common factors cannot inflate order.
3. QuadraticBranches: construct an analytic square root of the normalized discriminant, nonzero quadratic leading coefficient, factorization into two analytic roots, and exhaustiveness. For this example L=-i suffices; avoid general Puiseux/Weierstrass theory and the full generic-level contact theorem.
4. ExactOrders: derive jets with an analytic remainder from the branch equation or radical, obtain Im(w_1)=-x^6(1/2+o(1)) and Im(w_3)=-x^2(2+o(1)), and uniform positive bounds. Use all roots for the lower bound and root 1 for the upper bound. Establish contact 6 and exclude contact 2.
5. Counterexample: construct the reduced bidisk certificate from R and its conjugate, apply Cayley transfer, identify the actual graph representation, and negate the universal conjecture. Strict isolated rebuild and transitive axiom audit remain mandatory.

Read-only mathlib inspection used the existing 2026-10-14 formal checkout, Lean v4.34.1 and manifest revision d13f23b723b8a846827a245b89c10fc7d3f11612. No Lean process was launched, so no compilation or replay is claimed. Analytic/Order.lean already provides `analyticOrderAt`, finite-order factorization, product/power rules, iterated-derivative characterization and `analyticOrderAt_comp_of_deriv_ne_zero`. InverseFunctionTheorem/Analytic.lean provides `analyticAt_localInverse`. A local analytic square root near 1 can be built as the local inverse of s↦s^2 at 1; this avoids any global branch-cut API. Existing bivariate implicit APIs handle differentiability, but need not supply a ready-made analytic implicit branch; the explicit quadratic/local-inverse route avoids this gap. Missing application lemmas include analytic jet-to-real-imaginary estimates, exhaustive local roots after clearing infinity, a reduced RIF certificate for the actual matrix inverse, and the explicit Cayley zero-set comparison. The whole theory of arbitrary contact order is unnecessary, but these bridges are substantial.

Estimated effort, as planning judgment rather than measured promise: roughly 1–3 expert weeks, perhaps 1,000–3,000 lines including source-faithfulness and matrix/domain bridges; risk is medium to high. First spend a bounded 1–2 days on the local analytic square-root/exhaustiveness and imaginary-distance comparison modules. Stop investment if these only yield conditional analytic statements or polynomial jets. The endpoint can reasonably be literal and not a surrogate. It is not yet acceptance-ready and is substantially more expensive than a finite combinatorial certificate.

## D. Prior art — HOLD, bounded search only

Dated HTTP receipts and response bodies are under receipts/ and downloads/. The two live arXiv abstract pages show no version later than source v2 and Bickel–Hong v1. Source v1/v2 Conjecture 6.1 and adjacent discussions were read. Bickel–Hong arXiv and the actual journal PDF, ELA 42 (March 2026), 213–238, were read at the definitions, Remark 3.2, Theorems 1.5/3.5–3.7 with the determinant proof mechanism and Section 4. These remain the one-w setting, do not permit adding another w color through their modifications, and neither refute nor prove this multiple-w conjecture. The journal retains the maximum convention. Its note that t=0 Conjecture 1.4 was resolved refers to the source's ONE-w theorem, not Conjecture 6.1.

Additional actual primary-body review:

- Bickel–Pascoe–Sola, arXiv:1803.04666: Definition 2.5, Theorem 3.1 and adjoining level-curve framework. General local maximum semantics and parametrization, no graph-distance refutation.
- Bickel–Knese–Pascoe–Sola, arXiv:2109.07507v2 (2024 journal version): Theorems 2.12 and 2.19 with adjoining construction discussion. Allows different contact data for general stable polynomials, but gives no unit-weight finite adjacency graph realizing this counterexample.
- Knese, *Rational Inner Functions on the Polydisk: A Survey*, arXiv:2409.14604 (2026 publication metadata): local structure Theorem 0.5.4, local maximum/infimum formulation and adjoining consequences. No graph-distance assertion.
- *On the membership of two-variable Rational Inner Functions in spaces of Dirichlet-type*, arXiv:2512.17388: main-results and Section 3 contact/factorization discussion. No multiple-w adjacency graph result found in the inspected sections.
- *Composition operators and Rational Inner Functions on the bidisc: A geometric approach*, arXiv:2604.20330: Theorem 2.2 and adjacent common-curve theorems, Sections 3.1–3.2. Results on transversality/operator boundedness, not graph distance.
- Knese, *Boundary local integrability of rational functions in two variables*, arXiv:2404.05042, with 2026 journal metadata: introduction, main-theorem discussion and Remark 1.15. This is an actual citing work: Remark 1.15 explicitly cites BOTH graph papers, describing adjacency constructions without a refutation. Its later integrability proofs were not audited in full.

These are targeted statement/body reads, not cover-to-cover proof verification of every paper. OpenAlex title searches and 2024–2026 contact-order search located the above leads. Its `cites` filters returned no indexed citing records for either graph work, despite the actual Knese citation just found; this demonstrates incomplete indexing and is NOT absence evidence. General Google responses were JS/challenge pages; no challenge was executed or retried. Bing responses were irrelevant to the submitted queries and are unusable as novelty evidence. Two guessed author-publication URLs returned 404. These failures are retained candidly.

Unread/not cleared: source journal body (ScienceDirect previously denied, no retry); the 2025 Bickel–Knese–Pascoe–Sola *Stable polynomials and admissible numerators in product domains* body, Hong's 2023 thesis, all other citing or unindexed 2026 works, and remaining companion literature. Prior access prohibitions were respected; no denied publisher/search API routes were retried. No claim of demonstrated worldwide novelty.

Live registries were fetched only through GitHub `/commits/HEAD` as instructed. OpenAI/math remains 4eaee87548250b2682affda7d05d947c05554bae. Omega/the-omega-institute/trureturing is now 440268e282fe97cd7e8d26c931f54f031a839271 (commit 2026-11-02 23:13:11 UTC), advanced from the brief's fec30b7b6ea52ed9c19e0d9dd27c5798df426d41. Its HEAD file list concerns Bajnok–Beatty and plane-word endpoint counts, not this conjecture. The intervening commits were not inventoried: HEAD alone cannot clear their proof bodies. An initial guessed leanprover-community/omega endpoint gave 404; it is not the Omega registry and was corrected using the inherited receipt. Cached expanded-corpus path screens are read-only background evidence, not fresh full-body clearance. D remains HOLD because neither a complete citing-work search nor intervening registry-body clearance has been achieved.

## E. Significance — QUALIFIED_PASS

Conditional on novelty clearance, this is a substantive explicit refutation of a genuine universal research conjecture and its equal-branches mechanism. It is not a color-domain typo, endpoint repair, already-proved one-w parameter instance, or a new count for a helper lemma. The source's Schur complement/path proof and Bickel–Hong's three graph modifications all retain one w vertex. Their one-paragraph combination cannot introduce the second w vertex and derive orders 6 and 2. The general stable-polynomial structure lemmas allow unequal branches, but do not construct this unweighted adjacency graph or settle nearest-w distance. The calculation becomes short once the graph is found; that alone does not make it a routine corollary. Novelty and literal Lean completion remain conditions, not inferred from MathDB's open label.

## Recommendation and next actions

Keep this as an ordinary counterexample candidate with zero accepted credit. First close the listed novelty/body gaps, particularly recent graph-specific citations and the registry interval. Then run the bounded analytic Lean feasibility experiment above before committing to full formalization. If pursued, correct the positive-level genericity explanation and use x=-1/z for upper-half-plane domain claims. Keep the direct stable-denominator proof as the primary formal route. Only root may accept after a literal endpoint, independent fidelity review and clean extracted replay.

All assigned inputs are SHA-256 bound before and after in receipts/input-before.json and input-after.json. Verification is recorded in receipts/input-verification.json. All new artifacts stay in this lane. Each substantive Python computation uses affinity at most two CPUs, CPU limit 120 seconds, and a 6 GiB address-space cap (stronger than the RSS cap); peak computation RSS is recorded. Fetch runs have a 140-second external timeout and per-request timeouts. No background job is left at handback.
