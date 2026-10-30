# T088P133 independent substantial-contribution review, round 1

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Reviewer author of original prose: Myeongjin
Kang (no affiliation), CC BY 4.0; original code MIT. Role: contribution review only, CONDITIONAL ON CORRECTNESS,
at the ENTIRE unchanged frozen scope. No correctness verdict, acceptance, count, priority or worldwide-novelty
finding is assigned here; a separate adversarial correctness review has not been dispatched at the time of
writing. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true, including its operative proof
operations.

## Verdict

**SUBSTANTIAL** (conditional on correctness), at the unchanged bounded-class scope.

After the strongest actual reduction (FHLX Section 4 in its real v1 text, plus the project's r132 route R1–R4
and (★), which the author re-proves completely and explicitly credits as routine), the unpaid obligation was a
specific sharp inequality in five real parameters whose equality set is a boundary curve: r132's (★) at n = 4,
including strictness. r132 had identified exactly this as its main open gap and abandoned it ("no analytic proof
found"). The author pays it with a genuine new bridge: a conditional-parts convex-order (HNBUE/Laplace)
majorization of the exponential expectation, an affine-in-scale separation that reduces (★) to the scale-free
two-sided inequality (S)_n, and an exact rational-coefficient certificate proving (S)_4 for all ten sign
patterns with strictness. The middle inequality (S)_n — D(b) P(W_b > 0)^2 <= (n+1) E W_b^+ for sums of
independent exponentials — is itself a new sharp inequality located nowhere in the literature searched, true
exactly for n <= 4 and false for n >= 5, so it captures a real dimension threshold rather than generic slack.
No prior statement of the theorem, of (S)_n, or of the bridge was found in the actual primary bodies or the
bounded searches recorded below; REDISCOVERED is therefore not warranted within those limits. The individual
ingredients are classical (see Section 4); the verdict rests on their integration into a mechanism that closes
a recognized open case of Brannen's problem, not on any single step.

## 1. Frozen claim reviewed (entire, unchanged)

Frozen statement SHA-256 86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354; proof SHA-256
971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84 (bound through the authenticated manifest);
detached author anchors FINAL 4656a93d80d1b67f4d349f3f95382ab8b03e644e45ad61b22629a86bd5c2cd09, MANIFEST
9ab6adfb17b4e612ad8bee1175109c15b73a1975b67dcc4c580dd955e3306324, REPORT
3659f82ea364b41303f4097e7df0d12ef380cab5a2d43b0f6bc39ed1405d49fd. All matched the actual bytes at review
start and again at sealing; the author root was never written.

**Theorem (verbatim scope).** Every convex polytope K in R^4 with non-empty interior and at most 6 facets
satisfies V_4(ΠK) <= (160/3) V_4(K)^3, with h_{ΠK}(u) = V_3(K|u^perp), equality if and only if K is a
simplex. The scope explicitly includes nonsimple, degenerate-Gale and repeated-knot six-facet polytopes and
excludes general convex bodies, 7+ facets, and dimensions 5–8. This is a bounded-class partial case of
Brannen's conjectured reverse projection inequality, not a solution of the general problem, and it is labelled
as such throughout the author packet. This review assesses exactly that scope: no narrowing, no renaming, no
substitute target.

## 2. Strongest actual reduction and what was unpaid

**Strongest primary antecedent, independently obtained.** FHLX (Feng, Hu, Liu, Xu, *On the Reverse Projection
Inequality*, arXiv:2610.13953v1, 2026-08-16; only version per the arXiv abstract page). I downloaded the actual
e-print source, PDF and HTML (hashes and sizes in work/primary-acquisition.json) and read the full TeX body:
introduction and Theorems 1.1–1.3 (lines 157–265), preliminaries (267–374), the dimension-3 equality
classification (375–990), and Section 4 (991–1425) plus bibliography. Section 4's operative content is:
Prop. 4.1 (transfer: P_n(Q) >= n^n V(S) V(P_F C_m), a LOWER bound at a fixed λ), Prop. 4.2 (codimension-one
product V(S)V(P_F C_m) = D(a) f_a(t)/(m-1)!, so a counterexample needs D(a) f_a(t) > (m-1)^2), Lemmas 4.3–4.4
and Prop. 4.5 (the n = 9 section violation via ∫|h| < ∫h^2 on an 8-cube), and the lifting (4.19)/Prop. 4.6 to
all n >= 9. The paper proves NO upper bound anywhere, gives NO positive result for any small dimension or
restricted facet class, and explicitly leaves 4 <= n <= 8 unresolved. Its counterexamples live in exactly the
frozen class (n-polytopes with at most n+2 facets). So the frozen theorem is not a corollary, special case, or
displayed consequence of FHLX.

**Strongest project antecedent.** r132 (PREFREEZE, no nominee) derived at sketch level: R1 (equality form of
Prop. 4.1 via the Minkowski equality case at λ* proportional to support numbers), R2 (universality of the
row-space/Gale model), R3–R4 (coarea + Gamma–Dirichlet exponential representation; for m = n+2 the B-spline
form sup P_n/c_n = sup_a D(a) ||M(·|a)||_inf / (n+1)^2), and the global normal form (★):
(1 + D(b)/(2(n+1))) E exp(-W^+/(1+c) - W^-/(1-c)) <= 1 for all c, b. r132 listed "prove (★) for n = 4..8" as
Gap 1 (main unpaid obligation), found only float first-variation evidence, and closed with no nominee. Its
brief explicitly allowed a rigorously labelled bounded-facet advance. I read r132's report, notes and parent
intake in full.

**The author's credited reduction.** Lemmas 1–4 and Proposition A of the author proof complete R1–R4/(★) with
full proofs (attainment of the maximum at t*, continuity of the density versions, the normal form
Ψ(α, b) = (1 + D(b)/(2(n+1))) E exp(-W_b^+/α - W_b^-/β), b ∈ [-α, 2-α]^n). I agree with the author's own
assessment: this is the equality case of FHLX's own argument plus standard Gale/coarea/Lukacs steps — expert
assembly, not a new result, and it is claimed as such. The reviewable contribution begins after it.

**What was unpaid after the strongest reduction.** Prove (★) at n = 4 for all α ∈ (0,2) and all b ∈ R^4 \ {0},
with strictness. This is a sharp inequality (equality holds on the boundary curve b = 0, the simplex locus) in
five real parameters, involving the law of a linear combination of independent exponentials. No located
literature provides a tool that closes it: there is no known sharp bound of B-spline maxima weighted by the
pairwise knot-distance sum D(a) (searches in Section 6), no few-facet classification route computes projection
volumes at the sharp constant (the class has continuous moduli; the dual 6-vertex 4-polytopes have finitely
many combinatorial types but the functional varies within each), and the pinned Source P product test evaluates
only the two product points T_2×T_2 and T_1×T_3 in the class (both give R_4 = 36 < 160/3 — two points, not
the class).

## 3. The new bridge (the actual contribution)

(i) **Convex-order comparison (Lemmas 5–6).** W_b has a log-concave density (Prékopa), so its conditional
positive and negative parts satisfy the HNBUE Laplace bound E e^{-sX} <= 1/(1 + s E X). As a fact this is
classical reliability theory — Klefsjö, Naval Res. Logist. Q. 29 (1982) 331–344 characterizes HNBUE through
the Laplace transform, and Klefsjö, J. Appl. Probab. 20 (1983) 615–626 defines the larger L-class by exactly
this inequality (abstracts retrieved via Crossref; bodies not read) — and the author reproves it
self-contained rather than claiming it. The operative move is its APPLICATION: it collapses the
infinite-dimensional expectation in (★) to a rational function of the three moments (p, P, N) and α, namely
Ψ <= (1 + d)[p α/(α + A) + (1-p) β/(β + B)]. No use of stochastic-order majorization against this geometric
problem was located in the literature or the project history.

(ii) **Affine-in-scale separation (Proposition B).** After the comparison, the deficit splits into two
brackets and the scale of b enters affinely; taking the worst endpoint α reduces Ψ < 1 to the scale-free
condition (S)_n for b and -b, with strictness tracked. This is a page of elementary algebra, but it is the
decisive structural step: it identifies a provable sufficient condition, and it is honest about its own cost —
the separation is lossy, (S)_n fails for n >= 5 (the corner ratio tends to 2(n-1)^2/(n(n+1))), so the method's
success at n = 4 is an exact fit at the boundary of its validity, not a consequence of loose technique.

(iii) **Exact certificate for (S)_4 (Proposition C).** D(b) P(W_b > 0)^2 <= 5 E W_b^+ for all b ∈ R^4, strict
when b has entries of both signs. Proof: order/sign parametrization by gap variables, classical
partial-fraction formulas for p and E W^+ (Lemma 7, proved in the packet), exact division through the
Vandermonde, clearing to a polynomial T in Q[x, y] per sign pattern, and exact nonnegativity of all
coefficients in each of the ten patterns (minimum nonzero coefficient 2), with a forced positive monomial in
the always-positive gap variables giving strictness, and continuity extending from the dense distinct-entry
locus (repeated knots and zeros included). The script checks the partial-fraction identities at random
rational points exactly and includes a negative control (rejects (S)_5 at pattern (4,1,0), min coefficient
-6). I re-ran certificate.py on a copy in this root: all ten patterns PASS, negative control behaves as
expected (artifact-level confirmation only, not a correctness audit). (S)_4 is a new sharp inequality for
linear combinations of independent exponentials; no prior statement was located, and its truth boundary
(n <= 4) matches the geometric content.

(iv) **Equality characterization.** Lemma 4' (b ≠ 0 for a genuine 6-facet polytope, else two facets share a
normal) plus the strictness in (iii) yield equality iff simplex across the whole frozen class, including
nonsimple and degenerate-Gale members. In dimension 3, the analogous equality characterization was a separate
paper's main theorem (FHLX Thm 1.2); here it comes out of the same mechanism.

## 4. Why not TECHNICAL; why not REDISCOVERED; calibration

**Not a routine composition.** The campaign criteria exclude results whose conclusion follows by composing
located statements. Here no located statement or combination yields the theorem: FHLX supplies only the lower
bound and the n >= 9 counterexamples; the equality-form reduction is the author's completion of r132 (credited,
routine); the closing steps (i)–(iii) combine a classical reliability bound, a new separation, and a new
certified inequality in a way found nowhere. The project record shows the exact gap was attacked one round
earlier and abandoned as unproven. A finite certificate and a short proof are not categorically technical under
the unchanged criteria; the question is the nonroutine operation after the strongest reduction, and it exists
here: the recognition that conditional HNBUE majorization plus scale separation reduces the B-spline maximum
problem to a scale-free inequality that is true and certifiable exactly at n = 4.

**Not REDISCOVERED.** REDISCOVERED requires a prior actual statement. Bounded searches (Section 6) found no
statement of the frozen theorem, of (S)_n, of the HNBUE-to-Brannen bridge, or of any sharp upper bound for
Brannen's ratio in dimension 4 beyond simplices. If such a statement later surfaces (most plausibly in B-spline
or exponential-sum literature I could not reach), the verdict should be revisited; that is a disclosed limit,
not an UNRESOLVED analysis.

**Calibration within the campaign.** This sits with the SUBSTANTIAL precedents in which the inherited
machinery was extensive but the residual estimate/bridge was new and sharp (t205m: uniform multiplicity floor
over an inherited recursion, "SUBSTANTIAL (narrow)"; t117q: a new selection bridge where the source step was
unavailable). It is unlike the TECHNICAL precedents in which the claimed operation was a literal prior
statement or a direct classical transfer (t184i134: the operation was Kang's Lemma 2.2; t106o133: an archived
routine transfer). The contribution here is narrower than a full new theory: it is one bridge plus one
certified inequality, at a bounded-class scope. The verdict is SUBSTANTIAL rather than borderline-technical
because the bridge closes a recognized open case of a named problem (the minimal-facet counterexample class at
the first open dimension), with sharp constant and full equality characterization, and because the auxiliary
inequality (S)_n isolates a genuine threshold phenomenon.

## 5. Honest residual limits (not verdict changes)

- Every ingredient is individually classical or mechanical: Prékopa log-concavity, HNBUE/L-class Laplace
  bounds (1982–83), hypoexponential partial fractions, polynomial nonnegativity certificates. A reader who
  weighs "no new tool" heavily could argue TECHNICAL; my judgement is that the integration and the new sharp
  inequality (S)_4 are the nonroutine content, and the criteria ask for exactly that identification.
- The proof of (S)_4 is computer-algebra (exact rational arithmetic over ten patterns). It is exact and
  includes a negative control, but it is a certificate, not a conceptual proof of why n = 4 is the boundary.
- Scope is one dimension and one facet count; nothing follows for 7+ facets or n = 5..8 (where (S)_n fails and
  the unseparated condition is numerically plausible but unproved).
- Correctness is NOT assessed here. The certificate interpretation, the reduction details, the boundary and
  strictness arguments, and the equality analysis all require the separate correctness review.
- Chronology note: the author's frozen record discloses that the proof sketch and the exact auxiliary
  certificate existed before the freeze; the proof text is post-freeze. This is preserved as disclosed, not
  re-certified.

## 6. Comparison sources actually consulted (versions, extents, failures)

- FHLX arXiv:2610.13953v1: e-print source, PDF, HTML and abstract page downloaded 2026-10-20 into
  private/primary; full TeX body read (see Section 2). The I43-retained text the author used matches the real
  v1 in the operative Section 4 displays (D(a) f_a(t) > (m-1)^2, complementary-minor identity, Γ_0, lifting
  4.19), spot-checked line by line.
- Saroglou, *Volumes of projection bodies of some classes of convex bodies*, Mathematika 57 (2011) 329–353:
  the author's host (myweb.uoi.gr) still fails TLS verification (reproduced, not bypassed); an archived copy
  of the same author PDF was obtained via web.archive.org (snapshot 2026-02-09, 30 pages). Read: abstract,
  introduction, Theorems 1–2, Corollaries 1–2 (3-dimensional zonoids, cones, double cones), and Section 7
  concluding remarks (dimension-3 statements; the d-dimensional zonoid problem noted as open). Not read line
  by line: interior proof sections 3–6. No dimension-4 or few-facet upper bound is present.
- Saroglou, *On the shape of a convex body with respect to its second projection body*, arXiv:1409.4347v2:
  e-print source downloaded; introduction read, body searched for facet/simplex/dimension-restricted upper
  bounds; the content is dimension-3 inclusions and lower-bound reductions. No overlap.
- Brannen 1996 (Mathematika 43, 255–264, DOI 10.1112/S002557930001175X) and Brannen 2005 (Adv. Geom. 5):
  bodies NOT obtained (Wiley 403, Cambridge 500, author page 403). Known from FHLX's introduction, Saroglou
  2011's introduction, and the Crossref/Cambridge abstract snippets: the 1996 paper disproves Schneider's
  symmetric conjecture and conjectures the simplex maximum; 2005 treats three-dimensional classes. Neither is
  reported anywhere as containing a dimension-4 upper bound.
- Chen–Feng–Li–Xi–Xu 2026 (MathSciDoc 2608.23001): body not located (the MathSciDoc URL pattern did not
  resolve to the paper). Its scope is dimension 3 (quoted as Thms 1.1–1.2 in FHLX, whose introduction I read
  in the original).
- Classical stochastic-order facts: Crossref metadata and abstracts for Klefsjö 1982 (NRL 29:331–344) and
  Klefsjö 1983 (JAP 20:615–626) confirm Lemma 6 is the classical HNBUE ⊂ L Laplace characterization; bodies
  not read. Barlow–Proschan not consulted.
- B-spline/divided-difference extremal literature: three bounded web searches (Curry–Schoenberg sup bounds,
  knot-distance weighted maxima, density-at-zero bounds for exponential sums). No sharp D(a)-weighted B-spline
  maximum bound and no (S)_n-type inequality located.
- Pinned sources: all 13 .tex/.md blobs of the two pinned preprints (product counterexample; Petty companion)
  independently fetched from pinned raw URLs and authenticated against the complete tree (13223 entries,
  truncated=false, SHA-256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b) by git blob
  SHA-1 and size — all match (work/upstream-acquisition.json). Source P main.tex read in full (facet formula,
  product identity, simplex value c_d, T_10×T_10 counterexample, exponential excess): at n = 4 the product
  test gives only the two points R_4 = 36; no class statement. Petty companion: main.tex, introduction,
  conclusion, consequences read, sections 02–05 searched for any upper-bound/few-facet/Brannen content — it is
  a lower-bound paper; no overlap. lean/docs/088.md at the pin and at the newer commit adc7f124… are identical
  (1964 bytes); it records only the Petty lower bound and the n = 20 counterexample.
- Project history (actual bodies): I43 §1.3 (RP4 parked after exact simplex-product tests for n = 4..8; T_2×T_2
  and T_3×T_1 give 36 < 160/3), r112 research-report 088 paragraph (product optimization not fresh), r131
  notes (UNSEALED; numerical n = 4 vertex search peaking at float noise 1 + 4e-15), r132 report/notes/parent
  intake (in full), and the r133 author packet (FROZEN-THEOREM, proof, report, reading-limits, notes in full;
  certificate.py and geometry_control.py read and re-run on copies). No project antecedent of any n = 4 proof,
  of (S)_n, or of the HNBUE bridge.
- Project alias searches (rg -uu, hidden and ignored included, no size cutoff; exclusions: active
  fresh-structural-discovery-r135 and t164f99-contribution-r1, this root, .git): "HNBUE" occurs only in r133
  and its parent; "log-concave density"/"Laplace bound"/"stochastic order"/"hypoexponential"/"sign pattern"/
  "Curry–Schoenberg"/"B-spline"/"D(b)" hits outside r132/r133 are copied corpora or unrelated families; the
  operative 088 hits are I43/r112/r131/r132 as listed. The author's earlier broad 1692-hit query was not
  re-run in full; my two narrowed passes cover the claimed-mechanism aliases.
- Bounded web searches (2026-10-20): six WebSearch queries (reverse projection inequality n+2 facets;
  Brannen conjecture dimensions 4–8; Schneider problem follow-ups; B-spline knot-distance bounds; Klefsjö
  Laplace class; density-at-zero of exponential sums) plus targeted fetches. Findings: no dimension-4 result,
  no few-facet class result, one irrelevant 2017 "Brannan conjecture" (a different problem), and the
  DeepMind formal-conjectures issue recording only the pinned n = 20 product counterexample.

## 7. Positioning requirements for any later manuscript/acceptance record (do not change the verdict)

- PQ1. Keep the bounded-class labelling exactly: 4-polytopes with at most 6 facets. Never present this as
  progress on the general 4 <= n <= 8 problem beyond that class.
- PQ2. Novelty wording: "new to this project; no antecedent found in the bounded searches recorded". No
  "first" or worldwide-priority phrasing.
- PQ3. Credit: FHLX §4 for the transfer/lower bound and counterexample class; r132 for R1–R4 and (★);
  Klefsjö 1982/1983 (and the HNBUE/L-class literature) for the classical status of Lemma 6.
- PQ4. Present Proposition C transparently as an exact computer-algebra certificate (ten sign patterns,
  rational arithmetic, negative control), and keep geometry_control.py labelled as a float diagnostic.
- PQ5. State that (S)_n fails for n >= 5 and that the unseparated n = 5..8 condition is unproved.

## 8. Evidence and integrity (this review)

- Author inputs: all 39 hashed input files (author root, parent root, common brief, AGENTS.md, upstream.json,
  preprints-tree.json) SHA-256 recorded at start (work/input-hashes-start.txt) and re-verified unchanged at
  sealing; the detached author anchors FINAL/MANIFEST/REPORT and the frozen/proof hashes match the actual
  bytes. Two parent-side files (commit-validation.json, contribution-r1-dispatch.json) were added by the
  parent after the start snapshot; recorded in work/parent-late-additions.txt; all originally hashed files are
  unchanged.
- Copied controls in this root (artifact checks, not mathematical gates): author verify.py on a full copy
  reports PASS files=24 directories=14 against the detached anchors; certificate.py re-run reports
  CERTIFICATE PASS (ten patterns, identity checks, strict monomials, negative control rejects (S)_5);
  geometry_control.py re-run reports GEOMETRY CONTROL PASS (40 random 6-facet 4-polytopes, direct vs formula
  agreement to 1e-10, max ratio 0.999891 < 1). Originals were never executed or modified.
- This root only: all downloads, scratch, controls and outputs were written inside
  frontier/campaigns/2026-10-14/t088p133-contribution-r1/. No nested agents, no git/shared-index writes, no
  publication/uploads/contacts/browser UI, no formal/manuscript/release work. Private primary/upstream bodies
  remain local under their original rights, separate from this review's original prose (CC BY 4.0) and code
  (MIT).
