# r618: independent focused review of MathDB 338366 (BRT Conjecture 4.1)

Reviewer: Claude (claude-opus-5-5), lane `claude-mathdb-curvature-prior-review-r618`.
Scope: the literal Conjecture 4.1, an independent check of the r602 candidate P1, and the
Bai–Lu–Yau published-object gate. No Lean, manuscript, alternative hypothesis or family search.
Recommendation: **EXCLUDE (no credit).** This is not an acceptance claim.
Integrity PASS (see `verify.py`) is not a mathematical or novelty PASS.

## 0. Bindings before reading

Bound at 2026-10-31T17:09:24Z (`initial-bindings.tsv`, `initial-bind-time.txt`) before any
scientific or administrative summary was read:

| file | size | sha256 |
|---|---|---|
| r617 manifest.json | 26036 | b63599f4…e77501 |
| r617 focused-assignment.json | 266 | b751f519…c58125 |
| r619 manifest.json | 10108 | a822fe2b…65b961 |
| r619 focused-assignment.json | 266 | b751f519…c58125 (byte-identical to r617) |

Read-only intake checks (own code; neither upstream `verify.py` was run):
- r617: 125/125 payloads match hash and size, no extra files beyond the 2 excluded paths.
- r619: 53/53 match, no extras.
- Every `frozen/` copy is byte-identical to its live original (r617 116/116, r619 42/42).
- r304 (6/6) and r363 (94/94) manifests also verify.
- r304 `accepted-exclusions.json` has no entry for 338366. The lane-wide grep hits were numeric
  coincidences.
- r363 is the Cayley 364119 exclusion and does not concern 338366. Its principle applies here:
  when a primary body already supplies the literal negation, the case is a "complete
  source-adaptation exclusion, not a claim that a separately labelled refutation was previously
  published".

The current r619 adjudication for 338366 is `HOLD_FOCUSED_SOURCE_PRIOR_REVIEW`, credit 0.
Counts are unchanged at 9 additional / 39 total / next 40. All external refs are in
`flat-bindings.json` (22 flat refs, no copies).

## 1. SOURCE verdict: PASS (arXiv v2 read; journal body unread)

Fresh retrieval at 2026-10-31T17:10Z with generic headers (`fetch-log.tsv`). Each PDF was hashed
before extraction, and each derived text and image was hashed before reading
(`derived-bindings.tsv`).
- `arXiv:1802.01952v2`: PDF sha256 `ea6ca026…a1e296`, 404998 B. Byte-identical to r602's cached copy.
  The abstract page lists v1 (2018-02-06) and v2 (2019-10-13). v2 is the latest version, and
  the arXiv page carries no journal-ref.
- Journal (Crossref, `fetched/crossref/brt.json`): *IMRN* 2021(22) 17091–17139,
  DOI 10.1093/imrn/rnz305, online 2019-12-09. The IMRN body is **not read**: the DOI resolved to
  an academic.oup.com Cloudflare challenge (HTTP 403), and I stopped with no retry.

Literal text read in `derived/1802.01952v2.layout.txt`:
- **§2 standing assumptions (lines 160–170).** Edges are 2-element subsets, so graphs are simple.
  "A finite graph is one where V is a finite set." "For the rest of this work, we will only
  consider connected graphs."
- **Measure (lines 239–249).** µ_x(x)=1/2, µ_x(v)=1/(2d_x) for v∼x, and 0 otherwise.
- **Definition 2.1.** κ(x,y)=1−W₁(µ_x,µ_y)/d(x,y).
- **Lines 255–258.** "When p ≥ max{1/(d_x+1), 1/(d_y+1)}, the optimal transport plans and the
  value κ(x,y) vary linearly with 1−p [16]". Here [16] is Bourne–Cushing–Liu–Münch–Peyerimhoff,
  *Ollivier–Ricci idleness functions*.
- **Theorem 2.1 (Ollivier), with proof in the text.** A lower bound k on neighbouring pairs
  implies the same lower bound on all pairs (triangle inequality for W₁ along a geodesic).
- **Theorem 4.4.** For d-regular G with κ≥k on all pairs, |S_{i+1}| ≤ ((d+1−2dk)/2)|S_i| for i≥1.
  Finite graphs are explicitly in scope of §4.2 (the remarks at lines 600–606 use "Because G is
  finite").
- **Example 1.** T_p is the infinite p-regular tree and T_p^q is the q-fold Cartesian product,
  which is pq-regular.
- **Conjecture 4.1 (literal).** "Let G be a pq-regular graph so that if u,v∈V(G), then
  κ(u,v) ≥ (2−p)/(pq). Let x∈V(G) and y∈V(T_p^q). Then for any i≥0, one has
  |dist_x^{-1}(i)| ≤ |dist_y^{-1}(i)|." The text continues: "A case of this conjecture is that
  the d-dimensional lattice T_2^d is conjectured to have the fastest volume growth for any
  2d-regular graph with curvature lower bound 0."

Quantifiers:
- G is simple, connected and pq-regular, finite or infinite.
- The hypothesis is κ ≥ (2−p)/(pq) for all u ≠ v; κ(u,u) is undefined.
- The conclusion is required for all x, y and all i ≥ 0.
- At p=q=2: G is 4-regular, the bound is κ≥0, and T_2^2=ℤ² has |S_i| = 1, 4, 8, 12, …

The MathDB record (frozen r617 copy of `assigned-records.json`) reproduces this statement
faithfully, writes κ as "the graph curvature" and cites arXiv:1802.01952.

Discrepancy and limit: whether the IMRN version keeps Conjecture 4.1 verbatim is **unverified**.

## 2. Published object: Bai–Lu–Yau, Theorem 11 / Figure 35

Fresh retrieval of `arXiv:2103.00941v2`: PDF sha256 `9a647048…ef3a45`, 2100380 B, byte-identical
to r602's cached copy. Versions: v1 2021-03-01, v2 2021-05-10 (latest). Journal (Crossref):
*Asian J. Math.* 25(6) (2021), DOI 10.4310/ajm.2021.v25.n6.a1. The intlpress landing page is a
JS shell, so the journal body was **not read**.

Definitions and theorems read (pp.1–2):
- µ_x^α(x)=α and µ_x^α(z)=(1−α)/d(x) for z∼x.
- κ_α = 1−W(µ_x^α,µ_y^α)/d(x,y).
- LLY curvature: k(x,y)=lim_{α→1} κ_α(x,y)/(1−α).
- Ricci-flat means k=0 on every edge.
- **Theorem 1** (cited from [1]=Bourne et al.). For x∼y, α↦κ_α(x,y) is piecewise linear and is
  linear on [1/(max(d(x),d(y))+1), 1]. The printed statement has the typos "lcm(d(x),d(x))" and
  "max(d(x),d(x))".
- **§4.2, third case (p.41).** G is a 4-regular Ricci-flat graph in class 𝒢 (max degree ≤4 and
  containing C₃ or C₄). It has two C₄s sharing a vertex and no two C₄s sharing an edge. Graphs
  with C₃ were handled in §4.1, so this case is C₃-free.
- **Figure 33.** Types A, B and C. Type C is a 5-cycle 0-1-2-3-4 in which each edge carries its
  own C₄ through two new vertices: 0-5-6-1, 1-7-8-2, 2-9-10-3, 3-11-12-4 and 4-13-14-0
  (`derived/img/bly-004.png`).
- **Lemmas 12–13** exclude Types A and B.
- **Theorem 11.** "Let G be a 4-regular Ricci-flat graph that contains a subgraph isomorphic to
  Type C. And G is isomorphic to the graph showing in Figure 35." Its proof, Case 1a, constructs
  the graph. The paper calls it a "Ricci-flat graph" (Figure 35 caption).

### Adjacency reconstruction T (20 vertices, 40 edges)

The 20 Type C edges come from Figure 33. The proof text of Case 1/1a then adds these edges:

| proof text | edges added |
|---|---|
| "it must be 12∼7" | 12–7 |
| "12∼16∼15∼7" | 12–16, 16–15, 15–7 |
| "we need 14∼9" | 14–9 |
| "14∼15 and 6∼11" | 14–15, 6–11 |
| "6∼17∼18∼11" | 6–17, 17–18, 18–11 |
| "9∼17∼15" | 9–17, 17–15 |
| "5∼16, and 5∼10" | 5–16, 5–10 |
| "8∼13, 8∼18" | 8–13, 8–18 |
| "18∼19∼13" | 18–19, 19–13 |
| "19∼16" | 19–16 |
| "for the edge (5,10) to be in a C₄ … 16∼19" | 10–19 (the C₄ 5-10-19-16 forces it; it is also the only remaining degree slot of 10 and of 19) |

Two source defects had to be resolved:
1. **Text.** The sentence "Note 16∼18 by Type C" conflicts with the later "18∼19∼13" and
   "19∼16": together they would give vertices 16 and 18 degree 5. Literal T+{16–18} has degree
   set {4,5} (`runs/check_bly35.r1.json`, `text_literal_T_plus_16_18`).
2. **Figure.** Figure 35 (`derived/img/bly-007.png`, zooms `fig35-*.png`) is read with collinear
   pass-through vertices 1, 4, 5, 14 and 8: lines 0-1-7, 0-4-12, 16-5-6, 15-14-13, 6-1-2,
   13-4-3 and 7-8-18. Read this way it shows exactly T's 40 edges **plus a spurious segment 2–17**,
   which would give vertices 2 and 17 degree 5. Figure-literal T+{2–17} has degrees {4,5}. The
   figure has **no** 16–18 segment and does show 16–19, which corroborates the resolution of the
   text defect.

T is therefore the unique 4-regular reading consistent with both the text and the figure.
Independently of my reading, T satisfies every hypothesis of Theorem 11 and of its §4.2 context
(checked in §3). BLY's uniqueness assertion therefore identifies T with the Figure 35 graph up
to isomorphism.

## 3. MATH verdict: Conjecture 4.1 is false (literal, p=q=2); full deduction

**Claim.** T is a simple, connected, 4-regular graph with κ(u,v) ≥ 0 = (2−p)/(pq) for all u≠v,
and |dist_x^{-1}(2)| = 10 > 8 = |dist_y^{-1}(2)| for every x∈V(T) and y∈ℤ². Hence Conjecture 4.1
fails for (p,q)=(2,2), i=2.

**Proof via published results plus a short bridge.**
1. **Ricci-flatness.** BLY publish T as a 4-regular LLY-Ricci-flat graph (Theorem 11 / Figure 35):
   k(x,y)=0 for every edge.
2. **Idleness bridge.** This is BLY Theorem 1, from [1]. BRT state the same fact themselves at
   lines 255–258, citing it as their [16].
   - For x∼y with d(x)=d(y)=4, κ_α is linear on [1/5, 1].
   - κ_1(x,y) = 1−W(δ_x,δ_y) = 0.
   - Linearity on the interval therefore gives κ_α = c(1−α), and c = lim κ_α/(1−α) = k(x,y) = 0.
   - Since 1/2 ∈ [1/5,1], κ_{1/2}(x,y) = 0.
3. **Convention identity.** BRT's µ_x is exactly µ_x^{1/2}: centre mass 1/2, neighbour mass
   (1−1/2)/4 = 1/8 = 1/(2d_x). Both papers use the graph distance. So κ_BRT = κ_{1/2} = 0 on every
   edge.
4. **All pairs.** BRT Theorem 2.1 (Ollivier; the triangle-inequality proof is given in BRT) turns
   κ ≥ 0 on edges into κ(u,v) ≥ 0 for all u≠v. The hypothesis of Conjecture 4.1 with p=q=2 holds.
5. **Sphere count.**
   - T is triangle-free, so the 4·3 = 12 non-backtracking 2-paths from x all end at distance
     exactly 2.
   - An endpoint b is hit by m paths, where m = |N(x)∩N(b)|. Then m ≥ 3 would make two C₄s share
     an edge, which is excluded, so m ≤ 2. Each m=2 vertex is the opposite vertex of exactly one
     C₄ through x.
   - So |S_2(x)| = 12 − c₄(x), where c₄(x) is the number of C₄s through x.
   - In T every edge lies in exactly one C₄, so each vertex lies in exactly 4/2 = 2 C₄s, giving
     |S_2(x)| = 10. In ℤ², |S_2| = 8.
   - This is consistent with BRT Theorem 4.4 (d=4, k=0, which gives |S_2| ≤ 10). T attains that
     bound with equality.
6. **Scope.** T is simple and connected, and the literal statement does not require G to be
   infinite. BRT's §4.2 bounds explicitly include finite graphs. ∎

**Independent exact validation.** `scripts/check_bly35.py` writes `runs/check_bly35.r1.json`
and ran under the guard: exit 0, 0.28 s, about 12 MB.
- **Method.** Rational masses are split into N unit atoms. W₁ is then (1/N) times the exact
  minimum-cost assignment, computed by bitmask DP. This is exact because the transportation LP
  with integral supplies has an integral optimum. No upstream script was imported or run.
- **Structure.** T has 20 vertices and 40 edges, is connected and 4-regular, and has 0 triangles.
  It has 10 C₄s. Every edge lies in exactly 1 C₄ and every vertex in exactly 2.
- **Type C and C₅s.** The labelled Type C subgraph is present. All 32 C₅s are Type C (each edge's
  C₄ uses two off-cycle vertices, 10 distinct in total).
- **Edge curvature.** κ_α = 0 on every edge for α ∈ {1/5, 1/3, 1/2}. This directly confirms LLY
  Ricci-flatness via the linearity theorem and matches the bridge.
- **All pairs.** All 190 pairs have κ_{1/2} ∈ {0, 3/16, 1/4}, so the minimum is 0. This is
  computed directly and does not depend on step 4.
- **Spheres.** From every vertex the sphere sizes are [1, 4, 10, 4, 1]. ℤ² gives [1, 4, 8, 12].

Dependencies:
- **BLY Theorem 11 / Figure 35, as a published object.** It is used only to establish that T is
  published. The math does not depend on the truth of its uniqueness claim, because T's
  properties are verified directly.
- **BCLMP linearity (BLY Thm 1 = BRT [16]).** Upstream, cited and not audited. It is redundant
  for the refutation given the direct κ_{1/2} computation.
- **Ollivier / BRT Theorem 2.1.** Its proof was read. It is redundant given the all-pairs
  computation.

New deductions audited here: steps 2–6 and the reconstruction.

## 4. Candidate P1 (r602) independent check

I re-implemented the candidate from its literal generators: a=(0 3 1 2), c=(0 3)(2 4),
d=(0 2)(1 4) and a⁻¹, with (u∗v)(i)=u(v(i)) and the right Cayley graph. Results:
- The group generated has order 20, and the Cayley graph has 20 vertices, 40 edges, is 4-regular
  and triangle-free.
- Edge curvature κ_{1/2} ∈ {0, 1/8}. All-pairs minimum is 0 (values {0, 1/8, 3/16, 5/24, 1/4}).
- Spheres from every vertex are [1, 4, 9, 6], so |S_2| = 9 > 8.

These match P1's claims.

Minor wording discrepancy: in the given labelling the group is not literally {x↦mx+t mod 5}
(`all_elements_affine_mod5: false`). It is an order-20 subgroup of S₅, hence a conjugate of
AGL(1,5) by the standard Sylow-normaliser fact, so the identification "AGL(1,5)" holds up to
relabelling.

The candidate graph is **not** isomorphic to T: |S_2| is 9 versus 10, and each vertex lies in
3 C₄s versus 2 (some edges lie in 2 C₄s). It is a distinct, weaker witness of the same negation.
P1's infinite H×ℤ^k family (q≥3) was **not** checked. It is not needed, and it is a variant /
parameter extension that would not be credited.

## 5. PRIOR verdict: published object defeats the target

The literal negation follows from an object published in arXiv May 2021 and in *Asian J. Math.*
2021. The bridge is short, and BRT themselves state it at lines 255–258. The conjecture was
posted in Feb 2018 (v2 Oct 2019, IMRN online Dec 2019). The object therefore postdates the
conjecture and predates the candidate by more than five years.

Bounded search: three web searches and Crossref metadata. They found **no explicit statement**
that anyone has noted the refutation of BRT Conjecture 4.1. This is an exclusion by routine
corollary of a public object (the same class as r363), **not** a claim that a labelled refutation
was published.

Not established:
- current MathDB/registry status (HOLD; no MathDB requests were made);
- the bodies of the IMRN and AJM versions;
- whether the AJM journal figure or text corrects the two typesetting defects.

Empty searches are not novelty evidence in either direction.

## 6. SUBSTANTIVE verdict: FAIL (no credit)

The campaign standard says: "Never count a known theorem, public proof/refutation, routine
corollary … parameter instance, or another variant". The decisive counterexample is a published
4-regular Ricci-flat graph. Applying it needs only a standard idleness-conversion theorem (quoted
in the conjecture's own paper), Ollivier's edge-to-pair lemma, and a radius-2 count. The
candidate's AGL(1,5) graph is a different witness of the same negation, with a smaller excess
(9 versus 10). It does not change the disposition.

## 7. FORMAL-FEASIBILITY verdict: feasible but moot

A Lean certificate for T would be small:
- Fin 20 adjacency and BFS spheres;
- 40 explicit transport plans in units of 1/8 (upper bounds only, since κ ≥ 0 needs W₁ ≤ 1);
- Ollivier's edge-to-pair lemma, or 190 explicit plans;
- an |S_2(ℤ²)| = 8 check.

Not pursued, because no credit is available. Formalization would be "mere formalization" of a
public-object corollary.

## 8. Strongest objections to this exclusion, and replies

1. **"BLY's text and figure are each defective, so the object is not cleanly published."** Each
   defect is a single isolated inconsistency (one sentence, one segment), and each produces a
   degree-5 vertex in a theorem about 4-regular graphs. The unique 4-regular reconciliation
   satisfies every hypothesis of BLY Theorem 11 and every property the paper attributes to the
   graph. A reader of the paper recovers T without new mathematics. Residual risk: low to
   moderate. The root may treat it as "published object modulo typos".
2. **"Intended domain is infinite graphs (volume growth / polynomial growth)."** The literal
   statement and BRT's own §4.2 include finite graphs. This objection would equally retire the
   candidate's own (finite) q=2 witness. An infinite 4-regular counterexample is not established
   here. That is a known limit, and any such example would be a variant.
3. **"Ricci-flat (LLY) ≠ lazy-1/2 curvature."** Handled by the linearity theorem, which applies
   because 1/2 ≥ 1/5, and independently by the direct exact κ_{1/2} computation on all pairs.
4. **"Edge-only flatness ≠ all-pairs hypothesis."** Handled by Ollivier's lemma and by direct
   all-pairs computation.
5. **"Journal versions may differ."** Unread (IMRN challenge, AJM JS shell). If IMRN silently
   dropped or altered Conjecture 4.1, the MathDB record would still cite arXiv. The exclusion
   would not become credit-worthy either way.

## 9. Recommendation

**EXCLUDE** 338366 / P1 from discovery credit: RETIRE_PRIOR_DEFEATED, by published-object
source adaptation. Credit stays 0, and counts stay 9 / 39 / next 40. Optionally preserve P1's
Cayley witness as a non-credited note. No Lean, manuscript or further search is warranted.
338408 is out of scope and untouched.

## 10. Failures, deviations, limits

See `failures.json`. In summary:
- **IMRN.** The DOI landing page returned 403 with a Cloudflare challenge. I stopped with no
  retry.
- **AJM.** The landing page is a JS shell, so the body is unread.
- **Guard deviation.** About ten short read-only inline `python3 -c` snippets ran without the
  helper guard during intake checking and JSON inspection. The first three also ran without
  `-I`/`-B`. They were manifest hash verification, JSON/proposal/record display, Crossref and
  landing-page parsing, and summaries of the check output. None executed mathematics or upstream
  code. All checker, extraction, image and binding runs used the guard. This is disclosed, not
  repaired.
- **pdftotext output.** My fresh layout texts are byte-identical to r602's derived copies
  (`24d03c90…` for BRT, `08615776…` for BLY), and the PDFs are identical too. I checked this
  only after my own reading. My page images (`page-43.png`) also match r602's
  `fig-2103-p-43.png` hash; I did not open r602's image.
- **Scope of verification.** Upstream truth (BLY uniqueness, the BCLMP theorem) was not audited.
  Registry status is HOLD.
