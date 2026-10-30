# Independent adversarial final review — cstar-sendov (all five gates)

Reviewer: pi-sendov-final-review (solo, no children, standard speed). Date: 2026-10-26.
Scope: `NEW/candidates/cstar-sendov` frozen at the 34 files listed in
`final-review-hashes.json`. Method: I copied the candidate bytes into my own lane
(`candidate/` here), re-measured **all 34 hashes myself**, and ran every check against
my own copy — never against the parent's working tree. The preliminary review
(`reviews/preliminary-review.md`) was treated as context only; nothing below relies on it.

## Verdicts

| Gate | Verdict |
|---|---|
| FORMAL (fresh isolated strict replay + own axiom/type audit) | **PASS** |
| SOURCE (exact statement, both PDFs, live MathDB, history) | **PASS** |
| MATH (independent rederivation, new structure) | **PASS** |
| NOVELTY (serious bounded screen) | **PASS** (limits recorded) |
| ELIGIBILITY (scope/credit discipline) | **PASS** |
| MANUSCRIPT (all 3 pages rendered and personally inspected vs Lean) | **PASS** |

Decisive objections: **none found.**

---

## 1. FORMAL gate — PASS

* All **34** files in `final-review-hashes.json` re-hashed from my own copy: **34/34 match**
  (my script: `logs/` work, recorded in provenance). No extra or missing files.
* Pinned toolchain verified first: lean 4.34.1 (commit 5045d0056413, Release) and all
  9 package revisions (`mathlib d13f23b7…` + 8 deps) match `verification/pins.json`;
  `git status --porcelain` clean on each.
* **Fresh isolated strict replay** in my lane with the pinned binary and
  `--packages …/2026-10-14/formal/.lake/packages`:
  `python3 candidate/verification/verify_candidate.py candidate …` →
  **PASS, 136 declarations, 8 modules, axioms exactly {Classical.choice, Quot.sound, propext}**
  (24.4 s wall; my own copy, own `build/` — no existing .olean trusted; the script deletes
  and rebuilds every module .olean).
* Module logs under `-DwarningAsError=true` are all **0 bytes** — no warnings anywhere.
* **Independent audit beyond the script** (`candidate/build/independent-audit/`):
  I rebuilt all 8 modules myself with a separate LEAN_PATH and ran my own
  `#check @…` + `#print axioms` file over all 136 declarations:
  136/136 axiom reports present, **every one exactly [propext, Classical.choice, Quot.sound]**.
  Full types of all 7 main theorems printed and read (`logs/independent-types.log`) —
  they match candidate.json verbatim.
* Own recount of declarations with an independent regex: 136 total
  (Analytic 39, Cubic 15, FunctionAlgebra 40, SourceStatement 16, EndpointAssembly 3,
  Selection 8, ConvexWeights 5, SourceCounterexample 10); identical to the parent
  receipt's inventory, name for name. Forbidden tokens
  (`sorry|admit|axiom|unsafe|native_decide`): **absent** (my own grep).
* The two formerly private helpers (`CStarSendov.harmonic_sum_zero`,
  `CStarSendov.conj_inv_eq_rmul`) are public and appear in the replay inventory.
* **Endpoints closed.** `source_counterexample_353909 : ¬sourceCubicConjecture353909` and
  `source_counterexample_published_conjecture4 : ¬sourceSplitCubicConjecture4` have
  **zero premises**. The two conjecture predicates carry only the literal source
  hypotheses (roots in disc; b_k zeros of the deleted derivative + disc + Equation-(1)
  representation; resp. complete linear factorization of p′). No residual
  classification, convexity, bound, positivity or existence premises anywhere in the
  negations.
* **Instance faithfulness (verified by synthesis probes, not by reading names):**
  `FunctionAlgebra = C(Set.Icc (0:ℝ) 1, ℂ)` — literally C([0,1],ℂ) with subtype topology.
  `CommCStarAlgebra FunctionAlgebra` synthesizes via `ContinuousMap.instCommCStarAlgebra`
  (needs `CompactSpace [0,1]` — true). `StarOrderedRing FunctionAlgebra` synthesizes via
  `ContinuousMap.instStarOrderedRingOfContinuousSqrt`; note `PartialOrder ℂ` is a
  **scoped** instance (`ComplexOrder` locale) — the candidate modules open that scope,
  which is why `inferInstance` works there. `sourceCStarPositiveOrder` is a real
  Mathlib instance, not an assumption.
* `sourceClosedDisc a r z := (z−a)*star(z−a) ≤ Real.sqrt r • 1` — the **√r is the
  source's own Definition 2** (I verified it on the rendered publisher p59; the parent's
  plain-text extraction drops the radical). Only r = 1 is ever used, so the unit disc is
  the pointwise `|z(t)−a(t)| ≤ 1` condition either way.
* No zero-divisor cancellation anywhere: `mul_eq_zero` is applied only **after pointwise
  evaluation in ℂ** (`pointwise_critical_classification`, `factor_root_global`), and the
  global choice is proved by connectedness (`selection_rigidity`/`continuous_two_point_selection`).
  The Selection.lean comments state this correctly.

## 2. SOURCE gate — PASS

* Fetched the **actual publisher PDF** (krasec.ru …/2026/03/Krishna.pdf):
  SHA256 `479fe573a30e3355222feb5aec6ad00535253bf30317826f26a8f6ada8086d8e` — exact match.
  Fetched the **preprint** (arxiv.org/pdf/2203.06916v1):
  SHA256 `fa06dae1bfbf79eccde4422d942f30a02dcc2ca81d739e0b53df4629fe8cb9b4` — exact match.
  Publisher PDF still live (HTTP 200, 2026-10-26).
* **Personally rendered and visually inspected** the publisher pp 59–60 (journal pages =
  PDF pages 4–5; my renders: `logs/pages/krishna-p-4.png`, `krishna-p-5.png`):
  - p59: Theorem 1 (C*-Gauss–Lucas) with **Equation (1)** `z = Σ ω_{z_j} a_j, Σ ω = 1`
    (positive ω ∈ A); **Definition 2** `D*(a,r) = {z : (z−a)(z−a)* ≤ √r·1}`; the source's
    p′ is literally the deleted-factor sum; Conjecture 2 (commutative + G(A) dense) begins.
  - p60: **Conjecture 3** (C*-algebraic Sendov): unital C*-algebra, a_j ∈ D*(0,1), p′ the
    deleted-factor sum, assume roots b₁,…,b_{n−1} ∈ D*(0,1) each in the form of Eq (1);
    then ∀ a_j ∃ zero b of p′ with b ∈ D*(a_j,1). **Conjecture 4**: same hypotheses,
    "p′ completely factors into linear factors" instead of the root/convexity assumptions.
    Theorem 2 verifies degree 2 only. No counterexample or resolution appears.
  - Preprint Conjecture 2.5 text-extracted and compared: verbatim the same statement
    (unital, no commutativity, no density) = published Conjecture 3 = MathDB 353909.
* **Live MathDB** (fresh API fetches `https://mathdb.com/api/posts/{353908,353909}`,
  2026-10-26, saved under `logs/`): both `status: open`, `lean_formalization_count: 0`,
  comments/solutions/model_attempts/human_solves/formulations/replies/attachments all 0.
  My fresh 353909 JSON is **semantically identical** to the candidate's frozen
  `sources/353909-live.json` (zero differing keys) — nothing happened since the freeze.
* **Hypothesis fit (n = 3)** against the exact published text: all three formal hypotheses
  discharged for the displayed elements (see §3/§4), conclusion fails at a₀ for **both**
  zeros of p′. The formal `sourceCubicConjecture353909` quantifies over arbitrary b-lists
  satisfying the hypotheses — weaker than the source's "the n−1 roots" reading, so
  ¬formal ⟹ ¬source; and the counterexample instance satisfies even the strongest
  reading (classification `source_critical_classification` + pointwise injectivity show
  B± are *exactly* the two critical elements, distinct everywhere).

## 3. MATH gate — PASS

I rederived everything independently with a deliberately different structure from the
parent's sympy checker (mpmath 50 dps, 4001-point dense grid, explicit coefficient
comparisons; `independent-check/independent_check.py`, output `independent-check/result.log`):

* q(t)² = 1 + (27/16)u(t)² pointwise (residual ≤ 3.7e-49 over the whole grid);
  |q|² ∈ [11/16, 43/16] so q is nowhere zero and |q| ≤ √43/4 < 2; hence B± continuous,
  nowhere equal, and |B±| ≤ (3/10)(1+√43/4) ≈ 0.7918 < 9/10 < 1.
* Deleted derivative = 3z² − (9/5)z − (729/1600)u² = 3(z−B⁺)(z−B⁻) **as a coefficient
  identity** (3(B⁺+B⁻) = 9/5, 3B⁺B⁻ = −729/1600 u²), i.e. a genuine polynomial identity in
  A[z], matching the Lean `sourcePolynomial_derivative_split` (proved coefficient-wise via
  evaluation homomorphisms — a true A[z] statement, not a pointwise numerical accident).
* Roots a₀ = 9/10, a₁ = (27/40)u, a₂ = −(27/40)u: norms 9/10, 27/40, 27/40, pairwise
  distinct at every t (u never vanishes).
* **Classification of every critical element** (the load-bearing zero-divisor point):
  p′(b)=0 in A gives, pointwise, b(t) ∈ {B⁺(t), B⁻(t)}; F(t) = ((10/3)b(t)−1)/q(t) is
  continuous into {−1,1} on connected [0,1], hence constant. Pointwise mixing impossible.
  Exactly **two** critical elements. The connectedness of [0,1] is essential, not incidental.
* B never meets any a_j (six cases; |q| ≠ 2, |u| ≠ 4/3), so B − a_j is invertible; the
  harmonic identity Σ_j (B−a_j)⁻¹ = 0 (division of p′(B)=0 by the nowhere-zero product,
  legitimate in the commutative algebra; the source's own Theorem 1 is likewise
  commutative-only) conjugates to Σ r_j(B−a_j) = 0 with r_j = |B−a_j|⁻² > 0, giving
  B = Σ ω_j a_j, ω_j = r_j/Σr_i — continuous, strictly positive, summing to 1. Residual
  < 1e-40 over the whole grid; min weight > 0. This is the source's Equation (1) with
  **genuine positive elements of A**, not unproven pointwise coefficients.
* Endpoint obstruction exact: Q = √43/4 = (3√3/4)√(43/27) > 3/2; B₋(0) = B₊(1) =
  (3/10)(1−Q); |a₀ − B₋|(0) = |a₀ − B₊|(1) = 3/5 + 3√43/40 = 1.0918078893226500489…,
  an exact algebraic number > 21/20 > 1. Each of the only two critical elements exits the
  unit disc around a₀ at one endpoint; sup-distance > 21/20 for every critical element.
* Max residual over all checks: 3.7e-49. Classical scalar Sendov is untouched: each fiber
  cubic has all roots in |z| ≤ 0.9 and the per-fiber near critical point exists, but the
  near branch switches B⁺ → B⁻ across [0,1]; no single continuous element can follow it.

## 4. NOVELTY gate — PASS (bounded; limits below)

Independent probes executed 2026-10-26 (raw outputs in `independent-check/`, `logs/`):

* **OpenAlex** `cites:W4226164614`: count = 4, all four are Krishna's own
  "C*-algebraic Bieberbach, Robertson, …" preprint duplicates (2022). No external citation.
* **arXiv API**: `abs:"Sendov"` newest-first, 37 entries — the only operator-algebraic
  entry is 2203.06916v1 itself. No C*-algebraic Sendov counterexample, refutation, or
  resolution anywhere in the abstract sweep. Submission history of 2203.06916: **v1 only**
  (2022-03-14), with `journal_ref` to the 2026 Vestnik KRAUNC volume — the published
  version is the same paper; no later arXiv revision.
* **Author later work**: arXiv author sweep — Krishna's later C* papers (Casas-Alvero
  2206.09197, Schoenberg 2206.06653, Smale mean value 2206.08154) are separate conjecture
  variants; none touches C*-Sendov; no retraction/correction of the 2026 paper.
* **MathDB live**: 353908 and 353909 both open, zero solutions/comments (§2).
* **Subsumption screen (nearest neighbours)**: Guo–Jiao–Kim, *On continuous selections of
  polynomial functions* (2007.03952) — I checked the parent lane's retained PDF
  (SHA `70fc63b1…` matches the addendum) and its extracted body: piecewise-polynomial
  selections with **Clarke subdifferential** critical points; **zero** occurrences of
  "Sendov"; nothing implies the present counterexample. Also checked: smooth selection of
  polynomial roots (math/9801026 — roots, not critical points, no proximity constraint),
  Salter's stratified braid monodromy (2304.04627), derivative-chain zero selection bounds —
  none subsumes a C*-Sendov refutation.
* Classical Sendov status (2026 proof, Tao's digestion post, teorth/sendov Lean repo, a
  computer-assisted proof candidate) is **consistent** with this proposal — the scalar
  statement is not contradicted, and no separate branch-mechanism credit is claimed.
* **Limits**: web/API search only (arXiv, OpenAlex, MathDB, publisher site, open web);
  Semantic Scholar rate-limited (HTTP 429) so OpenAlex was used as the citation source;
  no MathSciNet/ZbMATH/Scopus; no exhaustive non-English full-text sweep; a bounded screen
  cannot prove absence. No absolute priority or first-worldwide claim is made or supported.

## 5. ELIGIBILITY gate — PASS

* One **combined** outcome: the two endpoints negate the literal cubic specializations of
  MathDB 353909 (preprint Conj 2.5 / published Conj 3) and the published fully-split
  variant (Conj 4) in the same algebra; treated as ONE outcome as instructed. Credit 0;
  accepted tally 15/30 untouched; no count asserted by this review.
* **353908 deliberately not claimed**: its extra density-of-invertibles hypothesis is
  outside the formal target, exactly as scoped in README/PROOF/paper §4. (For the record,
  C([0,1],ℂ) does have dense invertibles, but no formal claim is made — correct discipline.)
* Scalar Sendov untouched; no separate credit for the classical selection/monodromy
  mechanism; numerical checks correctly framed as supplementary.
* No shared-index or other-lane edits made; nothing staged or committed; no external posts.

## 6. MANUSCRIPT gate — PASS

Rendered **all 3 pages** of `paper.pdf` (SHA `ecdc4450…` matching the freeze; tex SHA
`3c0a517b…` matching) at 110 dpi and personally inspected each page
(`logs/pages/paper-{1,2,3}.png`). No clipping, unresolved references, or rendering issues;
hyperref links resolve. Every mathematical/manuscript claim was cross-checked against the
full Lean endpoints:

| Paper claim | Lean witness |
|---|---|
| "norm at most 9/10" roots; strict interior | `roots_norm_le`, `roots_in_source_disc`, `source_complete_counterexample` |
| derivative splits completely, two distinct branches | `sourcePolynomial_derivative_split` (A[z] identity), `criticals_pointwise_injective` |
| p′ = 3(z−B⁺)(z−B−) for every z ∈ A; also in A[z] | `sourcePolynomial_derivative_split`, `sourceCubicDeleted_derivative` |
| ‖B±‖ < 9/10 | `criticals_norm_lt` |
| B± satisfy (1) with strictly positive continuous real coefficients | `source_critical_strict_real_weights`, `source_critical_positive_convex` |
| every critical element is B± ; ‖a₀−b‖ > 21/20 | `source_critical_classification`, `source_all_critical_distance_gt` |
| both source conclusions fail | `source_counterexample_353909`, `source_counterexample_published_conjecture4` |
| √r retained in the disc definition | `sourceClosedDisc` (and p59 of the publisher PDF) |
| endpoint distance 3/5 + 3√43/40 ≈ 1.0918078893 | `bad_minus_endpoint`/`bad_plus_endpoint`; my mpmath: 1.0918078893226500489… |
| 136 declarations / 8 modules / 3 axioms / warnings-as-errors | my fresh replay (§1) |

The paper's source-fidelity paragraph (Definition 2 √r, deleted-factor p′, Eq (1), Conj 3 =
preprint 2.5 = MathDB 353909, Conj 4 variant, degree-2 Theorem 2 only, 353908 scoping) is
accurate against the pages I inspected. `provenance.json`'s `final-provenance.json`
correctly marks "independent_final_review: pending" — this document is that review.

## Non-blocking notes (no action required)

1. `sourceClosedDisc`'s √r looks unusual but is **exactly** the source's Definition 2; only
   r = 1 occurs. Keep it; the paper already explains it.
2. In `sourcePositiveConvex`, `0 ≤ w j` is the pointwise PartialOrder (via the
   `ComplexOrder`-scoped `Complex.partialOrder` + `ContinuousMap.partialOrder`). For
   real-valued continuous weights this coincides with C*-positivity (w ≥ 0 ⟺ w = √w·√w),
   and the genuine `StarOrderedRing` instance exists and is inventoried
   (`sourceCStarPositiveOrder`). Faithful; worth one sentence if the paper is ever extended.
3. The formal conjectures quantify over arbitrary b-lists (a weakening of the source's
   "the n−1 roots" phrasing). This only makes the refutation harder, and the instance
   satisfies the strongest reading anyway (classification + injectivity). No action.
4. `sourceCubicDeleted roots z` and `sourceDeleted z`, and the deleted-derivative /
   `deletedProductDeriv` bridge, are joined by defeq plus explicit transfer lemmas; all
   compiled and audited, but they are separate definitions — future editors should not
   assume syntactic identity.
5. Fresh MathDB fetch is byte-different from the frozen JSON (key ordering) but
   key-for-key identical in content — no drift.

## Verdict

All five gates **PASS** on my own byte-verified copy: the 136-declaration certificate is
reproducible from the pinned toolchain with warnings as errors and only the three standard
axioms; both source negations are closed and faithful to the published statements; the
mathematics rederives cleanly; the bounded novelty screen found no prior or subsuming
work; the manuscript matches the formal certificate claim-for-claim. **No decisive
objections.** I recommend the parent proceed to packet assembly and extracted replay; the
candidate remains credit0 with no priority claim.

— pi-sendov-final-review
