# Final independent review — candidate `maximal-index` (frozen commit 337af169cd)

Reviewer: pi (GLM, standard speed), review sub-agent. This is a NEW full review of the
complete 76-declaration/12-module candidate and 3-page manuscript. I authored none of the
proof, formalization, or manuscript. No children were started; no external writes.

**Overall verdict: PASS on all five gates.** The candidate proves, for the actual
separately sorted d²-entry arrays of Caro–Graswald Conjecture 4.19 / published IV.19
(MathDB 347947), that for every d ≥ 5 and every 0 ≤ k ≤ d² the universal inequality
[A_k(p)+G_k(p) ≤ d over the full nonnegative probability simplex] holds iff k ≤ 2d−5,
with strict universal sufficiency for all d ≥ 3 and an explicit uniform sharpness family.
No residual hypotheses remain in the formal endpoint. Candidate credit remains 0 until
parent packet extraction and final acceptance; accepted tally remains 11/30.

---

## Gate 1 — SOURCE: PASS

Verified artifacts and hashes (all recomputed by me):

| Artifact | SHA-256 | Match |
|---|---|---|
| arXiv 2009.06666v3 PDF (parent lane) | 7f1fe71fd961954626ea37968ab194187c9f9d4cbc40a23cde92bc491950947a | matches task |
| Published copy embedded in Caro's thesis (pi-maxindex-review/sources/thesis.pdf) | 09f704a6f4fdeba9f078761fd700d96867917902ea1d232c0ba377de23ba8903 | matches primary mediatum hash |

- **arXiv v3, p. 18, visually read** (render/…/source/arxiv/page-18.png, 130 dpi): Conjecture
  4.19 states: p ∈ ℝ^d_≥0 with Σpᵢ = 1; a_ij = (pᵢ+p_j)/2, g_ij = √(pᵢp_j); a↓_k and g↓_k the
  k-th largest entries of a and g **respectively** (independent sorting, all d² ordered
  entries, multiplicities retained); A+G ≤ d for any probability vector p maximal at
  h(d) = 2d−5. Remark 4.18 gives the Ky-Fan/operator context; Remark 4.20 states they
  cannot construct a violating channel. Text extraction (source/arxiv/arxiv.txt) agrees.
- **Version history (arXiv abs page, fetched live):** v1 2020-09-14, v2 2021-03-08
  (extended related works), **v3 2022-10-30 (latest)**, journal ref JMP 62, 042203 (2021).
  v3's only change is an added assumption in Lemma 4.26 — does not touch Conj. 4.19.
- **Published copy visually read** (source/thesis/thesis-p132-132.png): the embedded article
  page 042203-13 in **Matthias C. Caro's *Quantum Learning Theory* thesis** shows
  **Conjecture IV.19** with an identical statement. The preliminary report's later sentence
  misattributing the embedded copy to Graswald's electronic-structure dissertation is
  **not perpetuated**; the parent addendum's correction is confirmed (thesis title page:
  "Quantum Learning Theory").
- **MathDB 347947, fresh live fetch** (novelty/, recorded in provenance): status `open`,
  `progress: null`, and **all** of `solutions`, `model_attempts`, `human_solves`,
  `replies`, `comments` empty. lean_formalization_count 0.
- **MSE 3968126 via official Stack Exchange API (fresh)**: `is_answered: false`,
  `answer_count: 0`; `/answers` returns empty; only two comments (rrogers + OP reply),
  no mathematical content toward resolution.
- I did **not** infer priority from the open label; the full-body citing-paper readings
  below are the substantive evidence.

## Gate 2 — MATH: PASS

I re-derived every ingredient from the literal arrays and checked the manuscript
line-by-line against the Lean endpoint:

- **Incidence reduction:** Σ_{(i,j)∈S} a_ij = Σᵢ cᵢpᵢ with cᵢ = (outᵢ+inᵢ)/2 (loop counts
  once). Single-vertex: cᵢ ≤ k/2+1/2 = m+1 (loop double-counted). Two vertices: internal
  ordered pairs contribute ≤ 1 each to cᵢ+cⱼ, externals ≤ 1/2, at most 4 internal ⇒
  cᵢ+cⱼ ≤ (k+4)/2 = m+5/2. No mask symmetry assumed. ✔
- **Weighted bound (P ≤ 2/3):** Σcᵢpᵢ ≤ aP+b(1−P) ≤ (2a+b)/3 ≤ ((m+1)+(m+5/2))/3 =
  (4m+7)/6. ✔ (Lean `weighted_coefficient_bound` uses b := min a (m+5/2−a); the closing
  linear inequality 2b+4a ≤ 4m+7 is exactly the two hypotheses summed.) ✔
- **Geometric:** Σg²ᵢⱼ = (Σpᵢ)² = 1 ⇒ G_k ≤ √k = √(2m+1). Largest-entry inclusion with
  ties (swap argument, `exists_full_maskTopSum_containing`) ⇒ G_k ≤ P+√(2m)√(1−P²). ✔
- **Low-max closure:** √(2m+1) < (2m+11)/6 ⟺ 4m²−28m+85 = (2m−7)²+36 > 0; strict. ✔
- **High-max (P > 2/3):** outside row/col u entries ≤ ε < P/2; baseline P/2 + loop extra
  P/2 + tail extras (each tail coordinate in ≤ 2 positions × pᵢ/2) ⇒ A_k ≤ (k+1)P/2+ε =
  1+mP. Two-dimensional Cauchy: (m+1)P+√(2m)√(1−P²) ≤ √(m²+4m+1); (m+2)²−(m²+4m+1)=3>0. ✔
- **Sharpness (exact rational recomputation, d = 5…15, math/exact-sharpness-check):**
  p = (4m²,1^m,0,0)/(4m²+m), r = 2m, N = r²+m; selected masks are genuine 2m+2-element
  sets; A_sel = ((m+3/2)r²+m)/N, G_sel = (r²+2mr+1)/N; A_{k′}+G_{k′}−d =
  (m−1)²/(4m²+m) > 0 exactly, for every tested d; d=5 gives 29/9+11/6 = 91/18 > 5.
  My exact top-sum computation matches the selected sums (the selections attain the top
  sums on this witness). The witness itself satisfies the bound at k = 2d−5.
- **Classification logic:** top sums nondecreasing in k ⇒ sufficiency for all k ≤ 2d−5
  from the strict bound at 2d−5; violation at 2d−4 propagates to all k ≥ 2d−4. Both
  directions complete; k ranges 0…d² as in the source. Independent random search
  (4000 vectors × d = 5…10) found violations exactly at k ≥ 2d−4 and none below.
- Ties, zeros, ordered pairs, normalization, exact cardinalities, natural-offset indices,
  and independent sorting all handled; no numerical certificate enters any proof step.

## Gate 3 — FORMAL: PASS

- Copied the candidate bytes into my lane (`candidate-copy/`, all 17 frozen hashes
  re-verified OK before replay) and ran the **fresh isolated strict replay** with the
  absolute binary `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
  and the absolute pinned packages; the toolchain exists and worked — no PATH inference.
- Result (formal/replay-stdout.log, formal/…/build/verified/audit.json):
  **PASS, 76 declarations, 12 modules**, compiler "Lean (version 4.34.1, …, commit
  5045d0056413266e57c625dcd7c365b10e377c52, Release)", dependency revisions checked,
  warningsAsError=true, only `propext`, `Classical.choice`, `Quot.sound`.
- **All 76 declaration types and axiom inventories were read from MY fresh Checks.log**
  (formal/…/build/verified/Checks.log); all 12 module logs are 0 bytes (no warnings).
- No `sorry`/`admit`/`axiom`/`unsafe`/`native_decide` in any source (script regex +
  my own grep). Parent receipt `verification/parent-audit.json` is **byte-identical**
  (sha d72f2313…) to my fresh `build/verified/audit.json`.
- **Definitions inspected, not just PASS:** `arithmeticEntry p e = (p e.1 + p e.2)/2`;
  `geometricEntry p e = √(p e.1 · p e.2)`; `sortedTopSum f k = Σ of first k of
  (Finset.univ.toList.mergeSort by ≥ value)` — the literal sorted array over ALL ordered
  d² indices, multiplicities retained, arithmetic and geometric sorted **independently**;
  `maskTopSum` = sup over Finsets of card ≤ k, with the bridge
  `sortedTopSum_eq_maskTopSum` proved (nodup/permutation/pairwise descending). No
  surrogate for the sorted source arrays is used at the endpoint.
- **Endpoint read from my log:** `MaxIndex.source_index_classification (d : ℕ) (hd : 5 ≤ d)
  (k : ℕ) (hk : k ≤ d * d) : (∀ p : Fin d → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
  sortedTopSum (arithmeticEntry p) k + sortedTopSum (geometricEntry p) k ≤ d) ↔ k ≤ 2*d − 5`
  — exactly d ≥ 5, k ≤ d², universal over the full simplex, actual sorted arrays; **no
  residual mask/incidence/normalization assumptions**. Supporting pieces verified in
  source: FiniteSelections (attainment, exact cardinality, largest-entry exchange with
  ties), IncidenceBounds (real row/column incidence for arbitrary ordered masks),
  ArithmeticHigh (full star-extras), GeometricBounds/ProbabilityEntries (actual square
  mass 1, diagonal = pᵤ), Sharpness (witness on `Option (Fin m ⊕ Bool)`, mask sizes 2m+2,
  actual sums, scalar gap), Reindexing (`maskTopSum_comp_equiv`),
  SourceClassification (witness reindexed onto Fin d via `Fintype.equivOfCardEq` — a
  genuine reindexing, and the iff assembled from counterexample + monotonicity +
  strict universal bound). No mathematical helper hypothesis remains final.
- Frozen main.tex / paper.pdf / audit / all 12 module hashes re-measured and match
  frozen-review-hashes.json exactly.

## Gate 4 — SERIOUS BOUNDED NOVELTY: PASS (bounded), extending preliminary coverage

- **Full bodies of all three S2-indexed citing papers read** (PDFs fetched and stored in
  novelty/, not abstracts):
  - **arXiv 2201.12524 v1** (Sadri, Shahbeigi, Puchala, Życzkowski, *Accessible Maps in a
    Group of Classical or Quantum Channels*, publ. doi 10.1142/S1230161222500020): the
    arXiv v1 reference list does **not even contain** Caro–Graswald (divisibility cited
    via Denisov and Wolf–Cirac). Body is group-structure/accessibility; zero engagement
    with the conjecture, singular-value divisibility criteria, or top-k AG sums.
  - **arXiv 2109.03847 v2** (Hasenöhrl, Caro, JMP 63, 072204): cites Caro–Graswald as
    [42] only once, in the outlook ("a divisibility variant of this question … [40–42]").
    Body: normal forms for superchannel semigroup generators. No engagement with the
    conjecture. (Papers indeed cite the published version, not v1.)
  - **arXiv 2004.09264 v3** (Chakraborty, Chruściński, *Construction of propagators…*):
    cites the source as [19] in a passing "see also recent eprint" list. Body:
    generalized-inverse propagator construction. No engagement with the conjecture.
- **Citation-index coverage:** OpenAlex (W3086098932, cited_by_count = 3): exactly the
  same three works — no additional citers. Crossref is-referenced-by-count = 2. The S2
  second-call 429 limitation noted by the preliminary review is superseded by two
  independent indexes.
- **Author trajectories:** Matthias C. Caro's complete arXiv listing through Oct 2026
  (31 works read) — all quantum learning/testing/tomography; no follow-up on this
  conjecture and no erratum. Benedikt (R.) Graswald's arXiv works are electronic-structure
  (DFT/MPS) only, besides the source. **No erratum/addendum to JMP 62, 042203 found**
  (Crossref `relation`/`updated-by` empty; arXiv listing current).
- **Problem-specific searches** (recorded queries/URLs in provenance.json; top hits are
  the MSE question itself, an unrelated probabilistic AG-inequality paper 2112.04340,
  graph-theoretic AG-index, Littlewood–Offord): nothing resolves or strengthens the
  conjecture. The source's own provable bound ⌊2d−2√(2d)+1⌋ is far weaker than 2d−5.
- **Subsumption check:** for a known result to subsume the candidate it would have to
  prove the specific independently-sorted pair bound — which would resolve the open
  conjecture; no identifiable such theorem was found (I did not rely on the earlier
  review's unattributed "Bapat max convolution" phrase). MathSciNet/zbMATH access not
  presumed. **Bounded conclusion: no published or posted proof or stronger result found;
  nothing excludes credit. No absolute priority or worldwide-count claim is made.**

## Gate 5 — MANUSCRIPT: PASS

- Rendered the frozen paper.pdf myself (110 dpi, render/paper-{1,2,3}.png): exactly
  3 pages, clean LaTeX layout, no cutoffs/overfull damage.
- Source attribution correct: Caro–Graswald, J. Math. Phys. 62, 042203 (2021),
  doi:10.1063/5.0031760, arXiv:2009.06666v3, Conjecture 4.19 / published IV.19.
- Scope exact: Theorem 1 is the full iff for d ≥ 5, 0 ≤ k ≤ d², over "every probability
  vector", with the strict sufficiency d ≥ 3 stated; small-d classifications explicitly
  outside the certificate. All formulas match my re-derivations and the Lean endpoint
  (incl. Eq. (1) cᵢ ≤ m+1, cᵢ+cⱼ ≤ m+5/2; Eq. (2)–(4); sharpness sums and gap).
- 76-declaration formal count stated; abstract/§1 correctly describe independent sorting
  and ordered d² entries; references clean. Parent build reported exit 0 zero issues,
  consistent with the rendered pages.

## Objections

- **Decisive objections: none.**
- **Non-decisive notes:** (1) The arXiv v1 of 2201.12524 does not cite the source at all;
  the S2 citation edge presumably keys on the published version — recorded, harmless.
  (2) Bounded novelty can never exclude unpublished/obscure resolutions (e.g. no
  MathSciNet/zbMATH); this limitation is inherited by any search of this kind and is
  disclosed. (3) The 2201.12524 published-version body was not separately fetched (v1
  full body read; journal is a minor World Scientific venue, content per abstract
  identical); risk negligible. (4) Small-d values (h1=0, h2=1, h3=2, h4=4) remain
  uncredited research notes, correctly not claimed by this candidate.

Candidate credit remains 0; accepted 11/30 until parent packet/extracted replay and
final acceptance. No candidate/parent/shared-index/dependency/git edits, no children,
no external posting made.
