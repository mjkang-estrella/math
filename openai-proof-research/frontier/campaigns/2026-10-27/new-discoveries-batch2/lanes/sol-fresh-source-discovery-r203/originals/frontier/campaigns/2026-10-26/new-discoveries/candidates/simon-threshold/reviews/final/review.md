# Independent final review — Simon threshold convexity (MathDB 349140 separate question)

Reviewer: pi-simon-threshold-final-review (new independent adversarial reviewer; not author/implementer).
Lane: `lanes/pi-simon-threshold-final-review`. Candidate: `lanes/parent-simon-threshold` frozen at pinned bytes (58 files, all hashes verified on my own byte copy, unchanged after my replay).
Scope: ONLY the last paragraph of Section 3, p5, of Simon arXiv:2012.11018v2. The MAIN MathDB 349140 complete-monotonicity-iff-criterion conjecture is NOT solved or claimed; I verified the candidate never claims it.

## Verdict summary

| Gate | Verdict |
|---|---|
| 1 Source | PASS (access limits recorded) |
| 2 Mathematics | PASS |
| 3 Formal (fresh strict replay) | PASS |
| 4 Bounded novelty / substantive eligibility | SUBSTANTIVE — ELIGIBLE (independent decision; minimal-end caveat recorded) |
| 5 Manuscript | PASS |

**Recommendation: ACCEPT as a substantive resolution of the explicit source threshold-convexity question, at discovery-credit decision of the parent.** This is a clear recommendation, not a forced count. If accepted, the remaining parent steps are the deterministic packet/extracted replay and ledger edit; candidate bytes stay frozen.

---

## Gate 1 — SOURCE: PASS

- I personally rendered and read `sources/source-page-5.png` and the extracted text of the pinned v2 PDF (`sources/2012.11018.pdf`, sha256 `7822c87202893152384dea9a93446e6c7187634e22de1b97fbf893c3920deca6`, matches provenance). The last paragraph of Section 3 (p5) reads, verbatim in substance: fix γ>1, set β(α) = inf{β > 0, z + γ(z^{β−α} − z^β) ≤ 1 for all z ∈ (0,1)} ∈ (α, α(1+γ)/2) for all α ∈ (0, 1/γ); "it is not difficult to prove that α ↦ β(α)/α is non-decreasing. We also believe that α ↦ β(α) is convex, but this fact still eludes us."
- The formal `SourceCriterion`/`sourceThreshold` match this definition literally: infimum over β > 0, criterion ∀ z ∈ (0,1) real powers, domain α ∈ (0, 1/γ), hypothesis γ > 1. The source's β(α)/α monotonicity is source-known and is NOT counted or claimed.
- Fresh refetches today: arXiv abs page confirms v2 (25 Mar 2021) is still latest; no journal ref on arXiv. OpenAlex W3113809050 gives DOI 10.1080/10652469.2021.1913138; the author's own publication list gives ITSF 33(2), 108–114, 2022. Publisher PDF route is a Cloudflare challenge (HTML, not body) — publication body unread; HAL API has no `fileMain` (verified: 0 occurrences). These limits are correctly disclosed.
- MathDB 349140: pinned live record (`sources/349140-live.json`, fetched same day, hash-verified) has status "open", post_type "conjecture", and its statement is the main CM-iff criterion — a different, separate question from the threshold paragraph. My own direct refetch of the MathDB record page/API hit 404/403 routing and was inconclusive; recorded as a limit (non-blocking; recommend the parent re-check status at acceptance time).

## Gate 2 — MATHEMATICS: PASS (independent rederivation)

I rederived every bridge myself, without reference to the candidate's text:

1. z = e^{−t}, t>0 bijection. Criterion ⟺ γ e^{−t(β−α)}(1−e^{−αt}) ≤ 1−e^{−t} ⟺ (logs of positive factors) β ≥ α + [log γ + log(1−e^{−αt}) − log(1−e^{−t})]/t for all t>0.
2. Substitution s = αt gives the family J_s(α) = α + (α/s)(log γ − f(s) + f(s/α)) with f(x) = −log(1−e^{−x}) > 0. The literal feasible set is {β>0 : β ≥ J_s(α) ∀s>0}.
3. Convexity: (α/s) f(s/α) = (1/s)·α f(s/α) is a positive multiple of the classical positive perspective of the convex f (f′ = −1/(e^x−1) strictly increasing); the remaining terms are linear in α. Pointwise supremum of convex functions is convex on (0,1/γ). All standard, openly credited.
4. Literal-infimum bridge — the actual content, all needed and all proved:
   - Feasibility: β = α+1 is admissible whenever γα ≤ 1, via 1−e^{−αt} ≤ αt and te^{−t} ≤ 1−e^{−t}. Hence sup ≤ α+1 < ∞ on the whole domain (since α < 1/γ ⇒ γα < 1).
   - Positivity: f(s) → 0, so for large s, log γ − f(s) > 0, and f(s/α) > 0 gives J_s(α) > α. Hence sup > α > 0. This step is essential: if the sup were ≤ 0, the literal infimum over β>0 would be 0, not the sup. The candidate handles this pitfall explicitly (`thresholdSup_pos`), and also avoids the sInf-empty (default 0) trap by proving nonemptiness.
   - Therefore the feasible set is [sup, ∞) and the literal infimum equals the supremum. No optimizer existence, attainment, or regularity premise is used anywhere.
5. Pitfalls checked: sInf unbounded/empty defaults; positive-β requirement; open endpoints (Ioo 0 (1/γ)); real rpow well-defined on (0,1); β≤α regime harmless (equivalence is algebraic); strict convexity is NOT claimed (correctly).
6. Numeric sanity (not proof): for γ ∈ {1.05, 1.5, 3, 10}, α sweeps, envelope-sup = direct-sup, positivity, "β=α+1 admissible iff γα≤1" and slope-nondecreasing all consistent. Saved check in my lane log.

No gap found. The proof is correct and complete for exactly the claimed statement.

## Gate 3 — FORMAL: PASS (own fresh strict replay)

- Own byte copy `replay/candidate-frozen`; all 58 `review-hashes.json` entries verified BEFORE replay and re-verified AFTER: unchanged. Parent candidate untouched (re-verified independently).
- Fresh strict replay with `verify_candidate.py` (my copy, my pins), explicit `--lean-bin .../lean-4.34.1-linux/bin/lean --packages .../2026-10-14/formal/.lake/packages`:
  - status PASS; Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; all 8 dependency revisions verified clean by the script.
  - 26 declarations / 5 modules; every module log 0 bytes; `-DwarningAsError=true`; no forbidden tokens (sorry/admit/axiom/unsafe/native_decide).
  - I personally read all 26 `#check`/`#print axioms` reports in my own `Checks.log`: every declaration depends only on propext, Classical.choice, Quot.sound. Endpoint: `SimonThreshold.source_threshold_convex {γ : ℝ} (hγ : 1 < γ) : ConvexOn ℝ (Set.Ioo 0 (1/γ)) (SimonThreshold.sourceThreshold γ)` — the literal real infimum, no residual optimizer/regularity premise.
  - Replay receipt: `replay/candidate-frozen/build/verified/audit.json` (my own run; parent's `parent-audit.json` sha 7df07ef6… matches the declared audit sha and my replay reproduces its content).

## Gate 4 — BOUNDED NOVELTY / SUBSTANTIVE ELIGIBILITY: SUBSTANTIVE, ELIGIBLE (independent decision)

I did not presume eligibility from the Lean PASS. My own investigation:

- Personally read theorem bodies of the three closest accessible sources: Berg–Çetinkaya–Karp 2004.14075 (gamma-ratio kernel LCM criteria; no threshold-convexity statement), Wang 2410.19330 (Theorem 1.2 moment log-convexity for gamma/beta products; different target), Ferreira–Simon 2512.04940 (Theorems A–D convex orderings of Mittag-Leffler functions; no β_γ threshold). None subsumes.
- Searched for prior resolutions (exact criterion, "still eludes us", threshold convexity, Le Roy Stieltjes threshold, 2021–2026 citers). All 10 OpenAlex citers identified; the geometric-"convexity" papers are unit-disk starlikeness/close-to-convexity — a different meaning. The four closed bodies (multi-parametric Le Roy 2023, revisited 2024, Turán-type 2025, Bratu 2026) were screened at abstract/scope level only — recorded limit; none plausibly contains a threshold-shape theorem.
- Decision reasoning: The resolution is NOT an immediate corollary of any located known theorem. The "known theorem" (perspective convexity, sup convexity) supplies only the final step; the result's content is the exact identification of the source's literal infimum with a perspective supremum, which requires the rescaling s=αt, a genuine admissibility bound (β=α+1 under γα≤1), and a positivity argument that is easy to get wrong. The author posed the question in a published paper (2021/2022) and stated it "still eludes us"; no resolution appeared in 5 years of accessible literature. This fits the campaign's counting standard (substantive resolution of an exact unresolved source question) and its precedent (short tool-based resolutions accepted, e.g. #8), while the exclusion standard targets results already implied by published theorems — not the case here.
- Caveat recorded honestly: the final convexity step is textbook material and is openly credited; this sits at the minimal end of "substantive". I judge it eligible because the reduction to that step is the new mathematics and is fully proved. The parent retains the final count decision; no worldwide-priority claim is made anywhere.

## Gate 5 — MANUSCRIPT: PASS

- Rendered and read both pages of `paper.pdf` (sha 956b1e5a…, matches provenance). Theorem 1 states exactly the formal endpoint (literal B_γ convex on (0,1/γ), ∀γ>1). Lemma 1 (representation, 0 < α < B_γ(α) ≤ α+1) and its proof match my independent derivation.
- No CM overclaim: abstract and page 2 explicitly say the complete-monotonicity conjecture "remains open here" and that this resolves only the separate final-paragraph question; MathDB 349140 named and not claimed. Source-known β/α monotonicity attributed to the source, uncounted. Tools (perspective/supremum convexity, exponential inequalities) explicitly declared standard with "no new general convexity theorem is claimed". Credit-0 pending language present. No worldwide-priority claim. Reference correct: arXiv:2012.11018v2 (2021), Section 3, p.5; ITSF 33(2) (2022), 108–114, doi:10.1080/10652469.2021.1913138. Pinned revisions in the text match `pins.json`. No clipping/undefined refs.

## Non-blocking findings

- N1: PROOF.md's smooth/strict-curvature route is informal and correctly excluded from both formal and paper claims. Keep it excluded if the parent revises.
- N2: The formal upper bound is α+1, weaker than the source's (correct) α(1+γ)/2; the formal never claims the source's bound, so no inconsistency. Optional future strengthening, no count impact.
- N3: `envelope_convex` is stated for all γ (log conventions for γ≤0 are irrelevant to its use at γ>1). Harmless generality.
- N4: My direct MathDB refetch was inconclusive (404/403 routing); the pinned same-day record was used. Parent should re-confirm MathDB 349140 still "open" at acceptance.
- N5: `threshold-numerics.json` is correctly labeled "Independent numerical evidence only, not proof"; the PROOF.md note about the failed 70-digit finite-difference at γ=1.01, α=0.01/γ (precision, not sign) is candid and no sign conclusion is drawn from it.
- N6: Minor wording: paper says the source "asks whether" β is convex; the source says "we also believe … still eludes us". Fair paraphrase; no action needed.

## Count

Count 22/30 unchanged by this review. Candidate credit 0 pending parent acceptance decision. No candidate/shared edits, no staging/commits, no external contact performed. Candidate bytes frozen (verified before and after).
