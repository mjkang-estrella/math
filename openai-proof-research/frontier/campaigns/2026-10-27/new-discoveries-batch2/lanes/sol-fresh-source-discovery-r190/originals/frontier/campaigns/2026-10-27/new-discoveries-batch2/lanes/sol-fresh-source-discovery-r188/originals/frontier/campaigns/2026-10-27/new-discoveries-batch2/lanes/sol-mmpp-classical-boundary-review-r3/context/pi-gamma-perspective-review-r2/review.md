# Independent r2 substantive re-adjudication — gamma-level convexity candidate (root-gamma-level-r1 @ 4bffd200db)

Reviewer: pi-gamma-perspective-review-r2 (Pi GLM-5.3-Flash-EXL3, thinking high, standard/default speed, no ultrafast). SOLO, no children. No git operations; no shared/parent/other-lane edits; no external postings. Frozen parent bytes re-verified unchanged (all six provenance hashes recomputed and matching before this review).

## Decision

**PASS — substantive eligible.** The exact all-parameter perspective reduction is **not** a routine classical corollary in this campaign's exclusion sense. Recommendation: proceed to the remaining gates (literal Lean endpoint incl. the absent GammaHasSum/strict-antitonicity/level-existence bridges, paper, final independent review, extracted replay). The stopped Euler-formal worker was correctly stopped; the deferral is now lifted at the substantive level. **No acceptance, count, or candidate/ledger edit is made here** — root alone integrates.

Credit-zero obligations (binding on any future paper/formal text):
- The classical perspective-convexity theorem (Rockafellar 1970; Combettes arXiv:1610.01552v3 Eq (1.1), Prop 2.3(ii), Prop 2.13, Section 4) gets **no credit**; it is a tool.
- Jensen's inequality, the Euler/Weierstrass product, and inverse-function convexity duality get **no credit**.
- The weighted-Jensen argument in PROOF.md **must not** be advertised as a new convexity tool. The root's PERSPECTIVE-OBJECTION.md correction stands: it is the standard proof of perspective convexity with adjusted weights, applied on the shift lattice. The preliminary review's claim that "Σ g((s+m)/x) is not a perspective sum and joint convexity fails" was **wrong** — multiplying the level inequality by the positive variable x gives exactly a sum of classical perspectives of shifted g; I verified the resulting joint convexity numerically (see checks/perspective_check.py: Hessian positive definite at 30 random points in 0<x<s).
- The discovery content is the **exact identification and assembly** that resolves the source question, not a new tool.

## Why this is the correct exclusion category — and why it is not excluded

### 1. What "routine classical corollary" has meant in this campaign's actual exclusions

Every clear classical exclusion (Hoggatt, An-Djokovic, zhou-coefficient, 329167, 338822, 372393, …) had the same structure: **a published theorem about the same objects already carried the mathematical difficulty**, and the source question dropped out by specialization or a mechanical bridge — Lamprecht Thm 30 + Garloff–Wagner for the exact q-Hoggatt summand family plus the paper's own induction; Postnikov's theorem for the exact monomial pairing; Xu–Zhao Lemma 4.4; Skorski Cor 3; Jiang–Qi Thm 5.3. In each case the cited theorem is *about the problem's own objects*.

Here the generic theorem (perspective convexity) is **about no gamma object at all**. I read the actual Combettes v3 body today (archived, hashed): it contains no statement about level sets, level curves, level radii, inverse functions, or sums of shifted perspectives (verified: zero such content; the perspective-convexity equivalence is credited to Rockafellar [57] as classical). A candidate result is not made "routine" by the *availability* of a generic tool any more than #23 was; otherwise nearly every first-batch acceptance (which credits classical tools) would be excluded.

### 2. The three pieces of non-contained content

(a) **Exact normalization bridge.** Γ(h)Γ(h+2x)/Γ(h+x)² = c ⟺ F(x,s)=Σ_{m≥0} −log(1−x²/(s+m)²) = log c (Euler product), and then xF = Σ_m x·g((s+m)/x) — a sum of classical perspectives composed with affine shifts. The multiplication by x>0 — turning a *non*-perspective sum into a perspective sum — is the step the preliminary review missed and the root corrected. It is an identification of the literal source object with a convex-analytic form; no published theorem performs it.

(b) **Two-shift strictness lemma.** Convexity of {xF − x log c ≤ 0} alone gives a convex radius, not a strictly convex one. The strict gap relies on: equality of both shifted ratios (s₀+m)/x₀ = (s₁+m)/x₁ at m=0 **and** m=1 forces x₀=x₁ (verified symbolically in my checks). Nothing of this kind exists in the perspective literature I inspected.

(c) **Assembly**: strict concavity of ρ ⟹ strict convexity of s_c by inverse duality ⟹ h_c = s_c − id on all of (0,∞), for every c>1 with one proof.

Each piece is short; **shortness is not routine** (explicit campaign instruction), and the accepted #23 precedent is exactly this shape.

### 3. Honest comparison with accepted #23 (Simon threshold, MathDB 349140)

#23 was an exact separate source question (final paragraph of Simon §3), resolved by an exact variational reduction identifying the literal infimum with a supremum, whose convexity is "standard perspective convexity after reparameterization" (its own PROOF.md §4 wording). Its acceptance record says: "Independent reviewer judges the exact reduction substantive, at the minimal end of the campaign standard; final perspective step classical," with perspective/supremum tools uncredited. **Accepted with credit 1.**

The present candidate is the same eligibility shape, with two differences, both neutral-to-favorable: (i) the source question here is an explicit open *belief* (Remark 16(a)) whose own method provably fails on the missing interval (H(x,y,z)>0 route via 1/ψ′ convexity), whereas #23's target was an explicit question; (ii) the missing interval (0,1) is load-bearing in the source's own Theorem 23 (log-convexity/log-concavity boundary at α<1), so the completion is not a dead endpoint. Consistency with #23 requires the same verdict; distinguishing them would need a principled criterion I cannot find, and none was articulated in any exclusion record.

### 4. Strongest contrary case (stated at full strength, per task)

A strict evaluator can argue: the Euler product representation of the log gamma ratio is classical and known to the source authors; once it is written, "multiply by x and cite perspective convexity" is a two-line quasiconvexity observation an expert could find in an afternoon; the only new content is the small two-shift lemma; hence the result is a routine classical corollary *in the generic sense*, and the case is Hoggatt-like (supply the right classical input, the question collapses). The source's failed method shows hardness only against the second-derivative route, not against all classical tools. Under this reading, even the c=2 endpoint resolution is routine and excluded.

**Why I reject it.** In Hoggatt the supplied inputs were published theorems *about the same summand family* that encoded the difficulty; the bridge was specialization. Here no published theorem encodes "the level radius of a convergent shifted-perspective sum is strictly concave"; the generic literature gives non-strict convexity at most, and the strictness mechanism is new. The "afternoon" plausibility of a proof is not an exclusion criterion this campaign has ever applied — it would also have excluded #23 (whose route, once found, is equally short) and several other accepted outcomes. The decisive question under the counting standard is whether the result is an *equivalent corollary of a known theorem*, and it is not: the known theorem is generic, the reduction is exact, and the strictness is uncontained. I also verified the mechanism end-to-end numerically (perspective-sum joint convexity, bridge, strictness algebra) — the reduction is real, not a heuristic.

### 5. Public resolution vs routine corollary — distinguished

No public resolution of Remark 16(a) was found in my independent bounded screen (below). That absence is *necessary but not sufficient*; the substantive adjudication above is what clears novelty-of-mechanism. Both prongs now point the same way.

## Per-gate status (this review's scope)

| Gate | Verdict | Notes |
|---|---|---|
| SUBSTANTIVE (exact all-parameter perspective reduction) | **PASS** | Adjudicated above; all-c>1 is ONE family, c=2 the source instance; no parameter-instance credit. |
| Mechanism correction (root objection) | **CONFIRMED** | Preliminary review's "not a perspective sum" reasoning was erroneous; root's xF perspective-sum bridge is correct and is now the primary mechanism characterization. The weighted-Jensen proof is the standard perspective proof with adjusted weights. |
| MATH (bridge pieces) | **PASS (my own checks)** | g″=2(3u²−1)/(u²(u−1)²(u+1)²)>0 (symbolic); Euler bridge at 6 points incl. x/s→1 within tail bound; xF jointly convex (30-pt Hessian); xF=Σ x·g((s+m)/x) identity; both-shifts equality ⟹ x₀=x₁ (symbolic). Diagnostics, not certificates; the full written proof was already double-checked by the preliminary review. |
| SOURCE (primary perspective claim) | **PASS** | Combettes v3 actual body read (archived PDF, pp. 1–3 + Prop 2.13 + §4): Eq (1.1), Prop 2.3(ii) "ϕ̃∈Γ₀(ℝ⊕G)", Prop 2.13 affine composition, §4 integral functions; convexity iff credited to Rockafellar [57]. Matches root's citation; no subsuming content. arXiv v4 remains latest version (abs page); JMAA VOR identity was closed by the preliminary review from the TU Wien open-access copy. |
| NOVELTY (bounded follow-up/registry screen) | **PASS at bounded level** | Screen below; no public resolution or subsuming lemma found. Residual risk recorded as a novelty limit, not a HOLD. |
| FORMAL | Not adjudicated here | Root 4-module 17-declaration support (fresh replay PASS, std3 only) is support only; the actual GammaHasSum, strict-antitonicity and level-existence bridges are **absent** and are the real endpoint work; no full FORMALPASS exists or is claimed. |

## Bounded independent novelty/follow-up screen (scope and limits)

- trureturing registry for this exact paper (the-omega-institute.github.io/trureturing-mdbook, Library/Problems): only the **Kummer modulus question (Remark 6)** is tracked — refuted 2026-10-26 by their quadratic counterexample, a *different* problem. No record on Remark 16(a)/h-convexity.
- Citing literature: closest citing work Ferreira–Simon, "Mittag-Leffler functions and convex ordering" (arXiv:2512.04940, Dec 2025) — convex ordering of E_α; does not touch h or Remark 16(a). Author pages (dm.uniba.it Garrappa) list no follow-up on h-convexity.
- General gamma-ratio convexity genres surfaced by search (log-convexity of series in gamma ratios JDE 2013, LCM ratios PMC, gamma bounds RGMIA, Merkle convexity): none treats an implicit level-curve radius of a gamma ratio.
- Limits: no Scopus/WoS/MathSciNet; no exhaustive citation crawl; Orlicz-means literature only partially screened (carried over from the preliminary review's screen, which additionally inspected Himmel–Matkowski in full, MSE 1337411, inverse-σ_k and epigraph-characterization genres). Empty results are not proof of absence; no worldwide-priority claim.

## Gaps that remain open (unchanged, for root's gates)

1. Literal Lean endpoint: GammaHasSum (partial sums → infinite series for the log gamma ratio), strict antitonicity, level existence — all absent; the 4-module support assumes them explicitly.
2. Paper and deterministic packet + fresh extracted replay.
3. All numerics (root's, preliminary review's, mine) are diagnostics, not interval certificates.
4. Bounded novelty screen only; the abstract-lemma residual risk is recorded above and in the preliminary review.
5. This review does not resolve v4 Conjectures 25/26, the non-real-zero boundary f, or any source complete-Bernstein classification; 'log E up to translation' receives no credit.

## Integrity

Wrote only in lanes/pi-gamma-perspective-review-r2/ (review.md, provenance.json, checks/, sources/). Frozen root lane byte-identical before review (hashes recomputed, matched provenance). No git, no shared edits, no external messages. Only public reads.
