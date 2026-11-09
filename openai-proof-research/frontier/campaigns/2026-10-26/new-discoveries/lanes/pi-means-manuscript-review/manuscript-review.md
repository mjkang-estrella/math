# Final manuscript review — candidate `classical-means` (MathDB 338823)

Reviewer: pi-means-manuscript-review lane (independent Pi review sub-agent, GLM5.3 Flash, standard speed, no children started).
Date: 2026-10-26.
Object under review: the FINAL manuscript bytes `main.tex` and `paper.pdf` at the candidate root, plus the full packet they reference.

**Authorship declaration: I authored none of the five Lean modules, none of the verification code, and none of the manuscript or PDF. I am not the parent, the new-screen worker, or the original pi-means-review reviewer. This review is performed independently against the bytes themselves, not against the parent's verdict.**

## Verdict

**PASS — no decisive objection.** Separate gate results below. Three non-blocking notes are listed; the parent may fix them or not, at its discretion. I change no acceptance state and no count.

---

## Gate A — Exact final hashes and byte identity: PASS

Verified by my own `sha256sum` on the candidate root files:

- `main.tex` = `477fbf7382e8f746dd71c698a743af4ac9b29fd7f2a0f39da20b5d6c0c060dfb` — matches the target exactly.
- `paper.pdf` = `14d879c869cab2a6bc5cb8ac1a9a3ff96202f580d4de7cb785da59935d1cf32f` — matches the target exactly.

Both match `verification/paper-qa.json` (`tex_sha256`, `pdf_sha256`) and the values in the review request. `git status` on the candidate tree is clean; commit `b5aff68e42` ("Prepare reviewed classical-means manuscript and document source exclusions") contains main.tex/paper.pdf and the reviews, and `git diff 88c5c34a01 b5aff68e42 -- .../formal/` is empty: the frozen five-module certificate is byte-identical to the original certificate commit `88c5c34a01`, whose five `.lean` hashes I also re-verified against both audit receipts.

## Gate B — Source fidelity: PASS

I personally inspected the rendered source pages (read-only copies in `lanes/new-screen/third-discovery/sources/`, PDF SHA `e80be061…c232` re-verified by me):

- **p.1892**: literal definitions H=2xy/(x+y), G=√(xy), A=(x+y)/2, Q=√((x²+y²)/2) for positive x,y — identical to the manuscript's Section 1 display and to the Lean `arithmetic/geometric/harmonic/quadratic`. Theorem 1.1 proves AG ≥ QH and the integer-n power-sum inequality; Remark gives A+G ≤ Q+H.
- **p.1894**: Conjecture 1.5 read verbatim: inequality (4) holds for all negative real n and all n ≥ 1/2, neither direction universal on (0,1/2). This matches the manuscript's characterization word-for-word in substance. The preprint numbering (Conjecture 1.6) is correctly stated.
- The manuscript's claim that the source's proposed range is refuted **on the whole interval 1/2 ≤ n < 1 with actual positive inputs** is accurate: the formal witnesses use concrete positive pairs, not endpoint or wording technicalities. The n=0 point (trivial equality 2=2) is beyond the source's "negative n" phrasing but is folded into the single classification, not counted separately.
- `sources/338823.json` matches the arXiv/published statement; the MathDB snapshot records all solution-bearing arrays empty, `progress` null, status `open`, correct UUID `d0d7b2e3-8f6a-49ce-b353-d1c8d4e85ee8`. I did not take any widget status as evidence; the original reviewer's live field-by-field retrieval is recorded in `reviews/independent-review-provenance.json`.

The manuscript does **not** rely on the invalid inferences the parent corrected: it nowhere writes AG=QH as a source relation (it writes and proves QH ≤ AG in (3), and uses AG ≥ QH in the n≤0 argument — the correct direction); it never uses zero citation counts or the 2026 nested-means paper as proof of openness (Section 5 explicitly disclaims both); the erroneous per-module prose split from the original report does not appear in the manuscript (it states only the correct total 34).

## Gate C — Mathematics and proof detail: PASS (every item checked by hand)

I re-derived each item independently:

1. **AH=G² and Q²=2A²−G²**: ((x+y)/2)(2xy/(x+y))=xy=G²; 2A²−G²=(x+y)²/2−xy=(x²+y²)/2=Q². ✓
2. **Normalization c=A/G≥1, (H,G,A,Q)/G=(1/c,1,c,√(2c²−1))**: H=G²/A ⟹ H/G=1/c; Q²/G²=2c²−1. ✓
3. **Sum comparison**: q²−(c+1−c⁻¹)² = (c−1)³(c+1)/c² (expanded and confirmed: c⁴−2c³+2c−1 over c²), ≥0 for c≥1, both sides positive ⟹ Q+H ≥ A+G. ✓
4. **Product comparison QH ≤ AG (an inequality, not equality)**: equivalent to q ≤ c², i.e. c⁴−q²=(c²−1)²≥0. ✓ The manuscript and Lean use the inequality direction correctly in the logarithmic step; no equality premise survives anywhere.
5. **Two-point increasing convexity (Lemma 2)**: c′=a+b−d gives d ≤ b ≤ a ≤ c′ ≤ c and a+b=c′+d; the chord inequality on [d,c′] for a and b (barycentric coordinates λ=(a−d)/(c′−d), 1−λ) sums to f(a)+f(b) ≤ f(c′)+f(d); monotonicity gives f(c′) ≤ f(c). Sound. The Lean `two_point_convex`/`two_point_convex_mono` implement exactly this via mathlib `ConvexOn` secant monotonicity and `ordConnected` intermediate point. Self-contained and correctly labeled classical.
6. **n≥1**: (A,G,Q,H) satisfy d≤b≤a≤c and a+b≤c+d; t↦t^n increasing convex. ✓
7. **n≤0**: d=n·log Q ≤ b=n·log A ≤ a=n·log G ≤ c=n·log H (multiplication by n≤0 reverses the log order), and a+b=n·log(AG) ≤ c+d=n·log(QH) because AG≥QH and n≤0. exp is increasing convex ⟹ G^n+A^n ≤ H^n+Q^n. Correct weak-majorization direction; equality at n=0. ✓
8. **Witness pair (5)**: x_c=c+√(c²−1), y_c=c−√(c²−1): product 1, sum 2c, √(c²−1)<c so both strictly positive; realizes A=c, G=1, H=1/c, Q=√(2c²−1) for every c≥1. ✓
9. **Defect and derivatives**: D_n(c)=(2c²−1)^{n/2}+c^{−n}−c^n−1 equals Q^n+H^n−A^n−G^n on the pair. D_n(1)=0; D′_n(c)=2nc(2c²−1)^{n/2−1}−nc^{−n−1}−nc^{n−1}; D′_n(1)=0; differentiating term-by-term at c=1 gives 4n²−6n+n(n+1)−n(n−1)=4n(n−1). ✓ No residual normalization/derivative hypothesis is assumed: bases are positive near c=1, so real powers are smooth there.
10. **Neighborhood/MVT sign**: for 0<n<1, D″_n(1)=4n(n−1)<0 and D′_n differentiable at 1 with D′_n(1)=0 ⟹ D′_n(c)<0 for c>1 near 1; MVT on [1,c] gives D_n(c)<D_n(1)=0, i.e. an actual positive-input failure for every 0<n<1. Sound. Lean `exists_normalized_failure` formalizes exactly this (sign of `deriv (firstDeriv n) 1`, `strictAntiOn_of_deriv_neg`, `StrictAntiOn` on [1,b]). My own numerics confirm D_n(1.001)<0 for n∈{0.1,0.5,0.75,0.99}.
11. **Half-power witness**: x=4+√15, y=4−√15 gives xy=1, x+y=8, so (A,G,H,Q)=(4,1,1/4,√31); forward would require 3 ≤ 31^{1/4}+1/2; 31<(5/2)⁴=625/16 ⟹ 31^{1/4}<5/2 ⟹ RHS<3. Verified numerically: 3 vs ≈2.8596. Lean `explicit_half_power_failure` matches. ✓
12. **Reverse, n>0**: ε=(5/4)^n−1>0, c=max{2,(2/ε)^{1/n}} ⟹ εc^n≥2 (case check: if the max is the second arm equality holds; if it is 2 then 2^n≥2/ε). For c≥2, (2c²−1)−(25/16)c²=(7/16)c²−1≥3/4>0 ⟹ q≥(5/4)c ⟹ Q^n≥(1+ε)c^n≥c^n+2>c^n+1=A^n+G^n. Forward strict on the pair ⟹ reverse fails. ✓
13. **Reverse, n<0**: c=max{2,3^{1/(−n)}} ⟹ H^n=c^{−n}≥3, A^n=c^n≤1, G^n=1, Q^n>0 ⟹ Q^n+H^n>A^n+G^n. ✓ n=0: both sums 2. ✓
14. **Both strict signs on (0,1)**: the n>0 reverse-witness construction is valid for every n∈(0,1) and the defect witness gives the opposite strict sign; combined correctly. ✓
15. **50k-scale random numerical spot checks** of my own at n∈{−2,−1,−0.5,0,0.1,0.3,0.5,0.75,0.99,1,1.5,2,3} agree with the classification; no counterexample to the theorem and no failure of the witnesses.

No gap found. All quantifiers are over literal positive inputs; no hypothesis smuggling.

## Gate D — Formal scope vs manuscript claims: PASS

`verification/audit.json` (parent) and `verification/independent-audit.json` (fresh Pi replay) agree: Lean 4.34.1, compiler commit `5045d005…`, mathlib `d13f23b7…`, warnings-as-errors, per-module counts **12, 4, 7, 6, 5 = 34** (the authoritative receipt split, matching the corrected addendum; the erroneous 10+5+8+6+5 prose split appears nowhere in the final packet except as corrected history). I re-hashed all five current `formal/*.lean` files: identical to both receipts. `declaration-types-and-axioms.log` lists exactly 34 declaration types and exactly `[propext, Classical.choice, Quot.sound]` on every one; a grep found no `sorryAx`/custom axiom/`native_decide`/`unsafe` tokens. A full recompilation is unnecessary: no source file changed since the audits (git diff empty), so the receipts bind to the current bytes.

Cross-check of manuscript claims against actual endpoint types:

- Theorem 1 eq. (1) ⟷ `source_exponent_classification (n) : UniversallyValid n ↔ n ≤ 0 ∨ 1 ≤ n` — exact match, including the literal mean definitions and ∀ x y > 0 quantifier.
- Theorem 1 eq. (2) ⟷ `source_converse_exponent_classification (n) : ConverseUniversallyValid n ↔ n = 0` — exact match.
- `source_full_classification (n)` states both equivalences with **no** mean/derivative/normalization/witness premise — the manuscript's Section 5 description is accurate.
- Witness theorems (`source_failure_all_intermediate`, `exists_strict_source_positive`, `exists_strict_source_negative`, `explicit_half_power_failure`) all produce strictly positive actual inputs via `normalized_pair` — matching the manuscript's "actual positive inputs" language.

## Gate E — Prior-credit / novelty wording: PASS

- Classical convexity/weak majorization, the source's integer theorem and its sum/product comparisons, and the n=0 equality are all explicitly credited; no separate outcome is claimed for them, for individual witnesses, or for either direction. One combined source-question resolution, consistent with the strict accepted tally of 7/30 and credit 0 pending gates.
- The bounded-novelty language is honest: subscription services unavailable, Sándor survey partially inspected, citation counts and search absence explicitly disclaimed as priority evidence, no exhaustive worldwide claim. My own independent searches (responseIds in provenance.json) surfaced no resolution or subsuming theorem; Jameson's abstract confirms it compares M_p with combinations of A and G — a different comparison, correctly described as Theorems 1–2 in the manuscript, with the bounded access language ("complete publisher HTML … direct PDF retrieval returned HTTP 403") precise and not overclaiming PDF access.
- The 2024 chain paper (actual PDF SHA `f57a53ff…1a33` re-verified) contains only fixed nested comparisons (verified from its own text: the eight-term chain, Muirhead remarks, two questions) — no real-exponent classification, and no claim from it is assumed. The 2026 Phuc–Thuy paper (SHA `74e12588…0246f` re-verified) is likewise fixed nesting. The manuscript correctly uses them as examined related comparisons, not as openness evidence.

## Gate F — Bibliography: PASS

[1] Meštrović–Andjić: Resonance 28(12) (2023) 1891–1897, DOI 10.1007/s12045-023-1726-x, online January 31, 2024, plus arXiv:1804.00542v1 with both conjecture numbers — all details confirmed via independent retrieval (Crossref/Scifaro/tandfonline metadata agree; 0 citations noted but not used). [2] Chain paper: The Teaching of Mathematics 27(1) (2024) 27–32, DOI 10.57016/TM-XDVI2817 — matches the actual PDF's own front matter exactly. [3] Jameson: American Mathematical Monthly 130(3) (2023) 276–278, DOI 10.1080/00029890.2022.2153560 — matches publisher records (published online 11 January 2023). No missing or fabricated references; the Phuc–Thuy paper is documented in NOVELTY.md/provenance rather than the bibliography, which is acceptable since the manuscript's text does not depend on it.

## Gate G — Rendered layout: PASS

I rendered all four pages myself from the verified `paper.pdf` bytes (pdftoppm) and inspected each: title/abstract, Section 1 theorem block, all displayed formulas, Section 5 and References begin together on page 4, all legible, no clipping, overlap, missing glyphs, or mis-numbered references. `build/main.log` shows **no overfull boxes and no undefined references**; the only TeX advisories are two mild underfull hboxes at the bibliography (badness 3713 and 3189, lines 245–249), invisible in the render and purely cosmetic. `build/paper-build.json` exit 0, issues empty. Cross-references (3), (4), (5), (6), Lemma 2 resolve correctly on the rendered pages.

## Non-blocking notes (parent's discretion)

1. **Underfull hboxes** (badness ≤ 3713) at the final bibliography paragraph. The parent's "no overfull boxes" statement is accurate as written; no action required, but recording for precision.
2. **§4 phrasing**: "Since H^n > 0, the forward inequality is strict there" — the strictness already follows from the displayed chain Q^n ≥ c^n+2 > A^n+G^n; H^n>0 is redundant (though true and harmless). Cosmetic wording only; the Lean proof (`exists_strict_source_positive`) is correct as formalized.
3. **Lemma 2 prose**: "Suppose d ≤ b ≤ a ≤ c and a+b ≤ c+d *in an interval*" is loose wording for "all four points lie in an interval on which f is increasing and convex"; the formal statement and proof impose exactly the right ordConnected/ConvexOn/MonotoneOn conditions. No mathematical issue.

## Objections

None decisive.

## Recommendation

- Exact hashes/bytes: **PASS**
- Source fidelity: **PASS**
- Mathematics/proof: **PASS**
- Formal scope cross-check: **PASS**
- Prior-credit/novelty wording: **PASS**
- Bibliography: **PASS**
- Rendered layout: **PASS**

The manuscript is eligible to proceed to the parent's final extracted-packet build/replay before any count update. This review changes no acceptance state, count, or ledger; the candidate remains at credit 0 until the parent's gates complete. No publication, posting, upload, author contact, or external message occurred from this review.
