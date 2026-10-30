# Independent adversarial review — sharp 3×3 permanental Koteljanskii ratio

Reviewer: pi-permanental3-review · 2026-10-26 · solo, no children.
Target: `lanes/parent-permanental3` frozen at `frozen-review.json` exact bytes (commit d67bc7255b lineage). Credit 0; count stays 0; parent decides.

**Verdict: PASS all five gates. No decisive objections. Three minor findings (none mathematical).**

---

## 0. Byte-level integrity (precondition)

All 13 sha256 values in `frozen-review.json` were recomputed from the parent lane and **matched exactly**: the six `formal/*.lean`, `main.tex`, `paper.pdf`, `verification/audit.json`, `PROOF.md`, `check_algebra.py`, `algebra-check.json`, `provenance.json`. `paper.pdf` is byte-identical to `build/main.pdf`, and `build/paper-build.json` records the frozen `main.tex` hash — the PDF is the build of the frozen source.

## Gate SOURCE — PASS

Independently verified, not from the parent receipt:

- **Live primary**: DOI 10.37236/13098 resolves (HTTP 200) to the correct EJC article; Crossref confirms *Permanental Inequalities for Totally Positive Matrices*, EJC **32**(1), published 2025-01-31. I rendered **p. 13 of `published2025.pdf` myself and visually read**: Proposition 11, Eq. (49), `1/2 ≤ per(x₁₂,₁₂)per(x₂₃,₂₃)/(per(x₁₂₃,₁₂₃)per(x₂,₂)) ≤ 2`, followed by the exact sentence "The authors believe that even these bounds are not tight. The smallest and greatest values for (49) that we have found are **2/3 and 121/114**, respectively." The class is MTP₃ = totally positive 3×3 (paper §1) — the same class as the proposal.
- **arXiv v1** (2406.00963): same result is **Proposition 3.6**, Eq. (49), identical 2/3 and 121/114 sentence. Matches the claimed numbering discrepancy.
- **Slides** (`skandera-slides.pdf`): "Open Problems" slide displays the weak bounds and asks "**Problem: Find tight bounds** … on MTPₙ" — the explicit ask the proposal targets.
- **Sra 2609.39979v1, Introduction**: I read the passage: "the positive semidefinite matrix A with rows (1,1,0), (1,2,1), (0,1,1) has per(A)per(A{2}) = 8 < 9 = per(A{1,2})per(A{2,3})" — i.e. **R = 9/8 on the PSD/TNN boundary is already published**. Theorem 1.1 is for symmetrizable inverse M-matrices, a different class; no TP3 sharp range is asserted. Exactly as the parent states.
- **fischer.pdf** (author-hosted, PDF creation date and title page both **May 8, 2026**): §6 gives the TNN/HPSD matrix [[8,2,1],[2,1,2],[1,2,8]] with 137 < 144, i.e. R = 144/137; §6 contains no sharp-range statement.
- **FPSAC2025** (SLC 93B Art. 124): same weak bounds after Eq. (3.15), same 2/3 / 121/114 observation.
- **Pan–Skandera–Wang 2606.13162**: unit-interval-order class, parity-block inequality (∗) and a Bruhat bijection conjecture; no sharp (49)-ratio bounds. Different work, as claimed.
- **MathDB 363360**: independently fetched (mathdb.com/problems/363360). Title: "Total nonnegativity of the permanental analogue of the Sihong polynomial" = source **Conjecture 13** / arXiv Eq. (51). Status open, 0 solutions. It is a **different question** from the sharp 3×3 ratio; the candidate's explicit non-resolution disclaimer is accurate and necessary. Eligibility is therefore assessed (and here granted) as the source paper's *own* optimal-constant question (Prop 11 remark + slides problem), with the honest caveat that this question is explicit but **not a numbered Problem/Conjecture** in the published paper.

*Coverage recorded honestly*: no MathSciNet/zbMATH; no full-literature full-text search; same-month work cannot be excluded for the very recent Sra/fischer items. No absolute priority claim is made.

## Gate MATH — PASS

I wrote a **new** exact-arithmetic checker from scratch (`check/review_algebra.py`, `fractions.Fraction`, independent 6-permutation permanent, independent Cauchy-kernel `1/(xᵢ+yⱼ)` TP generator — not reusing the parent's script). **27/27 checks PASS** (log `check/review-algebra.log`):

- R invariant under the row/column normalization B_ij = a_ij·a₁₁/(a_i1·a_1j) on 300 exact TP matrices; normalization matches the claimed formula; first row/column equal 1.
- Both certificate identities ((x−1)(3N−2D) and (x−1)(9D−8N) expansions) hold **exactly** at 500 random rational points, and the lower identity holds for **free w** (no hidden parametrization); N−D = bc−2x².
- Normalized determinant = (x−1)d; all 19 minors of a generic positive-parameter instance positive.
- **All 19 minors strictly positive** for `upperFamily` at 4 rational t (det exactly 1) and `lowerFamily` at 4 rational ε (det exactly ε²); ratio formulas `(9t²+24t+30)/(8t²+24t+38)` and `(2+ε)(2+10ε+9ε²)/((1+ε)(6+20ε+9ε²))` exact; **per(lowerFamily ε) = 6+20ε+9ε²** (the Lean-corrected value, matching the final theorem/paper, not the stale intermediate formula).
- Limits: R(U(1/s)) = (9+24s+30s²)/(8+24s+38s²) < 9/8 approaching from below; R(V(ε)) > 2/3 approaching from above; both approach the claimed constants.
- **2/3 < R < 9/8 on 1000 exact rational TP (Cauchy) matrices** — an independent adversarial search found zero violations.
- Parent's small integer witness [[1,1,1],[1,2,9],[1,9,66]]: TP, R = 639/598. Sra boundary matrix: R = 9/8 exactly, not strictly TP, is TNN. Fischer matrix: R = 144/137. 121/114 ∈ (2/3, 9/8).
- Parent's `check_algebra.py` re-run from a neutral cwd: exit 0, reproduces the frozen `algebra-check.json` output; parent lane bytes unchanged (hash re-verified).

Hand-proof cross-check: the four minors used (entries; 12|12 → x>1; 12|23 → y>x; 23|12 → z>x; det → Δ>0) are exactly what the certificates consume; every summand of the lower certificate is strictly positive for x>1 (2x²(x−1)² > 0), and of the upper certificate (2x³(x−1) > 0; 2(x−2)²bc ≥ 0 suffices). Optimality iff-statements correctly reduce to the approach families.

## Gate FORMAL — PASS (fresh isolated replay, own copy)

- Copied the whole candidate to `replay/candidate-copy`, cleared `build/verified`, ran the shared `verify_candidate.py` with the pinned Lean 4.34.1 and `.../2026-10-14/formal/.lake/packages`: **status PASS, 53 declarations, 6 modules**, main theorems `strictTP3_iff_allMinors` and `source_sharp_permanental_bounds`. Compiler and every pinned dependency revision (mathlib d13f23b… + 8 deps) verified by the script; receipt sha256 **641a5be6…** is byte-identical to the parent's `verification/audit.json`.
- My own checks on top of the script: forbidden tokens (sorry/admit/axiom/unsafe/native_decide) **absent**; my independent declaration count 13+6+16+10+2+6 = **53**; **53/53** `#print axioms` reports, all exactly {propext, Classical.choice, Quot.sound}; per-module `.log` files empty (compiled with `-DwarningAsError=true`).
- I read every declaration and verified semantics against the proposed ONE result: `per3`/`per2` are actual 6-/2-term permutation sums, proved equal to Mathlib `Matrix.permanent` (S₃/S₂ enumerated by `decide +kernel`); `sourceRatio A = per(A|₁₂,₁₂)·per(A|₂₃,₂₃)/(per A · a₂₂)` literally; `AllMinorsPositive` quantifies over **every increasing row/column selection of size ≤ 3** and is proved equivalent to `StrictTP3`; the endpoint conjunction contains the strict universal bounds **plus both optimal-constant iff statements** with no normalization hypotheses. The endpoint statement matches the proposed result exactly.

## Gate NOVELTY + ELIGIBILITY (serious, bounded) — PASS

- **Uncounted items correctly excluded**: the 9/8 boundary value (Sra intro — independently re-read), the 144/137 example (fischer §6 — independently re-read), R≤1 failures and 121/114 as observation. The proposed credit is only the **universal optimal strict bounds for all TP3**.
- **Searched for subsuming known results**: all citations of the source found (Semantic Scholar: 3 — Sra; Mashreghi–Nasri–Vishwakarma JMAA 2026 (convolution/entrywise calculus, no Koteljanskii/permanent-inequality content — checked abstract); Skandera's own Barrett–Johnson paper; OpenAlex: 1) — none states sharp TP3 bounds. arXiv API sweeps (2026-10-26) of abstracts containing "permanental" (60 most recent) and "Koteljanskii" (all 7) — no other candidate. Author follow-ups read (FPSAC2025, fischer.pdf, Pan–Skandera–Wang). MathDB 363360 shows 0 solutions; nothing inferred from its emptiness.
- **No immediate-or-subsumed theorem found**: no known result makes 2/3 < R < 9/8 on TP3 immediate. Sra's positive theorem is a different class (inverse M-matrices, where R ≥ 1 holds); the density remark in the source (Eq. 11) transfers TP bounds to TNN but does not supply the constants.
- **Eligibility**: granted as the source paper's explicit optimal-constant question (Prop 11 remark + slides problem), with the recorded caveat that it is informal rather than a numbered problem, and with MathDB 363360 explicitly *not* claimed. I found no mislabeling in the candidate's framing.
- Honest scope: bounded sweep; no absolute priority claim possible or made.

## Gate MANUSCRIPT — PASS (with one cosmetic slip)

- Rendered and **personally inspected all 3 pages** of `paper.pdf` (110 dpi PNGs in `evidence/pages/`): clean layout, no overflow, no undefined references; 3 pages as claimed.
- Theorem 1 matches the Lean endpoint including both "Equivalently" iff-lines; §2 normalization, scaling factor r₁r₂²r₃c₁c₂²c₃, and both certificate displays match the Lean `lower_certificate`/`upper_certificate` term-by-term; §3 families match `upperFamily`/`lowerFamily` including det U = 1, det V = ε²; §4 gives correct attribution and explicitly disclaims the known 9/8 boundary value, 144/137, and the R≤1 failures; the Lean scope paragraph (53 declarations, six modules, pinned revision, no numerical substitutes) is accurate; MathDB 363360 is correctly described as a different, unresolved question.
- References check out against the consulted PDFs, including the May 8, 2026 date of the author-hosted Barrett–Johnson manuscript.

**Minor finding M1 (cosmetic, no mathematical impact).** In PROOF.md §1 and paper §3 the nine 2×2 minors are presented "in lexicographic row-pair and column-pair order", but two entries are interchanged: the correct array is row (1,3)×(2,3) → w−x−**c** and row (2,3)×(1,3) → w−x−**b**; the documents place them swapped. Both values appear, both are positive, and all-19-minor positivity is verified — purely a display-order slip.
**M2.** Ref [3] could additionally cite the published Linear Multilinear Algebra version (doi:10.1080/03081087.2024.2446784) alongside the dated author manuscript.
**M3.** The eligibility anchor is an explicit but informal source question (remark + slide problem), not a numbered Problem/Conjecture — worth one clarifying sentence in any final packet.

## Decisive objections

**None.**

## Per-gate verdicts

| Gate | Verdict |
|---|---|
| SOURCE | **PASS** |
| MATH | **PASS** |
| FORMAL | **PASS** (fresh isolated replay, own copy, 53/53 declarations, 3 standard axioms only) |
| NOVELTY + ELIGIBILITY | **PASS** (bounded scope honestly recorded; no decisive prior art; endpoint items correctly uncounted) |
| MANUSCRIPT | **PASS** (cosmetic M1) |

Count remains 0; this review neither edits the candidate, ledger, nor acceptance, stages/commits nothing, and initiates no external communication.
