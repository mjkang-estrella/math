# Independent review — cstar-polynomial (frozen commit 1b388f77e5)

Reviewer: review sub-agent (pi-cstar-polynomial-review), STANDARD/default speed, Pi/GLM5.3Flash only, no children. Date: 2026-10-26 (review session). Candidate credit proposed: 0 pending this verdict. I did not author the candidate; I edited nothing outside my lane.

## Verdict summary

**ELIGIBLE — all five gates PASS.** One combined counterexample construction (single witness triple (R, −2R, R) with critical factors (I, −I) in M₂(C), R = [[1,2],[0,−1]]) refutes Krishna arXiv:2206.06653v1 Conjectures 2.1, 2.3 and 2.4 as literally stated. Treated as ONE outcome throughout; the six defect evaluations are consequences of one construction, not six directions. Under the strict 10→11 standard this candidate is eligible for acceptance; counting/integration is the parent's job, not mine.

## Gate 1 — SOURCE: PASS

- I personally downloaded https://arxiv.org/pdf/2206.06653v1 (my lane `sources/2206.06653v1.pdf`): SHA256 `16c6521f2dd722ec580dcaaa9136a0d7e10ecad368a0887acff1563e3e912684` — matches the frozen claim exactly.
- Read all 4 pages (pdftotext + 300 dpi renders of pages 2–4, visually inspected by me: `sources/page-2-2.png` … `hi-2/3.png`, crops `crop-p2-conj12.png`, `crop-p3-conj23.png`).
- Source facts verified directly: P′ is the ORDERED deletion sum, defined ∀z ∈ A (p.2); Conjecture 2.1 (pp.2–3) has hypotheses only "d ∈ N∖{1}" and the factorization P′(z) = d(z−b₁)⋯(z−b_{d−1}) on A — NO normality, self-adjointness, invertibility, distinctness or commutation condition; Conjecture 2.3 additionally assumes Σa_j = 0; Conjecture 2.4 (pp.3–4) mixes n/d in two summation indices (Σ_{j=1}^n), immaterial here since n = d = 3.
- Coefficients pinned at 300 dpi: 2.1 RHS = (1/d²)[Σa_j][Σa_j]* + ((d−2)/d)Σ a_j a_j* (and star-reversed); 2.3 RHS = (2/d²)(Σ a_j a_j*)² + ((d−4)/d)Σ(a_j a_j*)² (and star-reversed); 2.4 has five term groups ((d−6)/d)Σ(a_j a_j*)², (1/d²)(Σ a_j a_j*)², (1/d²)·corr·corr*, (2/d)Σ a_j·sh_j·sh_j*·a_j*, −(4/d³)Σ a_j·(Σa)·(Σa)*·a_j* (and star-reversed), with corr = Σa_j² − (1/d²)(Σa)², sh_j = a_j + (1/d)Σa. **The formal definitions match these term-for-term, including multiplication order.**
- arXiv abs page: only [v1], submitted 14 Jun 2022, "4 Pages, 0 Figures", DataCite DOI only, no journal-ref, no replacement/withdrawal. No published or current companion revision restricting the roots or resolving the conjectures was found.
- MathDB: fresh GETs of /api/posts/355008 and /355009. status "open", progress null, solutions/model_attempts/human_solves/comments/replies/formulations/attachments all empty. My snapshot SHA256s (`a48fd670…`, `c0c1404d…`) match the parent's provenance exactly. The posts' reference note "Status: solved … 'This was proved by Cheung and Ng in 2006'" misreads the source: Cheung–Ng proved the SCALAR Conjecture 1.2 (de Bruin–Sharma), not the C*-algebraic statements. I did not rely on those summaries.
- Nearest priors read (actual PDFs): Cheung–Ng 2006 (author copy `hkumath.hku.hk/~ntw/publications/paper19.pdf`, sha256 `601eabfdb4047fafbfa0ad752322582b4847f104396ed4cbeb4451acc816dac9`; the task-brief HKU-hub URL is Cloudflare-blocked from this environment — recorded as an access limit) — scalar complex polynomials, no C* content; Kushel–Tyaglov 2016 (`arxiv.org/pdf/1512.07983`, 14 pp.) — scalar; its Corollary 1.2 independently confirms the (2/n²)(Σ|λ|²)² coefficient shape Krishna uses; Bratteli–Jorgensen–Kishimoto–Robinson 1984 (Ann. Inst. Fourier 34.3, 155–187) — complete dissipations / CP semigroups / negative-definite maps, a different "Schoenberg theorem", no polynomial root moments.

## Gate 2 — MATH: PASS (my own codepaths, different from the parent's)

Parent uses fractions.Fraction literal-expression evaluation + 100 sampled derivative checks. I used two structurally different exact codepaths (`math/reviewer_independent_check.py`, output `math/reviewer-check-output.json`):

1. **Universal identity, no sampling:** with z = [[x₁,x₂],[x₃,x₄]] GENERIC over ℤ[x₁..x₄] (exact polynomial arithmetic), I verified P′(z) = (z+2R)(z−R) + (z−R)² + (z−R)(z+2R) = 3(z−I)(z+I) = 3z² − 3I entrywise as a polynomial identity. This proves the factorization for EVERY complex matrix z, with zR/Rz cancelling separately and no commutation assumed. (An initial free-algebra-over-words variant I tried is strictly stronger than the source claim — I is central only modulo matrix-unit relations — and correctly failed; the generic-polynomial check is the right universal statement. Recorded for candor.)
2. **All six defects, own transcription** (pure integer matrices, denominators by explicit ×9 / ×27 scaling, written from the pages I read, not copied from `scripts/check_exact.py`): 2(H−I)=[[8,−4],[−4,0]], 2(J−I)=[[0,4],[4,8]], 2(H²−I)=[[56,−24],[−24,8]], 2(J²−I)=[[8,24],[24,56]], 14(I−H²)=[[−392,168],[168,−56]], 14(I−J²)=[[−56,−168],[−168,−392]]; H=RR*=[[5,−2],[−2,1]], J=R*R=[[1,2],[2,5]], R²=I, Σroots=0, S=6H, T=18H², C=6I, E=18I, critical-point sums 2I. Quadratic forms: −8 on (1,2)/(2,−1) for the first four, −392 on e₁/e₂ for the last two; all six real symmetric (Hermitian); roots and critical factors are genuine zeros.

**No loophole found.** The source's derivative IS the ordered deletion (not a Frechet/calculus derivative); the factorization hypothesis is satisfied by central, distinct, self-adjoint b's; all relevant expressions are Hermitian so the failure is genuine Loewner-positivity failure, not a non-Hermitian-order artifact; and I checked no root-count/order/degree escape (degree 3, d=3, d−1=2 critical factors).

**Robustness beyond the literal statement:** Krishna's scalar Conjecture 1.2 display (2/d²) appears to differ from Cheung–Ng's original display; under the alternative classical reading of 2.3 with coefficient (2/d) = 2/3, the defect becomes 18H² − 2I = [[520,−216],[−216,70]], det = 36400 − 46656 = −10256 < 0 (indefinite; e.g. quadratic form −490 on (2,5)). So the witness refutes BOTH readings of 2.3. The refutation does not depend on resolving Krishna's possible scalar misquote.

## Gate 3 — FORMAL: PASS (fresh isolated strict replay in my lane)

- Copied the frozen candidate to `replay/copiedCandidate/` and ran `verification/verify_candidate.py` with the prescribed lean-bin and packages. **PASS**, receipt `replay/copiedCandidate/build/verified/audit.json` — **byte-identical** to the frozen `build/verified/audit.json` (SHA256 `7f47050421d699672e1bfadaa004e5b8be99fbee6b9ac3030c53cdeaa41a7909`).
- Inventory verified: 36 declarations = PolynomialWitness 23 + FourthMoment 13; compiler Lean 4.34.1 (commit 5045d00…), mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 + 8 dependency pins verified clean; `-DwarningAsError=true`; forbidden tokens (sorry/admit/axiom/unsafe/native_decide) script-enforced absent.
- I read all 36 declaration TYPES and `#print axioms` outputs from my replay's `Checks.log`: every declaration depends only on propext, Classical.choice, Quot.sound. Key types: `derivative_factorization (z : M₂) : sourceDerivative roots z = 3 • ((z − critical 0) * (z − critical 1))` — universal ∀z ∈ M₂, NOT weakened to scalar or central z; `sourceDerivative` is the literal ordered deletion of the actual matrix roots; the 2.4 defect definitions include the full correction/shift/final terms with correct star ordering before simplification; `genuine_roots`/`genuine_critical_points` are actual evaluations; PSD bridge uses Mathlib `Matrix.PosSemidef` (ComplexOrder) via a negative quadratic form — the correct complex Loewner notion for M₂(ℂ); final closed endpoint `CstarPolynomial.source_all_three_conjectures_false` carries no residual premises (Σroots=0 ∧ genuine roots ∧ ∀z factorization ∧ ∀i critical zeros ∧ ∀k, Hermitian ∧ ¬PosSemidef).

## Gate 4 — BOUNDED NOVELTY: PASS with explicit limits

Searches and inspections (all in my lane `sources/`):

- Semantic Scholar API citations of 2206.06653: 2 records — arXiv 2206.09197 (C*-Casas-Alvero) and 2206.08154 (C*-Smale/Dubinin–Sugawa), both Krishna's own preprints, neither addresses the Schoenberg-type conjectures. Exa reports "4 citations"; the additional two are Krishna 2208.0140v1 (inspected: cites 2206.06653 only in a remark listing formulated conjectures, no progress) and Krishna's 2026 Vestnik KRAUNC paper (inspected: C*-Gauss-Lucas/Sendov over commutative C*-algebras, cites BJKR in bibliography only, does not touch 2.1/2.3/2.4).
- Tang–Zhang, "Sharp Schoenberg type inequalities and the de Bruin–Sharma problem" (arXiv 2508.10341v2, 2025): scalar complex polynomials only; no C* content (checked body). arXiv 2504.09837 (Schoenberg type inequalities): scalar.
- Cheung–Ng 2006 and Kushel–Tyaglov 2016: scalar theorems; source itself credits them; they are not refuted and get no credit. BJKR 1984: different Schoenberg theorem (positive semigroups).
- Targeted refutation searches ("C*-algebraic Schoenberg counterexample", "non-normal matrix Loewner polynomial moment counterexample", "Schoenberg conjecture operator algebra refuted", 2023–2026 recency): nothing.

**No old public counterexample and no directly subsuming negative theorem was found.** The ingredients (nonnormal involutions; failure of naive scalar→Loewner extension) are classical and the candidate claims no new general theory.

**Limits (candor):** citing-corpus review used Semantic Scholar API + web search engines (Exa-mediated), not a full MathSciNet/zbMATH/Google Scholar sweep (no institutional access attempted); the HKU-hub author PDF was Cloudflare-blocked and I substituted the author's departmental copy; MathDB "open" status and low citation count are NOT priority guarantees; a counterexample could exist in an unindexed/unpublished source. No absolute priority claim is made or supported.

## Gate 5 — MANUSCRIPT: PASS

- Rendered BOTH pages of the frozen `paper.pdf` (SHA256 `575dc943…`, matches frozen hash; also matches git blob at 1b388f77e5) at 150 dpi (`render/mp-1.png`, `render/mp-2.png`) and inspected all math.
- Every displayed item independently recomputed: P′ expansion with correct deletion order; S=6H, T=18H², C=6I₂, E=18I₂; right sides 2H, 2H², 16I₂−14H² (and J-versions); all quadratic forms −8/−8/−8/−8/−392/−392; (H²)₁₁=(J²)₂₂=29. All correct.
- The specializations (1)–(3) of Conjectures 2.1/2.3/2.4 at d=3, Σa=0 are faithful to the source statements I read; the note that the source's mixed n/d indexing is immaterial is correct.
- Attribution and honesty: Krishna's conjectures credited ([1], with conjecture numbers); Cheung–Ng [2] and Kushel–Tyaglov [3] correctly described as scalar predecessors; explicit "No new theorem about nonnormal involutions is being asserted", "No absolute priority claim", "one outcome". Two-page layout, no orphan references, bibliography accurate. `build/paper-build.json`: exit 0, issues []. The prior 3-page orphan-reference layout is superseded; the frozen 2-page version is clean.

## Frozen hashes verified (working tree AND git blob 1b388f77e5)

| file | SHA256 | git 1b388f77e5 |
|---|---|---|
| formal/PolynomialWitness.lean | 452991763aba35a47af47e0f7b78efd0b478a96c47c42611f6c2f19f4e21e194 | match |
| formal/FourthMoment.lean | 2d90919de7a947b43c7b3c8c13973cc1d01f330a8a2dfa8a934153c93b7f0e3a | match |
| main.tex | 0c48b60fa8d61492813ddbe169f645808830d572adbeedc0cbe41825eea9d8c9 | match |
| paper.pdf | 575dc94346a6be849b1247d3756236b10694950e17fa19d6c39e5204810022d6 | match |
| build/verified/audit.json | 7f47050421d699672e1bfadaa004e5b8be99fbee6b9ac3030c53cdeaa41a7909 | match (working tree; artifact regenerated byte-identically by my replay) |

`audit.json` is a replay artifact not stored in the commit itself; its frozen hash refers to the parent's replay receipt, and my own independent replay reproduced it byte-for-byte.

## Replay receipt (mine)

- Command: `python3 verification/verify_candidate.py replay/copiedCandidate --lean-bin …/lean-4.34.1-linux/bin/lean --packages …/2026-10-14/formal/.lake/packages` (run inside my lane).
- Result: PASS; 36 declarations (23+13); axioms {Classical.choice, Quot.sound, propext}; warnings-as-errors; receipt `replay/copiedCandidate/build/verified/audit.json` SHA256 `7f470504…` (identical to frozen).

## Decisive objections

None.

## Non-decisive observations (for the parent, no candidate edit required or made)

1. Krishna's scalar Conjecture 1.2 / C* Conjecture 2.3 coefficient (2/d²) appears inconsistent with the classical display in Cheung–Ng; harmless here because the witness refutes both readings (verified exactly). Worth one sentence in any future exposition.
2. `critical := ![1, −1]` are C-casts to M₂: central, self-adjoint, distinct — stronger than the hypothesis requires; no issue.
3. An initial free-algebra word-level check I attempted is over-strong (fails only because I is non-central in the free algebra); documented to prevent future reviewers repeating it; the generic-polynomial check is the correct universal verification.
4. My novelty search could not exhaust MathSciNet/zbMATH; recorded as a standing limit, not an objection.

## Eligibility

One combined outcome; source (v1, only version), mathematics (independently re-derived via two new codepaths), formalization (fresh byte-identical strict replay, all 36 types/axioms read), bounded novelty (no prior refutation or subsuming theorem found; limits recorded), and manuscript (both pages verified) all pass. **Eligible under the strict 10→11 standard.** I did not count or edit acceptance.
