# Independent adversarial five-gate review — parent-matrix-screen-r7 @ 1ea6b3103b

Reviewer: pi-squared-polya-final-review (solo, no children). Date: 2026-10-27.
Scope: own lane only. No parent/shared edits, no git actions, no tally/acceptance changes, no external contacts.

Candidate: closed finite-dimensional refutation of the FIRST squared Pólya–Szegő clause of
Moslehian–Fu arXiv:1501.02939v1 Conjecture 2.16 (p.9) / MathDB 329636, via positive 4×4
inputs U=diag(A,B), V=diag(B,I) (spectra in [1,1024]), an honest full-algebra unital positive
complex-linear (in fact completely positive) map M₄(C)→M₂(C) given by averaging diagonal
blocks, genuine CFC geometric means, and the exact negative quadratic form of
α²C²−D² at v=(1,2), α=1025/64. Discovery credit 0. Tally 25/30 unchanged.

All 70 hashes in full100-review-hashes.json verified against my own copy of the frozen lane:
**70/70 OK** (no missing, no mismatch). Working tree clean inside the lane at 1ea6b3103b.

---

## Gate 1 — Source: PASS (with documented residual access hole)

1. I rendered arXiv:1501.02939v1 p.9 myself from the lane's own PDF copy
   (evidence/page9-09.png, evidence/conjecture-crop.png) and **visually read** the statement.
   Confirmed verbatim: "Conjecture 2.16. Let Φ be a unital positive linear map. If 0 < m₁² ≤ A ≤ M₁²
   and 0 < m₂² ≤ B ≤ M₂² for some positive real numbers m₁ ≤ M₁ and m₂ ≤ M₂ ...";
   first display is (Φ(A)♯Φ(B))² ≤ **¼(√(M₁M₂/(m₁m₂)) + √(m₁m₂/(M₁M₂)))² Φ(A♯B)²** —
   the ¼ is **outside** the squared parentheses, exactly as the candidate assumes
   (coefficient = ((√(M₁M₂/m₁m₂)+√(m₁m₂/M₁M₂))/2)² = α²; at m₁=m₂=1, M₁=M₂=32: (1025/64)²).
   MathDB 329636 statement matches the arXiv display digit for digit (sources/329636-live.json,
   hash-verified); MathDB post_type=conjecture, status=open, all activity arrays empty.
2. arXiv abs page re-fetched: **v1 only** (submitted 2015-01-13), journal ref LAA 491 (2016) 73–82.
   Crossref record re-fetched: DOI 10.1016/j.laa.2015.01.041, PII S0024379515001160, 14 references.
   No Crossref/OpenAlex sign of an erratum or corrigendum; MathDB shows no resolution.
3. Hypothesis audit: the conjecture requires only "unital positive linear map" and the four
   spectral bounds. The witness satisfies all of them with **strictly positive definite** inputs
   and a map that is unital, complex-linear, *-preserving and completely positive — no reading
   of "positive linear map" (real-linear positive, complex-linear, *-preserving, CP) is violated.
   No hidden hypothesis (no dimension restriction, no 2-positivity, no normality) is present in
   the source statement. A finite-dimensional instance logically refutes the unrestricted
   universal operator assertion (finite-dimensional Hilbert spaces are instances of it).
4. Consistency with the source's own proven results: the abstract's **proven** first inequality
   has constant ((M₁M₂+m₁m₂)/(2√(M₁M₂m₁m₂)))⁴ = α⁴ ≈ 65792 for this input, while Conjecture 2.16
   proposes the sharpened α² ≈ 256.5. The refutation targets only the conjectured sharpening and
   is fully consistent with the paper's theorems (witness ratio ≈ 275.7 ≪ α⁴).
5. **Published body remains unread (residual risk).** Unpaywall confirms bronze OA at the
   publisher (pdf URL https://www.sciencedirect.com/science/article/pii/S0024379515001160/pdf);
   my direct attempt returned 403 (bot challenge, 1.2 MB HTML challenge page); Elsevier full-text
   API returned metadata-only/401/429 in the parent's saved files (re-examined: no body).
   Author's old site moslehian.ir is now a domain-parking page. No legitimate public copy found.
   Residual risk: the published LAA version could in principle have modified or withdrawn the
   conjecture; nothing accessible suggests it (v1 says "to appear in LAA", 10 pages, and the
   citation graph shows no correction), but it is not closed. This bounds eligibility; it does
   not affect mathematical correctness (MathDB records the arXiv statement).

**Gate verdict: PASS** on the source statement and hypothesis match, with the published-body
comparison explicitly open and carried into the eligibility decision.

## Gate 2 — Mathematics: PASS (independent rederivation, not a rerun)

I wrote my own checker (checks/own_exact_check.py; run log checks/own_exact_check.run.txt)
using a different methodology from the parent's (exact Fractions + independent 60-digit
eigendecomposition cross-checks + sympy radicals). 29/29 checks pass:

1. A=I+1023P, B=I+1023Q with P,Q orthogonal projections ⇒ A,B have spectra exactly {1,1024}
   (Cayley–Hamilton verified exactly); U=diag(A,B), V=diag(B,I) satisfy 1≤U,V≤1024·I exactly.
2. Riccati: (A+B)A⁻¹(A+B)=(1054721/2048)B exactly; det A=det B=1024; **A♯B=(A+B)/s** confirmed
   TWICE — by Riccati uniqueness and by an independent symmetric eigendecomposition of
   A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2} (agreement < 1e-40). Likewise B♯I=diag(32,1) and
   **F♯G=(G+dF)/√(r+2d)** (d²=4100/1054721=det G/det F, r=tr(F⁻¹G)=1058821/1054721) by both routes.
3. Quadratic form: my own Fraction-interval arithmetic (independent implementation, tighter
   1e-14 rational sqrt bounds) gives vᵀ(α²C²−D²)v ∈ (−17254.6313894163, −17254.6313893871);
   true value at 60 dps: **−17254.631389407252…** — strictly below −17000 with margin ≈254.6.
   No scaling glitch: this is the literal quadratic form of α²Φ(U♯V)²−(Φ(U)♯Φ(V))² at v=(1,2)
   on the actual 2×2 matrices; entries of F² are O(10⁵) and the defect is O(−10⁴), consistent.
4. The exact coarse rational bound **−1763270875137191128175507/102858162597360173056**
   (= −17142.7413…) is reproduced bit-for-bit from the manuscript's displayed bounds
   a≤441/10000, 623/10000≤b≤624/10000 (squared checks verified), and the monotone
   numerator/denominator direction of the estimation is correct.
5. All intermediate quadratic-form values in the displays verified exactly:
   qF²=1058845/8, qFT+qTF=17463 (⇒ a·17463/2), qT²/4=257, qG²=1050641/4, qGF+qFG=1056799/4,
   and the identities GF⁻¹G=rG−(4100/K)F and TB⁻¹T=I.
6. Parent's check_exact_witnesses.py rerun from my copied bytes: exit 0 and its output
   exact-witnesses.json is **byte-identical** to the frozen copy (sha ad1a4290…).
7. Prior-example corrections independently reproduced: Hoa–Binh–Ho (Sci. Math. Jpn.) Remark 1
   matrices X=[[5/6,2],[2,5]], Y=[[1,3],[3,10]] DO lie in [1/50,11] and the difference
   K(X♯Y)²−(X∇Y)² is positive definite (leading minor 910803√6/8000+95141243/198000>0,
   determinant 88033691903/87120000+10018833√6/12800>0) — the printed −4.1122 is wrong;
   the arXiv 1610.04162 p.5 example has min eigenvalue 0.00782 < stated m=1, violating its
   own bound. Neither is a valid prior refutation, matching the parent's correction.
8. Supplementary rational Diaz–Metcalf witness (t=16): v₂ᵀ[(257/32)²C₂²−M₂²]v₂ = −2449502775/8192
   reproduced exactly (uncredited supplementary material; not counted).

**Gate verdict: PASS.**

## Gate 3 — Formal: PASS (fresh strict replay from own copied bytes)

1. Copied the 9 module sources + candidate.json + verify_candidate.py/pins.json into my lane
   (replay/), verified every copied byte against full100-review-hashes.json, then ran the
   pinned verifier with --packages /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages.
2. Result: **PASS, 100 declarations, axioms exactly {propext, Classical.choice, Quot.sound}**,
   Lean 4.34.1 binary at dlp-research/.tools/lean-4.34.1-linux/bin/lean, mathlib d13f23b… and
   all 8 dependencies hash- and cleanliness-checked by the script. All 9 module compile logs are
   0 bytes (warningAsError=true) — replay/replay-log-hashes.txt.
3. I read the actual Checks.log produced by my replay (not the receipt): all 100 #check types and
   #print axioms are present and standard. Key endpoints:
   - `SquaredPolya.SourceClaim329636First : Prop` — the literal finite-dimensional universal
     first-clause assertion (unital Φ, PSD-preservation, four scalar-bound hypotheses,
     conclusion `sourceCoefficient m₁ M₁ m₂ M₂ • Φ(A♯B)² − (Φ(A)♯Φ(B))² PosSemidef`).
   - `SquaredPolya.source_counterexample_329636_first : ¬SourceClaim329636First` — **closed,
     no premises**; it is the negation of the literal assertion, not merely a scalar sign.
   - `literal_matrix_failure`, `matrix_defect_not_posSemidef`, `scalarDefect_lt` all typed as
     claimed; `geometricMean` is the genuine CFC square-root definition and
     `geometricMean_eq_of_riccati` bridges via uniqueness of the positive square root.
   - `blockAverage` is `→ₗ[ℂ]`, unital (`blockAverage 1 = 1`) and positive on the full M₄(C) —
     the "full algebra, not block subalgebra" claim is proved, not asserted.
4. No `sorry/admit/axiom/unsafe/native_decide` (script-enforced), no nonstandard axioms, no
   type-level escape hatch. The formalization does NOT claim the second clause, CP-strength, or
   an optimal constant — matching the candidate's scope statement.

**Gate verdict: PASS.**

## Gate 4 — Novelty / substantive: HOLD (genuinely open; no public refutation found, but
### access holes remain; one new closest-primary source analyzed)

What I checked:
- **MathDB 329636**: open, no solutions/comments (hash-verified snapshot). Other MathDB records
  in the lane (324727, 329181, 336251) are unrelated problems; 324727 (Wielandt) is public,
  excluded, and mechanism-only.
- **Registry clone** pi-euler-turan-final-review/fresh/trureturing at exactly
  f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada (read-only; no mutations): no title/ID/source match
  for this target (the only "Polya" hit is an unrelated quantum NormCompression item). A scan,
  not a certificate.
- **The six OpenAlex citers (complete graph, W2030228287, cited_by=6)**:
  - JMAA 2018 Gumus–Moradi–Sababheh "More accurate operator means inequalities" — **body UNREAD**
    (ScienceDirect 403; no arXiv version exists — checked arXiv API by title and by
    au:Gumus+au:Moradi; Unpaywall shows bronze OA at publisher only; Semantic Scholar 429).
    This remains the single largest known hole.
  - arXiv 1610.04162 (= Expo. Math. extension, W2529323322): body read. Contains no mention of
    Conjecture 2.16; its p.5 claimed counterexample violates its own stated m=1 bound
    (independently verified). Not a refutation.
  - Filomat 2019 (W3006829787): body saved; its results are weaker power bounds and its
    Remark 2.12 only recovers MF Theorem 2.14 (second clause, proven direction). No conjecture
    resolution.
  - ScienceAsia 2017 (W2769198309, Fu–Yang): body read; refinements of |Ψₚ(A)|≤½μᵖ-type
    inequalities; cites MF only in the reference list. No resolution.
  - arXiv 1801.08634 (Furuchi–Moradi–Sabbagh… actually Furuichi–Moradi–Sababheh, sharp2018):
    body read; concerns Φ(A∇B)ᵖ bounds — a different inequality shape; does not touch
    (Φ(A)♯Φ(B))² vs Φ(A♯B)². No resolution.
  - JIA 2020 (W3032443886, Karim–Ali–Mushtaq): abstract retrieved ("reverse AM-GM improving
    Xue"); body bot-walled at Springer (challenge page saved/removed); topic orthogonal.
  - arXiv 1612.02361 (Zagreb indices): irrelevant graph-theory citation.
- **NEW closest-primary source found by this review (not among the 6 citers — it does not cite
  MF): Yang–Fu, "Squaring operator α-geometric mean inequality", J. Math. Inequal. 10 (2016)
  571–575, doi:10.7153/jmi-10-45** — by the conjecture's own co-author. Open PDF fetched and
  read (evidence/jmi-10-45-yang-fu.pdf, sha 091627b6…). Its Theorem 2.3 proves the SAME-SHAPE
  inequality (Φ(A)♯_αΦ(B))² ≤ β·Φ²(A♯_αB) with a case-dependent constant β. At α=1/2 its core
  factor (G+g)²/(4Gg) equals **exactly the conjectured constant (1025/64)²** for m₁=m₂=1,
  M₁=M₂=32, multiplied by K⁻¹ slack; on my witness parameters β ≈ 748 (case g≤t₀) / 1965.7
  (paper's own case selection), while the witness ratio is 275.699 — so Yang–Fu's valid bound
  holds and the conjectured 256.5 fails. Conclusion: Yang–Fu 2016 neither subsumes the
  conjecture nor contains a counterexample; the conjecture is precisely the "remove the
  Kantorovich slack" refinement, and refuting it is not a known corollary of that paper.
  This find STRENGTHENS confidence that no trivial subsumption exists and independently
  corroborates the witness numbers (checks/yang_fu_comparison.txt).
- **Ando 2016, "Square inequality and strong order relation"** (Adv. Oper. Theory 1, cited by
  ScienceAsia): abstract checked via OpenAlex (general strong-order criterion for squaring;
  no positive-linear-map squared Pólya–Szegő statement). Body not retrieved (bot-walls);
  low subsumption risk, noted.
- Web searches for any published resolution/counterexample of Conjecture 2.16: nothing found
  (search infrastructure partially rate-limited; documented).

Substantive assessment: the refutation decides, negatively, a specific constant question posed
as an open conjecture by established operator theorists and recorded in MathDB. It is not a
known corollary: the closest published valid constants are strictly weaker (source's own α⁴ ≈
65792; Yang–Fu β ≈ 748–1966 for this input), and the witness shows the conjectured constant
fails with a small but exact margin (ratio 275.699 vs 256.500, factor ≈ 1.0749). The
construction is honest (CP unital map, positive definite inputs, genuine geometric means) and
the mechanism is exhibited by a non-isolated one-parameter family (t=32 instance formalized).

**Gate verdict: HOLD** — no evidence of prior refutation or subsumption anywhere accessible,
but eligibility must remain bounded until (a) the published LAA body is read (confirms the
conjecture survives publication unchanged) and (b) the JMAA 2018 body is read (the one citer
of the right topic whose body is unknown). Neither can invalidate the mathematics; either
could invalidate novelty/eligibility. No novelty PASS is warranted on current access.

## Gate 5 — Manuscript: PASS

1. Both pages of paper.pdf rendered and read by me (evidence/paper-1.png, paper-2.png);
   paper.pdf sha b768fa39… and main.tex sha 245fcd42… match the 70-hash file; paper.pdf is
   byte-identical to build/main.pdf; build log clean (no warnings/errors).
2. Every display recomputed exactly (checks/manuscript_display_checks.txt): the conjecture
   transcription (1) is verbatim-correct including ¼ outside the square; F,G,T matrices; K, a,
   b, r, ρ; both Riccati identities; A♯B=a(A+B), B♯I=T, (G+bF)F⁻¹(G+bF)=ρG; displays (4) and
   (5) term-by-term; the square-root bounds by squaring; display (6) coarse bound reproduced
   bit-for-bit; the Hoa determinant display matches my sympy computation; the endomorphism-
   convention remark (diag(Φ,Φ), test vector (v,0)) is mathematically correct.
3. Scope hygiene: credit 0, "independent review pending", no priority claim, second clause and
   optimal constants explicitly not claimed, access limits stated in the paper itself. The
   bibliography cites MF (LAA 491 (2016) 73–82 + arXiv v1), Hoa–Binh–Ho (Sci. Math. Jpn. 80
   (2017) 139–151), and 1610.04162v1. Minor non-blocking nit: [3] cites the arXiv version
   though a published Expo. Math. version exists; the draft's own qualification section covers
   the unread-body status honestly.

**Gate verdict: PASS.**

---

## Overall bounded eligibility decision

- The mathematics and the formal certificate are correct and independently reproduced; the
  source target is verified against the actual arXiv PDF visually; the manuscript is accurate.
- **Eligibility: CONDITIONAL — first clause only, HOLD pending two named body readings:**
  1. Published LAA 491(2016) 73–82 body (PII S0024379515001160, bronze OA but bot-blocked):
     must confirm the conjecture (or at least its first clause) is present/unchanged, and no
     published correction exists.
  2. JMAA 465 (2018) 267–280 body: must confirm it neither contains nor implies a refutation
     of the first clause.
  If both clear, the novelty gate can be revisited toward PASS by a future reviewer; the
  Yang–Fu 2016 paper I found must be added to the closest-prior-art list (it does not block).
- Not eligible: second (Diaz–Metcalf) clause; any CP-vs-positive strengthening; any optimal
  constant or mechanism credit; the Hoa/1610.04162 printed-value corrections (reported, not
  counted); the supplementary t=16 witness (uncredited by design).
- Decisive objections found: none that survive. Strongest counterarguments considered and
  rejected: (i) "counterexample is just an unsquared failure" — no, the squared statement is
  refuted directly and the unsquared-type valid bounds all hold; (ii) "subsumed by Yang–Fu
  2016" — no, their constant is strictly weaker and contains the conjectured constant as a
  factor with K-slack > 1; (iii) "map not honest" — the map is unital, complex-linear,
  *-preserving, completely positive on the full M₄(C); (iv) "finite-dimensional insufficiency"
  — logically airtight; (v) "prior examples already refute the second clause" — both checked
  examples are invalid at their stated bounds, and the second clause is not claimed anyway.

No acceptance, packet, tally, or credit change is made or proposed by this review. Tally 25/30
and candidate credit 0 remain unchanged.
