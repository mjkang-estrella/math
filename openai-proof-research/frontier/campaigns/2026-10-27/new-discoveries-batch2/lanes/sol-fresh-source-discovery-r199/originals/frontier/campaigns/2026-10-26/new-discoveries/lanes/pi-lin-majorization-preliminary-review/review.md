# Preliminary adversarial review — prospective NEW MathDB 332939 / Lin arXiv:1604.04141 Conjecture 4.3 eigenvalue majorization refutation

Reviewer: pi review sub-agent. Solo, standard speed, no children, no git/shared edits. All writes in
`lanes/pi-lin-majorization-preliminary-review/`. Review date: 2026-10-27 (UTC).

## VERDICT (one line)

**The mathematics is exactly correct and I reproduce it in full; the source fidelity is verified; but the
NOVELTY GATE FAILS — Lin's Conjecture 4.3 was already publicly refuted with a kernel-checked Lean proof
committed 2026-10-22 (experiments 2026-10-18) in `the-omega-institute/trureturing`, which I have
independently exact-verified. Recommend: no Lean investment, no formal packet, Count 0; MathDB 332939
is already resolved (refuted).**

---

## 1. Source review (SOURCE)

Verified **visually** from `sources/1604.04141.pdf` (arXiv v1, the only version; saved history page confirms
no v2). Pages 1, 2, 5, 6 rendered to PNG and read as images.

- **The claim (p.6, read visually):** "Conjecture 4.3. Let A and B be n × n positive semidefinite matrices.
  Then λ(A² + |BA|^p) ≻ λ(A² + |AB|^p) for all p > 0."
- **Absolute value convention (p.1, read visually):** |X| = (X* X)^{1/2}, the unique PSD square root of X* X.
  So |BA| = (A B² A)^{1/2} and |AB| = (B A² B)^{1/2}. The parent's identification of the absolute roots is the
  literal source reading; **orientation confirmed** (the conjectured-majorizing side is the **|BA|** side).
- **Semidefinite allowed:** the quantifier is "positive semidefinite matrices" (p.6, visual). A SPD ⊂ PSD and
  B PSD rank 2 are inside the quantifier. **Confirmed; the rank-2 singular B is legitimate.** (The prior-art
  witness uses even B positive definite, so nothing hinges on singularity.)
- **Orientation coherence check:** p.2 defines majorization with descending eigenvalues and prefix sums, and
  (P1): λ(X) ≻ λ(Y) ⟹ det X ≤ det Y. Hence Conjecture 4.3 would imply det(A²+|BA|^p) ≤ det(A²+|AB|^p),
  exactly the open question printed above it (det(A²+|AB|^p) ≥ det(A²+|BA|^p), p.6 visual). The source is
  internally coherent; the parent refutes the k=2 prefix condition, which kills both ≻ and ≻_w.
- **Published version:** Commun. Contemp. Math. 19 (2017) 1650044, DOI 10.1142/S0219199716500449 —
  **paywalled, HTTP 406 on fetch; body not read.** Conjecture numbering in the published version is
  corroborated by two independent secondary quotes (trureturing mdbook; oam-16-60's quote of the
  determinantal question). arXiv v1 is MathDB's own cited source, so the review basis is the pinned one.
- **Source internal error found (new observation, does not affect the parent):** p.5 asserts "in
  [8, Corollary 2.3] the authors observed that for any positive integer k, it holds λ(A²+|BA|^{2k}) ≻
  λ(A²+|AB|^{2k})". I fetched Lin–Wolkowicz (Waterloo CORR report, final LAMA version):
  **Corollary 2.3 actually reads** "λ(A² + (AB)^k(BA)^k) ≻ λ(A² + (BA)^k(AB)^k)" for Hermitian A,B. For k ≥ 2,
  (AB)^k(BA)^k ≠ (AB²A)^k = |BA|^{2k}. So the source **misquotes** [8]; the printed |BA|^{2k} sentence is
  false as stated (exactly the p=4 phenomenon below), while the cited corollary is true and only covers
  p = 2 among our cases. Any paper written from this source must not propagate that sentence. The
  determinant corollary (4.2) itself survives — it was later proved for all p > 0 by
  Ghabries–Abbas–Mourad (LAA 596 (2020) 169–183), as quoted in oam-16-60 §1.

**SOURCE verdict: PASS.** Claim, hypotheses, orientation, and modulus convention all match the parent's
reading. No eligibility loophole (no PD-only, no Hermitian-only, no fixed-p restriction).

## 2. Mathematics review (MATH) — independent exact rederivation

I rewrote the checker from scratch (`review_checker.py`, `fractions.Fraction` only, no reuse of parent
code; mpmath 90-dps eigenvalues built from exact rationals). **27/27 checks PASS**
(`review_checker_output.json`):

- Q orthogonal (QQᵀ = QᵀQ = I, exact); Q is the Cayley transform of the parent's recorded K.
- A symmetric SPD: leading minors 3/10, 1791/78400, 78726589/4348848000, all > 0 (Sylvester).
- B symmetric PSD rank 2: 2×2 block det 2022720/83779 > 0, third diagonal 0.
- AB = QD and BA = DQᵀ **exactly** (all 9 entries).
- Absolute roots **from the definition**: (QDQᵀ)² = AB²A with QDQᵀ ⪰ 0 ⟹ |BA| = QDQᵀ and |BA|³ = QD³Qᵀ;
  D² = BA²B with D ⪰ 0 ⟹ |AB| = D and |AB|³ = D³. (QDQᵀ)³ computed directly as a cube, matches.
- L = A²+|BA|³ and R = A²+|AB|³ recomputed from A and match the parent's stored L, R entry-for-entry.
- τ = 197/500: L − τI has leading minors 164962021007737/231238250510400,
  16944916580133891169/453226971000384000000, 78544752135078542548579/235692188263043442000000000,
  all > 0 ⟹ SPD ⟹ λ₃(L) > τ. (Parent certificate values match mine.)
- v = (−19/100, −1, 37/50): vᵀ(R − τI)v = **−137006877457/21744240000000** < 0 (exact) ⟹ λ₃(R) < τ.
- tr L = tr R = 9705109861/3261636000 (exact equality).
- Hence λ₃(L) > τ > λ₃(R); equal totals force Σ_{i≤2}λ↓ᵢ(L) < Σ_{i≤2}λ↓ᵢ(R). 90-dps spectra:
  λ(L) = (2.1427147592138889…, 0.4340627963140154…, 0.3987567655919263…),
  λ(R) = (1.7877739082792623…, 0.7977442335992058…, 0.3900161792413625…);
  top-2 difference −0.008740586350563961, matching the parent's `gap_float` exactly. k=1 prefix holds
  (2.1427 > 1.7878), so the refutation is exactly at k=2 — a genuine, tight counterexample.

**MATH verdict: PASS.** The witness is an exact rational refutation of Conjecture 4.3 at p = 3, n = 3,
A SPD, B PSD rank 2. I find no error. The mechanism (threshold sandwich + equal traces) is Lean-friendly
and the parent's plan would formalize cleanly. **But see §3.**

## 3. Novelty review (NOVELTY) — **FAILS: already publicly refuted**

### 3.1 Decisive prior art (found by this review; the parent task did not list it)

`the-omega-institute/trureturing` — "A library for discovering truth: questions, computation, reusable
proofs, and an open frontier" — contains a **complete, kernel-checked Lean refutation of the identical
conjecture**, file `D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.lean`:

- **Timeline (UTC):** experiments commit with pinned exact checker `check.py`
  (SHA-256 5d3d2268…e5890a, which I refetched and **hash-matched**) committed **2026-10-18 03:37**;
  issue #18700 preregistration **2026-10-18 04:09**; Lean file committed **2026-10-22 20:35**
  (commit 9ea8cc201975); merged to main **2026-10-27 08:49**. Parent lane files: 2026-10-27 ~01:45–01:56.
  **The refutation predates the parent witness by 5–9 days.**
- **Witness:** A = diag(3, 1, 1/2), B = [[1/2, 1/4, 3/4], [1/4, 3/4, 0], [3/4, 0, 5/2]] (positive definite),
  **p = 4**, τ = 7/5, v = (0, −1, 19/64). Same mechanism as the parent: L − (7/5)I ⪰ 0 via exact rational
  ULᵀDU factorization, negative quadratic form for R − (7/5)I, equal traces, two-entry prefix violation.
- **Verification status:** stated axiom closure {propext, Classical.choice, Quot.sound}; the Lean file I
  downloaded at the immutable commit contains complete certificate data and the final `theorem result :
  ¬ claim`. I **independently exact-verified every ingredient** (`prior_art_check.py`,
  `prior_art_witness_check.json`): B PD; all 7 principal minors of L−(7/5)I ≥ 0 **and** their published
  ULᵀDU product reproduces L−(7/5)I entry-exactly; vᵀ(R−(7/5)I)v = −95831/20971520 < 0; traces equal
  410065/4096; 90-dps spectra λ(L) = (97.0048814674967962…, 1.7023284034977602…, 1.4063155196304436…),
  λ(R) = (92.0269284935598257…, 6.6916368647913731…, 1.3949600322738013…); prefix-2 violation
  −0.0113554873566423. **The prior art is mathematically sound.**
- **Ledger precedent:** this campaign already excluded a candidate (MathDB 332318, lane parent-matrix-
  screen-r4) because "Sra posted 8 October 2026 linconj-v1 Theorem 1.1 exact resolution; immutable GitHub
  PDF refetched and actual statement read." Public GitHub posts by researchers count as excluding prior
  art under the campaign's own standard. The same standard applies here, with the additional strength of a
  machine-checked proof, a pinned verifier, and a dated preregistration issue.

### 3.2 Consequence for this candidate

Conjecture 4.3 is a single universal statement. One valid counterexample — the prior art's p = 4 one —
settles it. The parent's p = 3 witness is a second, independent, also-valid counterexample of the same
phenomenon (trureturing's floating-point scan reports their witness violates for 3 ≤ p ≤ 33/4 and holds at
p = 2, so p = 3 is inside the known violating range for their witness too). A second counterexample to an
already-refuted universal claim is not a new-to-literature theorem and does not resolve MathDB 332939
first. **Novelty: FAIL. Eligibility: FAIL (no formal PASS, no credit). Count stays 0 — unchanged.**

### 3.3 What the literature actually established (cross-checked against local full texts)

- **Determinantal conjecture 4.2 and the all-p det question are already proved:** mia-23-14 (Abbas–
  Ghabries, MIA 23 (2020) 169–) proves det versions and states the A singular case gives the det
  conjecture; oam-16-60 §1 states verbatim that Ghabries–Abbas–Mourad [11 = W3012424503, LAA 596 (2020)
  169–183] **proved det(A²+|AB|^α) ≥ det(A²+|BA|^α) for all α > 0** (their body was not fetched —
  Anubis/Elsevier blocks — but two independent secondary quotes agree). So the **only** open residue was
  the majorization — which is now refuted. Consistent with the parent's framing; the refutation does not
  contradict any proved det inequality (our witness has det L < det R, as required).
- **2105.13356 (W3172560439, Ghabries–Abbas–Mourad–Assi, LMA 2022):** read locally; it disproves the
  **Lemos–Soares Conjecture 1.2** (singular-value log-majorization for products of weighted geometric
  means) — a different conjecture. Not prior art for the additive Lin majorization. Task's premise confirmed.
- **"GPT, the Counterexample Machine" (arXiv 2608.29595) and suvrit/count-ex-machina:** full local text
  has **zero** matches for Lin/1604.04141/diffusion/majorization-of-|BA| (only hit is an unrelated
  McSwiggen–Sahi reference). The live repo registry at immutable commit dbf673741a54c7dc9d88a6aec0e8148a
  538f4a3a (fetched, hashed) has **0** hits for Lin / 1604.04141 / majoriz. All 17 listed cases are other
  problems. **No conflict and no help.**
- **15 OpenAlex citers:** 6 full bodies inspected locally (mia-23-14, oam-15-07, oam-16-60, W2594589766,
  W3172560439, W4389884742) — all cite Lin only for the det results or the ♮ operation; none states or
  resolves the λ(A²+|BA|^p) ≻ λ(A²+|AB|^p) majorization. Remaining 9 (W2996326898, W3045600120,
  W2791284414, W3012424503, W3042904500, W2549198460, W4414338466, W7125900077, W7168164875) screened
  at title/abstract level only — all det/mean/operator topics. **No earlier refutation or proof of the
  majorization found in any citing body**; the trureturing settlement (2026-10-18/22) is the earliest
  refutation located.
- **Ghabries 2022 thesis (Remark 2.5, p.50):** body inaccessible — HAL `tel-03936351` is behind an Anubis
  bot-proof-of-work page (confirmed twice; the root `ghabries-thesis.pdf` is that bot HTML), and the
  ResearchGate author upload returns HTTP 403. The 2022 thesis predates everything here and can only
  corroborate that the majorization was open in 2022; **it cannot restore novelty** after the 2026-10-18
  public refutation. Non-blocking for the verdict, but flagged as an unread item.

## 4. Recommendations to the parent

1. **Do not invest in Lean** for the p = 3 witness and do not open a formal packet for MathDB 332939.
2. Record MathDB 332939 as **already resolved (refuted)**, citing
   `github.com/the-omega-institute/trureturing` commit `ac2cac036236684b9ff33cc22a3e219c8e4a33c0`
   (Lean file committed 2026-10-22; experiments 2026-10-18; issue #18700), independently exact-verified
   by this review.
3. If the parent wants salvageable value from this lane: the **source misquote of Lin–Wolkowicz
   Corollary 2.3** (§1) is a small, documented observation; and the parent's exact p = 3 witness is sound
   but redundant. Neither carries discovery credit.
4. No changes to shared indexes, ledger, or NEXT.md were made by this review (per rules); the parent
   integrates.

## 5. Residual risks (bounded)

- The published CCM version body and the Ghabries thesis body were never read (paywall/bot blocks). Both
  are pre-2026-10-18 and cannot reinstate novelty; they could only add *earlier* refutations, which would
  strengthen, not weaken, the rejection.
- Nine citing bodies were screened at title/abstract level only. Same direction of risk: an earlier
  refutation there would only add prior art; nothing can make the parent's witness invalid or first.
- The trureturing project's ownership/operator is unknown to me; it is public, dated, immutable-committed,
  and hash-verifiable regardless. If it were the same operator's parallel effort, that is a parent-level
  policy question — mathematically and publicly the refutation exists.

## 6. Artifact index (this lane)

- `review_checker.py`, `review_checker_output.json` — independent from-scratch exact verification of the
  parent witness (27/27 PASS).
- `prior_art_check.py`, `prior_art_witness_check.json` — independent exact verification of the prior-art
  p = 4 witness (all ingredients PASS).
- `trureturing-LinDTIMajorizationRefutation.lean` — prior-art Lean source fetched at immutable commit.
- `prior_art_trureturing_check.py` — prior-art pinned checker (SHA matches their pinned hash).
- `lin-wolkowicz-2012-cor23-extract.txt`, `lin-wolkowicz-cor23-verbatim.txt` — actual Corollary 2.3 text.
- `cm-registry.json` — count-ex-machina registry at pinned commit (0 Lin hits).
- `provenance.json` — URLs, hashes, dates, access limits.
