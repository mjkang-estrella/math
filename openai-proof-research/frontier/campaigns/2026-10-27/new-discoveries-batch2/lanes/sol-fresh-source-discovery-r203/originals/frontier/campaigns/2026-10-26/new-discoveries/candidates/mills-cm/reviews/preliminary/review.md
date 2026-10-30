# Preliminary adversarial review — parent-mills-cm (frozen commit 475eaec)

Reviewer: pi review sub-agent (solo, no children, own lane only).
Scope: SOURCE / MATH / serious bounded NOVELTY / ELIGIBILITY of the frozen
23-file mathematical evidence for the Ferreira–Simon Conjecture 3 (arXiv:2108.09244v2,
p.31; MathDB 351688) n=0 refutation via `F(x) = −r(x)²/r′(x) = r(x)²/(1−x·r(x))`.

This is a **preliminary review**: it does NOT grant final formal, manuscript,
packet, or credit acceptance. Credit stays 0.

## Gate verdicts

| Gate | Verdict | Summary |
|---|---|---|
| SOURCE | **PASS** (with recorded material limit) | arXiv v2 confirmed latest; pp.29–31 independently rendered and read; exact normalization, domain, quantifier, and n=0 inclusion verified. Published Trans. AMS body remains inaccessible (soft block) — limit recorded, non-blocking at this stage. |
| MATH | **PASS** | Sign proof is exact and complete. Three independent structures (own recurrence derivation, exact power-series division, direct numerical differentiation of the literal erfc function) agree. Exact Bernstein certificate verified with independent code. Rigorous rational proof 3.141592 < π < 3.141593 reproduced from scratch (Machin + alternating series). Positive-input violation is genuine, not boundary-only. |
| FORMAL | **NOT CLAIMED / NOT PASS** | As instructed: the full source endpoint (finite identity + sign + continuity + positive-input contradiction in Lean) does not exist yet. Frozen support modules (Mills.lean 13 decls, DerivativeRecurrence.lean 6 decls) are consistent with the claims and were read line-by-line; the parent's .olean artifacts attest the support compile, but I could not independently recompile in this environment (no Lean toolchain available here). This gate is not assessed. |
| NOVELTY | **PASS (provisional, bounded)** — no exclusion evidence found | MathDB 351688 refetched fresh: open, progress null, every solution/attempt/comment array empty. All 3 OpenAlex citers' full bodies compared: zero overlap. Yang 2507.10954 §4.4, Xu–Yang 2026 full body, and Salazar 2606.31647 checked in full: different objects, no subsumption. No author follow-up resolves the conjecture. Targeted searches found no prior refutation. Limits recorded (no MathSciNet/zbMATH, S2 not retried by policy, publisher PDF blocked). Full formal novelty review still required before any acceptance. |

**Overall: PROCEED to parent's full formal completion.** No decisive (blocking)
finding. Non-blocking findings listed below.

## 1. SOURCE gate — what was independently verified

1. **Latest version.** arXiv abstract page fetched fresh: v1 2021-08-20, v2
   2022-05-19 ("Minor corrections. To appear in Transactions of the American
   Mathematical Society"). v2 is the latest.
2. **Rendered and read pp.29–31** (`sources-rendered/page-29.png`, `page-30.png`,
   `page-31.png`, produced by me from the frozen PDF; also compared against the
   parent's `mills-conjecture-31.png`):
   - §5.5 (p.29): r(x) = e^{x²/2}∫_x^∞ e^{−t²/2}dt — **exactly** the candidate's r;
     no √2 scaling anywhere in §5.5. r(0)² = π/2 follows (and is proved in the
     frozen Lean `mills_zero_sq`).
   - Proposition 10 (p.30): z ↦ −(r^{(n)}(√z))²/r^{(2n+1)}(√z) is CM for every n;
     LCM for n = 0, 1. **The √z argument is proved, and our refutation does not
     touch it** — different function (no square root in Conjecture 3).
   - Conjecture 3 (p.31): "For every integer n, the function z ↦ −(r^{(n)}(z))²/r^{(2n+1)}(z)
     is CM", explicitly a refinement of Proposition 10 (via CM-preservation under
     z ↦ f(√z)), "supported by simulations, but we could not find any proof."
   - **n = 0 is included**: "every integer n"; moreover the refinement claim only
     covers Prop 10's n = 0 case if n = 0 is in Conjecture 3. For n = 0 the
     conjectured function is −r(z)²/r′(z) = r²/(1−zr) on (0,∞) — precisely the
     candidate's F. The refutation targets genuinely positive inputs.
3. **Published version.** Crossref confirms DOI 10.1090/tran/8748 = Tran. AMS
   376(2), 855–890, online 2022-12-01; its abstract is word-identical to arXiv
   v2's. The PDF endpoints serve a cookie-consent HTML shell (soft block) —
   comparison of the published body is a material limit, recorded in
   `sources-published/published-version-attempt.md`. Same limit the parent
   recorded; not resolvable here.
4. **MathDB 351688** refetched fresh (`novelty/mathdb-351688-refetch.json`):
   status open, progress null, all solution/attempt/comment arrays empty —
   matches the parent's frozen record byte-for-byte in structure.

**SOURCE: PASS** (the published-body limit does not block a preliminary review;
it must be cleared before final manuscript acceptance).

## 2. MATH gate — independent verification (not the parent's script)

Checker: `checker/pi_review_independent_check.py` (exact Fraction/sympy
arithmetic throughout; result record `checker/independent-check-result.json`).

A. **Own recurrence derivation.** I re-derived everything from the ODE r′ = xr − 1
   via r^{(k)} = A_k(x)r(x) + B_k(x), A_{k+1} = A_k′ + xA_k, B_{k+1} = B_k′ − A_k,
   and verified the closed forms R_{2m} = (2m−1)!!·c, R_{2m+1} = −(2m)!! and the
   parent's stated recurrence R_{k+2} = (k+1)R_k. For F I used F − x·r·F = r² and
   Leibniz at 0: D_{n+1} = Σ C(n+1,k)R_kR_{n+1−k} + (n+1)Σ C(n,k)R_kD_{n−k}.
   My D_0..D_40 reproduce **all 41 entries** of the frozen derivative-table.json
   and the D40 integer-coefficient polynomial (degree 21 in t = c²) exactly.

B. **Fully separate structure: exact power series.** r(x) = Σa_nxⁿ with a_0 = c,
   a_1 = −1, (n+1)a_{n+1} = a_{n−1}; solved r² = (1−x·r)F coefficientwise and
   extracted F_40. 40!·F_40 equals the recurrence D_40 identically, and evaluates
   at c² = π/2 to
   −24628065653022778370272.2022227366258310805590422078980816668976846944760521069133173158958288…
   — matching the parent's recorded decimal digit-for-digit (to the recorded
   precision).

C. **Bernstein certificate, exact.** Both stored lists (raw and binomial-scaled)
   satisfy scaled_k = raw_k·C(21,k); all 22 coefficients strictly negative; the
   identity P(a + (b−a)u) = Σ scaled_k·u^k(1−u)^{21−k} verified by exact
   polynomial expansion; a = 392699/250000 = 3141592/2000000 = 1.570796,
   b = 3141593/2000000 = 1.5707965, b − a = 1/2000000.

D. **Rigorous π bounds reproduced from scratch.** Machin π = 16 arctan(1/5) −
   4 arctan(1/239) with alternating-series rational bounds gives the exact
   interval containing π with 3.141592 < π < 3.141593, hence a < π/2 < b with
   strict inequalities. No floating-point is trusted anywhere in the sign proof.
   (The parent's claim of "proved six-decimal bounds" is confirmed; the proof is
   elementary and my re-derivation is independent.)

E. **Positive-input violation is genuine.** r is entire and r′(0) = −1 ≠ 0, so
   F = −r²/r′ is analytic near 0; F^{(40)} is continuous and
   F^{(40)}(0) = P(π/2) < 0 **exactly** (A–D). Hence ∃δ > 0 with F^{(40)}(x) < 0
   for **every** 0 < x < δ — an open positive interval, violating the CM
   condition (−1)^{40}F^{(40)} ≥ 0. This is not a boundary-only loophole.
   Confirmed at 120 digits by the independent series at x ∈ {1/1000, 1/200,
   1/100, 1/50} (diagnostic only).

F. **Third independent structure (numeric, diagnostic).** Direct 50-digit
   numerical differentiation of the literal function F built from complex erfc:
   F^{(40)}(0) ≈ −2.462806565302277837e22 (≈19 digits agreement with the exact
   value), F^{(40)}(0.01) ≈ −2.4433185744922557899e22 < 0; r(0) = √(π/2),
   r′(0) = −1 confirmed.

G. **Parent's verifier reproduced.** Running the frozen verify_certificate.py on
   the frozen inputs reproduces certificate-check.json byte-identically
   (including the 3.99e-83 Cauchy-quadrature diagnostic).

**MATH: PASS.** The refutation of Conjecture 3 at n = 0 is mathematically
established by the frozen evidence. The 40th derivative is not claimed minimal
anywhere in the frozen material (correct posture).

## 3. FORMAL gate — not assessed

Read line-by-line: `formal/Mills.lean` (13 declarations, matches provenance) and
`formal/DerivativeRecurrence.lean` (6 declarations, matches). Both are faithful
to the mathematics above: literal Gaussian tail via `∫ t in Ioi x`, ODE
`mills_hasDerivAt` (x·mills − 1), `mills_zero_sq` (π/2), `quotient_eq`
(r²/(1−x·mills)), the near-zero identity, the R-recurrence, and the D-recurrence
statement. No completed endpoint exists (no DerivativeTable/Sign/Identification
or SourceCounterexample declaration is frozen; those files exist in the parent's
worktree as development and were deliberately not reviewed). I could not
independently recompile (no Lean toolchain in this review environment); the
parent's .olean artifacts and empty build logs are consistent with "support
compiles clean" but this remains parent-attested. **No formal gate is claimed.**

## 4. NOVELTY gate — bounded screen

See `novelty/novelty-screen.md`. Highlights:
- MathDB 351688 refetched: open/empty (not novelty evidence by itself, but no
  resolution recorded).
- All three OpenAlex citers' **full bodies** compared: bessel2026 (one passing
  citation of FS23 Section 2), unimodal2408.01755 (bibliography-only citation),
  fox2502.10483 (no trace of FS23 in retained text). None touches derivative
  ratios of Mills ratio.
- Yang 2507.10954 §4.4: CM of differences-of-products of Mills moments —
  weighted, not quotient; does not cite FS23.
- Xu–Yang 2026 (10.1186/s13660-026-03505-9), full HTML body scanned: zero
  Ferreira/Simon/2108.09244 occurrences; studies Y_{a,b}(x) = (x²+a)R² + bxR.
  Its own Conjecture 7.1 is unrelated.
- Salazar 2606.31647: Hankel/STP in the order parameter p at fixed x —
  orthogonal axis; no Conjecture 3 mention; no subsumption.
- Author follow-up 2212.07974: Wright-function log-concavity, unrelated.
- 8 targeted searches: no prior refutation or proof located.

**NOVELTY: PASS (provisional, bounded).** A serious screen found nothing
excluding the result. It is NOT an absolute-priority claim. Final acceptance
requires the parent's full formal/manuscript-stage novelty review.

## 5. Findings

**Decisive (blocking): none.**

**Non-blocking notes:**
1. `verify_certificate.py` asserts `a == 3141592/2000000` while PROOF.md writes
   a = 392699/250000; these are the same rational (1.570796). Cosmetic only.
2. The certificate JSON stores both raw and binomial-scaled Bernstein lists;
   the parent's script checks the scaled list. I verified **both** lists and
   their exact relation; no normalization ambiguity.
3. The Cauchy-quadrature diagnostic is correctly labeled diagnostic in the
   frozen material; it plays no role in the sign proof. Agreed.
4. The E-stage series truncation (n ≤ 159) is diagnostic; the rigorous
   positive-input argument is continuity + exact sign at 0. Agreed and recorded.
5. Parent's `derivative_polynomial_sensitivity` field (~1.8e25) is a plausible
   conditioning note; unused by my checks.
6. Unproved conceptual alternative mentioned by the parent (Pringsheim +
   non-real poles of 1/(1−z·r(z)) explaining CM failure) is correctly NOT used
   in the finite proof. My check found the true radius of the F Maclaurin series
   is governed by complex zeros of r′; this stays a remark, not evidence.
7. My own checker initially contained two bugs (series sign; comparison without
   the 40! factor) that produced transient disagreements; both were fixed and
   documented. The frozen parent evidence was correct at every point of
   disagreement. (Recorded for transparency.)

## 6. Eligibility

The candidate is a **substantive new refutation of the source's own Conjecture 3
at n = 0**: exact, complete, source-faithful, and not located in prior art by a
serious bounded screen. It is not a re-derivation of known Mills CM facts (r CM,
1/r convex, Sampford bounds) and does not touch the proved √z Proposition 10.
Eligible to proceed to the parent's full formal completion, final source/math/
formal/manuscript review, deterministic packet, and fresh extracted replay.
No count or ledger edits were made in this lane.

## Artifacts in this lane

- `checker/pi_review_independent_check.py`, `checker/independent-check-result.json`
- `frozen-*` — byte-verified extracts of the 23 frozen files (23/23 hashes match
  the frozen commit; `sourcehashes/current-records.json`)
- `sources-rendered/page-29.png, page-30.png, page-31.png` — my independent
  render of arXiv v2 pp.29–31 (+ copies of the parent's PDF and render)
- `sources-published/published-version-attempt.md`,
  `sources-published/crossref-10.1090-tran-8748.json`
- `novelty/novelty-screen.md`, `novelty/mathdb-351688-refetch.json`
- `provenance.json` — this lane's provenance
