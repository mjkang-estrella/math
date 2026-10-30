# Preliminary adversarial review — Hetyei Conjecture 6.10 (MathDB 319292) candidate

Reviewer: pi-hetyei-preliminary-review (solo, no children, default speed).
Candidate lane: `parent-flat-bernoulli` at commit 2654a9583a (checkpoint db68146d18).
Scope: SOURCE / MATH / BOUNDED-NOVELTY / ELIGIBILITY. **No formal PASS and no
acceptance is awarded or requested.** Credit stays 0; accepted total stays 21/30;
no count changes and no shared-ledger writes were made.

## 0. Verdicts

| Dimension | Verdict | One-line reason |
|---|---|---|
| Exact source | **PASS** | Conjecture 6.10, Lemma 6.9, eqs (15)–(19), (21)–(23) verified on rendered pp. 19–20 and live MathDB; target normalization independently reproduced. |
| Full proposed math (PROOF.md §§1–4) | **PASS as a route** | Every load-bearing step independently re-derived, re-computed (4 routes) and re-checked in Lean; two exposition gaps found, neither fatal (see D1, D2). |
| Bounded novelty | **PASS (bounded)** | No resolution or subsumption found in all reachable bodies/registries; decisive negative evidence against each classical subsumption (§4 below). Not a global novelty claim. |
| Substantive eligibility | **PASS as source-question resolution candidate; HOLD for acceptance** | Substantive (new mechanism), *not* an immediate known-corollary rediscovery; acceptance blocked on the still-absent formal endpoint (correctly not claimed). |

## 1. Freeze and provenance integrity

All **36/36** frozen hashes in `preliminary-review-hashes.json` were recomputed
independently and match; the freeze is preserved unchanged. Files created after
the freeze (`renewal-hansen-thesis.pdf/.txt`, `formal/SpectralMoments.lean`,
`formal/SpectralPropagation.lean`, `formal-dev/*`, checkpoint) are outside the
freeze exactly as FORMAL-CHECKPOINT.md states.

## 2. Source review — PASS

Rendered and read `sources/source-page19.png` / `source-page20.png` myself:

- **Conjecture 6.10 printed verbatim**: "For n ≥ 12 we have n·κ_{n−1} > κ_n.
  Equivalently, n·K_{n−1} > K_n holds for n ≥ 11." ✓
- **Lemma 6.9**: a_n := (−1)ⁿ(κ_{n+1} − (n+1)κ_n)/(n+1) = (−1)ⁿ(K_n − n·K_{n−1}),
  coefficient of tⁿ/n! in 1/(1 − ln(1+t)); "first 11 entries are positive, then
  a₁₂ = −519312 is negative, the subsequent entries seem to have alternating
  signs." ✓
- **Eq (15)**: Σκ_n tⁿ/n! = t/((1−t)(1−ln(1−t))); **(16)**: K_n = κ_{n+1}/(n+1) =
  nonnegative ordered-composition count (multinomial × ∏(m_i−2)!, m_i ≥ 2);
  **(17)**: ΣK_n tⁿ/n! = 1/((1−t)(1−ln(1−t))); **(18)**: K_n = (−1)ⁿ Σ s(n+1,k)(k−1)!;
  **(19)**, **(21)**, **(22)**, **(23)** as described. ✓
- Eq (23) indeed prints the integral with the sign as root described; per
  instructions it is **not** counted and **not** targeted. ✓
- **Live MathDB refetch** (my own fetch, `sources/mathdb-319292-live.html`):
  problem 319292, status **open**, **0** solutions, **0** answers, statement
  identical to Conjecture 6.10; references only math/0202304 + 0912.0573.
- **arXiv history refetch**: 0912.0573 has **only v1** (2009-12-03); journal ref
  JCTA 117 (2010) 1107–1126. No author update on arXiv. My full arXiv author
  listing for Hetyei (39 entries, through 2026-05) contains **no** follow-up on
  this conjecture.
- **OEIS A006252** (archived text): a₁₁ = 319296, a₁₂ = −519312 match; e.g.f.
  1/(1−log(1+x)); only a 2018 **asymptotic** (Kotesovec) is listed — no exact
  threshold proof. ✓ (matches root's characterization)
- Rank shift and normalization verified independently: κ_{n+1} = (n+1)K_n from
  (16) (source Example 6.3: κ₅ = 40 reproduced), so n·κ_{n−1} > κ_n (n ≥ 12) ⟺
  m·K_{m−1} > K_m (m ≥ 11) ⟺ b_n := K_n/n! − K_{n−1}/(n−1)! < 0 for n ≥ 11; and
  b_n = (−1)ⁿa_n/n!, so a₁₂ = −519312 ⟺ b₁₂ = −10819/9979200 (exact, matches).

**Access limits (uncleared, same as root's):** the published JCTA body returns
HTTP 403 for me as well (I retried; `hetyei-published-access.html` retained);
Sterling–Stirling 2018 final body paywalled; the Timber fetch is a thesis
containing the author chapter, not a standalone journal PDF. None of these is
cleared by abstract or citation count. The published-version caveat is mitigated
but not eliminated by the live open MathDB status and v1-only arXiv history.

## 3. Math review — PASS as a route

I verified every load-bearing claim with **different algorithms** from root's
(`verify_recurrence.py` uses exact-rational moment/probability recurrences; I
used power-series long division, literal combinatorial formulas, and
`numpy.linalg.eigh` on actual arrowhead matrices). Artifacts:
`independent_checker.py`, `independent-check.json`.

1. **Literal normalization.** (1−t)(1−log(1−t)) = 1 − Σ_{j≥2} t^j/(j(j−1))
   re-derived from the rendered series; U(t) = 1/((1−t)(1−ln(1−t))) (eq 17) ✓.
2. **Exact values.** b₃ = −1/3, b₁₂ = −10819/9979200 < −1/2000 (margin
   29147/49896000), b₁₄ = −3676549/1816214400 < b₁₂, b₁₄−b₁₂ =
   −1707491/1816214400 — reproduced by (a) long division of 1/((1−t)(1−ln(1−t)))
   to order 240, (b) the literal composition formula (16) brute-forced over
   ordered compositions, (c) the signed-Stirling formula (18), (d) mpmath
   quadrature of the source integral (19). All four agree; b_n < 0 exactly for
   n = 11..239; float recurrence negative for all n ≤ 2000.
3. **Arrowhead structure.** Both sum-of-squares identities re-verified by hand
   (they are correct). numpy eigh on H_N for N ∈ {16,…,1024}: spectrum ⊆ [−1,1];
   **exactly one** negative eigenvalue every time; q ≈ 0.583 ≥ 1/2; (H²)₀₀ =
   (N+1)/(2N) exactly. The codimension-1 argument (any two orthonormal negative
   eigenvectors combine to a nonzero a=0 vector with negative form) is correct;
   repeated positive eigenvalues are harmless.
4. **Finite recurrence exactness.** The resolvent calculation
   (I−zH)₀₀⁻¹ = 1/(1 − Σ_{j≥2} p_j^{(N)} z^j) is correct, hence
   u_n^{(N)} = Σ_{j=2}^n p_j^{(N)} u_{n−j}^{(N)} **exactly** — verified to
   machine precision against matrix powers for N ∈ {3,7,16,50}.
5. **Propagation criterion.** Even step: T < S₀ from b₁₂ < 0 and q ≤ 1 give
   S₁ ≥ S₀; tangent inequality gives S_m ≥ S₀; hence b_{12+2m} ≤ q^{2m}b₁₂ ≤
   −c·4^{−m}. Odd step: d_λ = w_λ(1−λ) has mass 1, so Jensen gives
   −b_{2m+1} ≥ (−b₃)^m ≥ 4^{−m}. Both verified **numerically on actual
   eigen-decompositions** (all m, n ≤ 40, N ∈ {128,256,512}: zero violations).
   The criterion hypotheses engage from N ≥ 128 (root's own data agrees); this
   is exactly what §4's "sufficiently large N" needs.
6. **Limit preservation of strictness.** The criterion's bounds are uniform in
   N; since b₁₂ = −10819/9979200 has a strict margin over −1/2000 and
   b₁₄ − b₁₂ < 0, −b₃ = 1/3 > 1/4, the finitely many limits are eventually
   inside the hypothesis set, and passing N → ∞ preserves the quantitative
   negative bounds. Sound; no measure or contour assumption is used anywhere in
   §§2–4. The §5 integral cross-check was not needed and I did not rely on it.
7. **Lean checkpoint independently replayed.** All four modules
   (WeightedPowers, EvenPropagation, SpectralMoments, SpectralPropagation)
   compile clean via `formal/run_lean.py` (exit 0, no output); all **14**
   declarations report exactly `[propext, Classical.choice, Quot.sound]` via my
   own `#print axioms` run. The generic criterion faithfully abstracts §3
   (`spectralIncrement_tail_negative` covers all n ≥ 11; `hneg` encodes
   single-negative-eigenvalue; `weighted_power_lower` derives the genuine
   Jensen-type bound c^m ≤ Σw·z^m from the tangent inequality applied to z/c).
   These remain generic helpers, not a source endpoint — correct scope.

**Objections D1–D2 (must be fixed in the manuscript, non-fatal):**

- **D1 (§3 odd step exposition).** "Convexity … (or their tangent inequality)
  yields −b_{2m+1} ≥ (1/4)^m": the tangent inequality alone yields only the
  linear bound 1 − (3/4)m, which is useless for m ≥ 2. The correct tool is the
  normalized Jensen/power-mean bound, which the Lean helper
  `weighted_power_lower` *does* prove correctly (tangent applied to z/c). Fix
  the PROOF.md sentence; the mathematics is fine.
- **D2 (§3 S₁ ≥ S₀ compression).** "b₁₄ ≤ q²b₁₂" is asserted as following
  "together with q ≤ 1"; the actual derivation needs b₁₂ < 0 (T < S₀) plus
  q² ≤ 1, giving S₁ ≥ (S₀−T)/q² + T ≥ S₀. One added line removes the gap; the
  Lean abstraction (`even_propagation` hypothesis `hnext`) is unaffected.

Minor notes: N = 1 degenerate arrowhead ([[0,1],[1,0]]) is harmless (q = 1);
left-endpoint Riemann nodes t_i = i/N put a t=0 node whose contribution lands
only in p₂ — verified harmless; the t_{N−1} = 1−1/N node keeps v_i > 0.

## 4. Prior art / subsumption — PASS (bounded), with decisive negatives

Refetched and read live: MathDB 319292 (open, 0 solutions), arXiv abs/history
(v1 only), OEIS A006252 (asymptotic only), Hetyei's full arXiv listing (no
follow-up). Checked the four OpenAlex citers' primary texts (q-hypergeometric
2021, domino/Integers 21B, Timber thesis chapter, Sterling 2018 paywalled):
none states or resolves the conjecture.

**Strongest subsumption candidates — each independently refuted:**

- **Kaluza / de Bruijn–Erdős / Hansen–Frenk renewal monotonicity.** I verified
  root's reading of Hansen's 1988 thesis §§2.3/3.4 (Theorems 2.3.1–2.3.4, Horn
  moment bridge). Decisively: p_j = 1/(j(j−1)) is log-convex *on its support*
  but **fails full log-convexity at j=2** (p₂² = 1/4 > 0 = p₁p₃, since p₁ = 0);
  and the renewal sequence u_n is **not log-convex at every even n ≤ 18**
  (exact check; e.g. u₁₂² > u₁₁u₁₃), so no log-convexity conclusion about u is
  even true. Theorem 2.3.4(ii)'s hypothesis fails (Σ(f_k+f_{k+1}) = 2 > 1−f₀);
  1−F(n) = 1/n is log-convex except at the single boundary point n = 1
  (f₀ = f₁ = 0), and u is in fact not non-increasing (u₄ = 1/3 > u₃ = 1/6).
  The conjecture is therefore *not* an immediate corollary of classical renewal
  monotonicity; its content is exactly the exceptional-initial-segment + exact
  threshold, which these theorems cannot deliver.
- **Zetalaw APP-0071 (Bendikov–Cygan SBF renewal monotonicity).** Our U(t) has
  ψ(s) = s(1−log s) with ψ(0)=0, ψ(1)=1 — superficially in scope. But the
  corollary's load-bearing representation 1/ψ(λ) = b + ∫e^{−λt}u(t)dt with
  nonincreasing u fails: 1/ψ(λ) = 1/(λ(1−ln λ)) is **increasing** for λ > e²
  (f′ = −(2−ln λ)/(λ²(1−ln λ)²) > 0), hence not completely monotone. Had it
  applied, it would give u_k nonincreasing for all k — false (u₁ = 0 < u₂ = 1/2).
  No subsumption.
- **Wang 2504.21176v3** (read): studies a_n = Σ_k (−1)^{k−1}(k−1)!c(n,k) — an
  extra (k−1)! per Stirling term, a different (much faster-growing) sequence
  with its own e.g.f.; not our sequence, no bearing on our signs.
- **Weniger 1005.0466v1 §6** (read): factorial-series summation of E₁; Table 1
  lists exactly our aₙ through n = 14 (same first 15 coefficients), but there is
  **no tail/sign theorem** anywhere in the section. Root's characterization
  confirmed.
- **Bényi–Yaqubi 1903.07450** (read): coloured permutations enumerate A006252
  (their Eq. for BC₀) but prove nothing about signs.
- **GitHub / registries (bounded):** unauthenticated repo searches (Hetyei
  Bernoulli game / flat Bernoulli conjecture / A006252 / sign-alternation) all
  return 0 repositories; root's code-search screen of trureturing shows only
  prime-reciprocal material (unrelated); count-ex-machina (arXiv 2608.29595 +
  repo) contains **no** match for Bernoulli/Hetyei/A006252/truncation (full-text
  search). Zetalaw handled above. This is negative evidence of bounded reach
  only — **not a novelty PASS in any global sense**.

**Characterization:** the proposal resolves an explicit printed open conjecture
by a new (spectral-propagation) mechanism built from standard tools; it is *not*
an immediate rediscovery of a known corollary. Conversely no global priority
claim is made or warranted.

## 5. Eligibility — PASS as candidate, HOLD for acceptance

- The candidate is a genuine source-question resolution attempt against a live
  open MathDB problem; not already-known; not a refuted-family repeat (unlike
  the correctly excluded Lin/Baskakov items).
- **No formal PASS** is warranted or claimed: the literal source
  composition/count bridge, arrowhead construction, actual moment/Riemann
  convergence, and source-level endpoint are all still absent from Lean; only
  generic helpers exist (correctly outside the freeze, standard axioms only).
- No paper, packet, extracted replay, count, or ledger change is made here; the
  parent owns integration, full Lean, final review, and the extracted packet.

## 6. Required actions before any formal checkpoint

1. Correct PROOF.md §3 per D1 and D2 (exposition only).
2. Record the access limits verbatim (JCTA 403, Sterling 2018 paywalled,
   Timber-is-a-thesis) in any future packet.
3. Formalization order I recommend for the endpoint: (i) arrowhead construction
   + two SOS identities; (ii) uniqueness of the negative eigenvalue; (iii)
   moment recurrence exactness via the node recursion or resolvent (no matrix
   inverse); (iv) Riemann convergence with the explicit strict margins
   (b₁₂ vs −1/2000 margin 29147/49896000 is comfortable); (v) source
   composition bridge and rank shift; (vi) replay of the three exact rational
   anchor values.

— pi-hetyei-preliminary-review, solo. No external posts; no git actions.
