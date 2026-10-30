# Independent adversarial FINAL review — complete peakon coefficient candidate (MathDB 372008)

Reviewer: pi-peakon-final-review (solo sub-agent, no children). Date: 2026-10-27.
Candidate: `lanes/parent-peakon-coefficients` frozen at commit `41bea8af21b2005dde02a3ff57b578141267d875`.
Review target: my own byte-copy `candidate-copy/` of the 64-path `final-review-hashes.json` manifest.

**Freeze integrity (verified, not trusted).** All 64 manifest paths hashed PASS against my copy
before any work; the copy is byte-identical to `git 41bea8af` for every hashed file (verified by
`git archive` diff; only untracked `.olean`/`build/`/`InspectSeries.lean` extras differ, none hashed,
none used). All 64 hashes re-verified PASS after the replay. `paper.pdf` = `b5573647e994afaa…`
as required. The 8 frozen-but-unhashed files at the commit (`formal/Checks.lean`, `Checks.log`,
`Support51Checks.lean`, `support51-*`, `SUPPORT51.md`, `support*-build.json`) are not part of the
review target; my replay regenerated `Checks.lean` from the manifest and did not consume them.

The preliminary 13-file freeze `e4bccde43b` is historical; `reviews/preliminary/` (report
`53019e1d…`, decision `PRELIMINARY-DECISION.md`) covers ONLY 21/3 and is not treated as a final PASS.

## Verdicts

| Gate | Verdict |
|---|---|
| G1 Exact source (published body, arXiv v3, predecessors, live MathDB record) | **PASS** |
| G2 Independent mathematics rederivation + own exact checks | **PASS** |
| G3 Fresh isolated strict replay, 121 decl / 19 modules, all reports read | **PASS** |
| G4 Wider bounded novelty / substantive screen | **PASS (bounded)** |
| G5 Final manuscript render/read, attribution, no overclaims | **PASS** |

Overall: the candidate resolves Avan–Frappat–Ragoucy, J. Phys. A **59** (2026) 245202,
Conjecture 5.2 (Eqs 5.20–5.21) with the complete partition coefficient
`a_j(k_1..k_j) = m·(j−1)! / (∏ k_i · ∏ r_s!)` via the source-conditioned determinant collapse
`det(I−tL) = 1 − Λ(z)·H(t)`, `H(t) = Σ_k h^(k) t^k / k`, plus proved formal trace-log and
multinomial bridges. The endpoint `source_conjecture_372008` covers arbitrary coherent complex
per-particle root amplitudes, all real positions (ties/unsorted handled), complex ν, z, γ with
`2z+γ ≠ 0`, all m > 0, all N; `nonnegative_source_conjecture_372008` separately covers the
literal principal `√(p_i p_j)` for all nonnegative real momenta. I found no mathematical defect,
no formal deficiency, and no subsuming prior work within my bounded screen. Credit/counting is
not mine; no acceptance is recorded here.

## G1 — Exact source: PASS

Visually read (300/110 dpi renders, `evidence/src-*.png`) the genuine IOP published PDF
(`sources/peakon-published.pdf`, 520776 bytes, fetch 200; pdfinfo: XeLaTeX/IOPP, J. Phys. A
59 (2026) 245202):

- **Eq 2.1–2.3 (paper p.2)**: `A = Σ √(p_i p_j) sinh(ν/2 (q_i−q_j)) E_ij`, `T = Σ √(p_i p_j) cosh(…) E_ij`,
  `S = Σ √(p_i p_j) s_ij sinh(…) E_ij`, sums over all i,j; `s_ij = sgn(q_i−q_j)`. Confirmed.
- **Eq 2.8 (p.3)**: `L(z) = z T^h + z^σ (T^h)^t + S` with `z^σ = −(γz/2+1)/(z+γ/2)`,
  `T^h = ½ Σ √(p_i p_j) e^{ν/2 (q_i−q_j)} E_ij`. Confirmed at 300 dpi (`evidence/eq28b-04.png`).
- **Eq 4.8 (p.8)**: rendered at 300 dpi (`evidence/eq48-L-09.png`, `eq48-zoom-09.png`):
  `L_ij(z) = √(p_i p_j)(h⁺_ij e^{ν|q_ij|/2} + h⁻_ij e^{−ν|q_ij|/2})`,
  `h⁺ = ½(1+Λ+s_ij ξ)`, `h⁻ = ½(−1+Λ−s_ij ξ)`, `Λ=(z²−1)/(2z+γ)`, `ξ=(z²+γz+1)/(2z+γ)`.
  The text-extraction trap is real (pdftotext line 664 is garbage) and resolved: I re-derived the
  entry identity `L_ij = (S + ΛT + ξA)_ij` from Eq 4.8 in **both** order cases `q_i≷q_j`
  (the `|q_ij|` pairs with `s_ij` exactly as `½(z e^x + z^σ e^{−x}) = Λ cosh x + ξ sinh x`),
  and it also matches Eq 2.8 entry-wise. Ties: `s_ij = 0`, `A_ij = 0` ⇒ `B_ij = 0`. No defect.
- **Eq 5.1, 5.4–5.6, Prop 5.1, Eq 5.17–5.19, Eq 5.18, Conjecture 5.2, Eq 5.20 (p.12),
  Eq 5.21 (p.13)**: all read visually and match the candidate's reading exactly, including
  `h^(m) = m tr[(T + ½γA)(S+A)^{m−1}]` (5.17), `ξ² = Λ²+γΛ+1` (5.18, re-derived by me
  symbolically — exact polynomial identity), `h^(1) = Σ p_i` (5.6), the two coefficient families,
  and the ordering `0 < k_j ≤ … ≤ k_1` (candidate's `k_1 ≥ … ≥ k_j` is the same convention).
  Prop 5.1 also states τ_m is a *homogeneous symmetric function of p of degree m* — the second
  leg of the coherent-root forcing, together with (5.6) via `T_ii` depending only on `p_i`.
- **Appendix C (p.19)**: explicit τ_4…τ_7 read visually; **every one of the 33 printed
  partition coefficients matches the universal formula** (I checked term-by-term, e.g.
  τ4: 1, 4/3, 1/2, 2, 1; τ5: 5/4, 5/6, 5/3, 5/4, 5/2, 1; τ6: 6/5, 3/4, 1/3, 3, 2, 1/4, 2, 9/2, 3, 1;
  τ7: 7/6, 7/10, 7/12, 7/5, 7/4, 7/9, 7/6, 7/4, 7/2, 21/8, 7/3, 21/2, 7/2, 1). The source nowhere
  proves the conjecture; §5.5 *uses* it for the cyclic-variable remark (and its loose "traces are
  all independent" remark is about a generic L, not claimed by the candidate).
- **arXiv:2512.11066v3** (`peakons2025.pdf/txt`, header "29 Jun 2026"): agrees with the published
  body at every checked equation (5.4–5.6, 5.17–5.21, App C text-identical).
- **2023 predecessor** (SciPost Phys. 15, 228): read §2.3/§4.1–4.3 text: spectral curve
  `(a²−ā²−1)/ā = (λ²−ρ²−1)/ρ` (its Eq 79) and commuting traces `τ_n(x)`; **no** determinant
  collapse, **no** coefficient conjecture, and its one-parameter family multiplies T, not the
  2026 halved family. **1995 Ragnisco–Bruschi**: Lax representation/r-matrix/Toda; invariants are
  `tr L^k` of the full matrix; no collapse statement. Grep + targeted reads confirm.
- **MathDB 372008** (`sources/mathdb372008.json`): post_type conjecture, status open, all
  activity arrays (comments, solutions, model_attempts, human_solves, replies) empty; statement
  text matches Eq 5.20–5.21. Cached record; not treated as novelty evidence.

**Source convention audit (independently re-challenged).** The source writes √(p_i p_j). I
re-derived the forcing myself: `h^(1) = tr(T + ½γA) = Σ_i T_ii` (A has zero diagonal), and (5.6)
says `h^(1) = Σ p_i`; since `T_ii` depends only on `p_i` (Eq 2.2), per-particle `T_ii = p_i`
follows, i.e. `√(p_i p_i) = p_i` — the coherent per-particle root. A per-pair principal root would
give `T_ii = |p_i|`, contradicting (5.6) for negative momenta, and Prop 5.1's homogeneity in the
`p_i`. The candidate does not silently narrow: `sourceLax` takes **arbitrary** `r : Fin N → ℂ`
(with `T_ii = r_i²`, so `r_i² = p_i` instantiates the source family, complex coherent roots
included), and the literal principal-root family is separately covered for `p_i ≥ 0`. I endorse
the preliminary audit's conclusion, reached independently.

## G2 — Independent mathematics: PASS

I re-derived every load-bearing step by hand and wrote my own exact checker from scratch
(`evidence/independent_check.py`, sha `4f242feb…`; Fractions, Bareiss determinant, direct
partition enumeration — a different design from both the parent's and the preliminary's checkers):

1. **Determinant lemma**: rank-2 lemma ⇒ `det(I−tL) = 1 − t(aP+bQ) + t²abC` with
   `a=(λ+ξ−1)/2, b=(λ−ξ+1)/2`, `a+b=λ`, `ab=(ξ−1)/2−γλ/4`; resolvent skew identity
   `R−Rᵀ = tR(B−Bᵀ)Rᵀ` sandwiched by vᵀ,u gives `P−Q = tC`; the curve condition kills all
   ξ-dependence, leaving `det(I−tL) = 1 − λ[t(P+Q)/2 + γt²C/4] = 1 − λt·tr((T+γA/2)R)`.
   I verified the cancellation `−(ξ−1)/2 + ab = −γλ/4` explicitly. Both sides are polynomials
   in t (`B^N = 0`), so evaluation at N+1 points suffices: **exact over ℚ, 210 random cases
   (N = 0…6), all PASS**, including degenerate curve points (λ=0, ξ=±1; γ arbitrary) not
   reachable through the z-parametrization, and tie cases (`u_i v_j = v_i u_j`).
2. **Source bridge**: `A=(uvᵀ−vuᵀ)/2, T=(uvᵀ+vuᵀ)/2, B=S+A` strictly upper with
   `B_ij = u_i v_j − v_i u_j (i<j)`, `B−Bᵀ = uvᵀ−vuᵀ`; Eq 4.8 ≡ S+ΛT+ξA (verified entry-wise,
   both order cases, above); `H(t) = Σ h^(k) t^k/k` with `h^(k) = k tr((T+γA/2)B^{k−1})` (5.17);
   `τ_m = tr L^m` (5.1).
3. **All-order extraction**: `−log det(I−tL) = Σ tr(L^m) t^m/m` (classical, both sides formal
   power series; `H(0)=0`); coefficient of `t^m` in `Λ^j H^j / j` collects
   `j!/∏r_s!` ordered compositions ⇒ `τ_m = Σ_j Λ^j Σ_partitions m(j−1)!/(∏k_i ∏r_s!) ∏h^(k_i)`.
   Verified **exactly** for all m ≤ 9 (including m > N via `h^(k) = 0`) against direct matrix
   powers, over 210 random instances incl. N=0, N=1, ties. The two printed families
   (`a_1(m)=1`, `a_m(1,…,1)=1`, `a_{j+1}(m−j,1^j)=m/(m−j) for j<m−1`) re-derived; the `j<m−1`
   restriction is exactly the separate all-ones case, as the source prints.
4. **Source data**: all 33 printed Appendix C coefficients match (listed under G1).

No residual hypothesis beyond the source parameter domains survives: `2z+γ≠0` is used only for
the rational parametrization (the proof itself needs only `ξ²=λ²+γλ+1`, which holds
identically, so degenerate γ is harmless); ties, unsorted positions (permutation invariance of
trace/Hamiltonians), m>N, N=0/1 are all covered. No fixed-N monomial independence or
coefficient uniqueness is used or claimed anywhere in the derivation.

## G3 — Fresh isolated strict replay: PASS

- Ran `verification/verify_candidate.py candidate-copy --packages
  …/2026-10-14/formal/.lake/packages` with Lean 4.34.1
  (`…/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, version string confirmed against
  `verification/pins.json`; mathlib `d13f23b723b…` and all 8 dependencies at pinned revisions,
  clean status) from my own copied bytes.
- Result: **PASS, 121 declarations / 19 modules**, compiler `4.34.1`, axioms
  `{propext, Classical.choice, Quot.sound}` only. All 19 module logs **empty**; only
  `Checks.log` (44,511 bytes) carries the 121 `#check`/`#print axioms` reports.
- **Receipt independently reproduced**: my `build/verified/audit.json` is **byte-identical**
  (sha `0f0d34bf36c11ba23d63260f0ce184f657747e5fab12b6b0d33f90f878f0571d`) to the parent's
  frozen `verification/full121-audit.json`, and my `Checks.log` is byte-identical to the frozen
  `verification/full121-Checks.log` (`a43cefdc…`). Not trusted — regenerated.
- All 121 type/axiom reports read (112 `[propext, Classical.choice, Quot.sound]`,
  9 `[propext, Quot.sound]`; inventory set equality with the manifest checked
  programmatically). No `sorryAx`, no `native_decide`, no unusual universe/instance artifacts.
- All 19 modules' sources read in full. Load-bearing proofs personally checked:
  `RankTwo.det_one_add_two_outer` / `det_add_two_outer` / `resolvent_pair_identity` /
  `determinant_spectral_collapse` (the ξ-cancellation is a `linear_combination` over
  `resolvent_pair_identity` and the curve hypothesis — genuine, no surrogates);
  `NilpotentCollapse` (strict-upper nilpotence via charpoly, finite geometric resolvent,
  two-sided inverses); `UpperFamily.algebraicLax_det_collapse` (only hypothesis: the curve);
  `TraceLog`/`MatrixSeries`/`FormalJacobi` (logOf derivative identity, determinant derivative
  via dual-number `Derivation`); `TraceExpansion`/`PartitionExpansion`/`HamiltonianSupport`
  (multiset product of monomials, `countPerms` multinomial, `rawHamiltonian_vanish` for k>N,
  `coeff_pow_congr_upto` support truncation); source modules (`SourceHyperbolic` exp/sinh
  identities, `SourceOrdered` S+A strictly upper **including ties**, `SourcePermutation`
  submatrix-conjugation invariance, `SourceLiteral` `Real.sqrt_mul` bridge and `spectral_curve`).
- **No hidden hypotheses**: the endpoint `source_conjecture_372008` /
  `nonnegative_source_conjecture_372008` carry only `2z+γ≠0` and `0<m` (besides the parameter
  types); no sorting/simplicity/genericity assumptions; the single witness
  `universalCoefficient p = m(j−1)!/(∏k ∏r!)` is one function for all N, m.
- Hashes re-verified after the replay: all 64 intact.

## G4 — Wider bounded novelty / substantive screen: PASS (bounded)

Primary theorem bodies actually read: the 2026 published paper (the conjecture's home; its
Prop 5.1 proves only degree-0/degree-1 structure), the 2023 predecessor (no collapse/no
coefficients; different family), the 1995 primary (tr-invariants of the full matrix only), and
MathDB 372008 (statement + empty activity). Fresh searches (DuckDuckGo provider; Exa
rate-limited 429, Brave key unavailable — my screen is therefore bounded to one engine's
coverage, candidly recorded):

- **Semiseparable/quasiseparable determinant identities**: the peakon Lax matrix is indeed
  rank-structured, and the general literature (Vandebril–Van Barel–Mastronardi et al.) gives
  representation/QR/determinant algorithms, but I found no instance of the specific
  curve-conditioned collapse `det(I−tL) = 1−Λ·Σ h^(k)t^k/k` or of any printed coefficient
  formula. Snippet/primary-page level only — residual risk recorded.
- **Full Kostant–Toda / Toda-type characteristic-polynomial invariants**: the surfaced bodies
  (f-Kotant–Toda flag-variety papers, CKP/C-Toda, Degasperis–Procesi–Toda) concern different
  Lax structures and invariant descriptions; no match found at the level accessed.
- **Peakon spectral curves**: searches surfaced only the source's own §5 and generic CH
  literature; no τ_m-expansion resolution.
- **Author followups / citers / registries**: no follow-up or citing work found; OpenAlex
  W4417515821 shows 0 citers (not treated as evidence, per rules). MathDB's own cross-reference
  list is an **artifact**: I fetched all four listed arXiv IDs (2508.18731, 2503.11912,
  2001.11599, 1808.01008) — graph-counting, Painlevé III, zonal polynomials, seaweed
  subalgebras — all decisively unrelated (also independently noted by the preliminary review).
  The record's `first_stated_year 2018` is therefore unverifiable; the genuine verifiable
  lineage is 2023 (no conjecture) → 2026 (Conjecture 5.2, open).
- Classical tools (rank-k determinant lemma, Jacobi/resolvent identities, formal trace-log,
  multinomial counting, Newton-type extraction) are credited as classical in PROOF.md and the
  paper; not counted as discoveries. The new content is the **specific source-conditioned
  collapse** and its use to determine **every** coefficient of a published open conjecture,
  including all unspecified ones — not an immediate corollary of any body I accessed, and not
  reducible to the two printed families (which leave infinitely many coefficients open).
  No absolute priority claim is made or supportable at my screen's depth.

## G5 — Final manuscript render/read: PASS

Rendered and read all three pages of the frozen `paper.pdf` (hash `b5573647…` = `build/main.pdf`;
sha bound in `paper-qa.json` together with `main.tex` `a34ad5f8…`; 3 pages, clean build):

- Abstract/Scope: honest — "Independent … final formal and manuscript review is pending; no
  priority claim or discovery credit is made here." Theorem 1's formula matches the Lean
  endpoint (`universalCoefficient`, `coherent_source_expansion`) and my derivation; Corollary 1
  matches `nonnegative_source_conjecture_372008` (literal `√(p_i p_j)`, `p_i ≥ 0`, ties
  included). Page-2 derivation matches PROOF.md and my G2 rederivation, equation by equation
  (including `ab = (ξ−1)/2 − γΛ/4` and the `ξ−1` cancellation). Page-3 formal scope states
  121 declarations / 19 modules, Lean 4.34.1, mathlib `d13f23b7…`, standard-3 replay, credit 0,
  pending final review — all verified true.
- Source attribution accurate: eq (1) = source (5.17); Theorem 1 resolves [1, Conjecture 5.2,
  Eqs (5.20)–(5.21)]; refs [1] (J. Phys. A 59 (2026) 245202, DOI 10.1088/1751-8121/ae7683,
  arXiv:2512.11066v3), [2] (SciPost Phys. 15 (2023) 228), [3] (arXiv:solv-int/9509012) are
  bibliographically correct against the actual documents (1995's journal version is Physica A
  228 (1996) 150–159; citing the arXiv is acceptable, not an error).
- One cosmetic imprecision: page 3 says "its identity `T_ii = p_i`, eq. (5.6)" — (5.6) states
  `h^(1) = Σ p_i`; the per-particle statement follows by combining it with the definition of
  `h^(1)` and Eq (2.2). The reasoning is sound (and independently re-derived in my G1);
  wording could cite "(2.2) with (5.6)". Cosmetic; no modification made per instructions.
- No fixed-N independence/uniqueness overclaim anywhere; no priority overclaim; "complex
  complex" suspicion in the abstract was a render-resolution artifact — the PDF text reads
  "coherent complex particle amplitudes".

## Decisive objections considered and resolved

1. **Eq 4.8 h±/exponent pairing** (the known text-extraction trap): challenged at 300 dpi and
   re-derived entry-level in both order cases plus Eq 2.8 agreement; resolves in the
   candidate's favor. Resolved.
2. **L = S+ΛT+ξA vs Eq 4.8**: an apparent ±sinh discrepancy I initially derived dissolved on
   careful expansion (`|q_ij|` with `s_ij`); identities exact including ties. Resolved.
3. **Coherent-root convention**: independently re-derived from (5.6)+(2.2)+Prop 5.1
   homogeneity; the formal endpoint keeps arbitrary complex `r`, and the literal nonnegative
   family is separately closed. Resolved.
4. **m>N / ties / N=0,1 / degenerate curve**: explicitly handled in Lean
   (`rawHamiltonian_vanish`, `sourceA_zero_of_equal`, empty/one-point index types) and in my
   exact checker (λ=0, ξ=±1 points, ties). Resolved.
5. **Subsumption**: no instance found; screen bounded (below). **Surviving risk, not objection.**

## Strongest surviving risks (candid)

1. **Bounded novelty screen.** My web access was DuckDuckGo-only (Exa 429, Brave key absent);
   Kostant–Toda and semiseparable bodies were checked at search/snippet plus selective primary
   level, not exhaustively. An unexamined paper could contain the collapse. No absolute
   priority is claimed by the candidate or by me.
2. **MathDB metadata unreliability** (unrelated cross-reference IDs; unverifiable
   `first_stated_year 2018`) means the record cannot be used to bound the stating-literature
   set; only the four primary documents read here bound what I can attest.
3. The unhashed frozen files (`formal/Checks.lean` etc.) are outside the manifest; a future
   packet should either hash them or exclude them explicitly. Cosmetic freeze-hygiene risk only;
   my replay did not consume them.
4. The paper's "(5.6)" wording (above) is the only presentational blemish found; it does not
   affect any claim.

No HOLD and no FAIL at any gate on the frozen bytes reviewed. This review makes no acceptance,
tally, or credit change; packet assembly and the parent's extracted final replay remain the
parent's deterministic steps.

## Evidence in this lane (all produced by this review)

- `candidate-copy/` — byte-verified review copy (64/64 hashes before and after; identical to
  commit `41bea8af` for all hashed files).
- `evidence/independent_check.py` (sha `4f242febd504193d72f8f9d9a9fa0aef66cb04624a73c5d16c9c4c872ad971e8`)
  — own exact checker; output: "PASS: 210 cases, det collapse + degenerate curve + universal
  partition identity (m<=9, incl m>N), ties, N=0/1, printed families m<=12. All exact over Q."
- `candidate-copy/build/verified/` — fresh replay artifacts; `audit.json` byte-identical to the
  parent receipt `0f0d34bf36c11ba23d63260f0ce184f657747e5fab12b6b0d33f90f878f0571d`;
  `Checks.log` `a43cefdc…` byte-identical to the frozen log.
- `evidence/src-*.png` — 300/110 dpi renders of published pp.2,3,4,8,12,13,19
  (Eq 2.1–2.3, 2.8, 4.8, 5.4–5.6, 5.17–5.21, Prop 5.1, Conj 5.2, App C).
- `evidence/paper-{1,2,3}.png` — renders of the frozen manuscript pages.
- `evidence/eq48-{L,zoom}-09.png` — 300 dpi Eq 4.8 used for the pairing re-audit.
