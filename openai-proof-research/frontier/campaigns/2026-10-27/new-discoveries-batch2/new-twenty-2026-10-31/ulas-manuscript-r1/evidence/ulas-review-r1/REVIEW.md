# ulas-review-r1: independent adversarial review of MathDB 342364 (Ulas–Żmija Conjecture 6.1)

Reviewer: Claude Opus 5.5 (lane ulas-review-r1), 2026-11-03. This is a review, not an acceptance. Root decides.

**Overall recommendation: PROCEED_TO_LEAN.** The Lean endpoint should be the full theorem (E2 in the r130 plan), not the refutation-only endpoint E1. The reasons are in gates A and D.

| Gate | Verdict |
|---|---|
| A. Statement fidelity | QUALIFIED_PASS |
| B. Independent mathematics | PASS (minor write-up repairs listed below) |
| C. Prior art | QUALIFIED_PASS (no resolution found; access limits listed) |
| D. Significance | QUALIFIED_PASS (genuine resolution if credited as the full theorem) |
| E. Lean feasibility | QUALIFIED_PASS (feasible; one hard component; the draft needs a literal conjunction endpoint) |

## Discipline and input binding

* I read the brief and the AGENTS.md files at `openai-proof-research/`, `new-discoveries-batch2/` and `new-twenty-2026-10-31/`.
* No child agents. No Lean, lake, leanchecker or SAT solver. No git, no ledger edits, no uploads, no messages and no browser tabs. Everything was written inside this lane: TMPDIR and XDG_CACHE_HOME pointed to `tmp/`, which stayed empty.
* Every computation was one `python3 -I` process run through my own runner, `scripts/run_capped.sh`. Caps: `taskset` on CPUs 0 and 1, `ulimit -t 120`, `timeout 140`, `ulimit -v` 6 GiB and `MALLOC_ARENA_MAX=2`. Processes ran strictly one at a time, and none was left running. Each run has a `logs/<name>.log`, a `.stderr` file with `/usr/bin/time -v` output, and a `.receipt.json` holding the script and log sha256.
* None of the r130 scripts were executed or imported. All code under `scripts/` is my own.
* **r130 inputs** (455 files, the whole `expanded-corpus-r130/` tree) were hash-bound before and after the review. The files are `hashes/r130-before.sha256` and `hashes/r130-after.sha256`. Both have the digest `d84400fcf25ee84708228b883209a6380463d6327fe80545d0d7a3d5929c6145` and their contents are identical, so the inputs were unchanged. Key files (full sha256):
  * `outputs/342364-proof.md`: d940f4120ad4d3949ca7fdf691e77a7339f4b0419d5addfbc935bed97c189977
  * `results.json`: 43ce79e61decea03c49c3dd5aaf5dd496ecc2c76174df61bf72fbc115f703fd1
  * `SUMMARY.md`: 8bd5e65a38edf822beaf8acd6b950cf4bd4968343dc537d1a06560719e232c2a
  * `raw/342364.jsonl`: 048b23cc8020ed78fcc5bf7fdd19b35cb335dee81d47f914b77bfd5c69d31baa
  * `lean-draft-UNCOMPILED/Statement342364.lean`: 23afec382b4a6494bad9e17da3f27c7bdd1356896878710df33c2d56af4a9736
  * `lean-draft-UNCOMPILED/PLAN.md`: 57c07261934d3e42e1f00b1c62eea684bb42b9b088ab3fd576dac079ba609290
  * `scripts/certificate_342364.py` (read, not run): b4c2b13662a2295bd404a3fe9744b6bfd519c105959840887c8269055ae25677
* **MathDB raw line.** Line 1759 (one-based) of `lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0006.jsonl` has sha256 `048b23cc8020ed78fcc5bf7fdd19b35cb335dee81d47f914b77bfd5c69d31baa`, counting the trailing newline. That matches the brief, and the line is byte-identical to `raw/342364.jsonl`. The chunk's sha256 is 1dd3c173…5ab88.
* **Source.** `sources/1904.03398v1.pdf` has sha256 ac3acf02…1a28d, which matches its receipt (HTTP 200, 2026-11-03T11:11Z). I read the extracted text myself.

## A. Statement fidelity — QUALIFIED_PASS

**Definitions.** Source `1904.03398v1.txt` lines 125–151 and 183–186 define G_k(x) = 1/(1−x) · Π_{n≥0} (1−x^{k^n})^{−(k−1)}, C(x) := G_2(x) and c_m(n) := S_{2,m}(n), the coefficients of G_2(x)^m. For m ≥ 1, c_m(n) counts binary partitions in which part 1 takes one of 2m colours and every part 2^i with i ≥ 1 takes one of m colours. I checked this independently (`logs/sanity-def.log`):

* c_1(n) = b(2n) for n < 200;
* (1−x)C(x) = (1+x)C(x²) up to x^199;
* direct colour enumeration agrees with the series for m ≤ 8 and n < 40, with 0 mismatches;
* c_15(1) = 30, c_15(4) = 48030 and the difference is 48000 = 2^7 · 375.

r130's proof line 11–13 states the definition correctly.

**Quantifiers.** In the source text (lines 1729–1735):

* even case: k ∈ N_+ and n ∈ N_+;
* odd cases: k ∈ N and n ∈ N_+, where N contains 0 because the source writes N_+ separately. So m = 1 and m = 3 are included.

The final sentence is "In each case the equality holds for infinitely many n ∈ N."

The MathDB statement (raw line, field `statement`) reproduces all of this. Its only blemishes are cosmetic: a typo ("kin\mathbb{N}_+"), a redundant preamble ("For positive integers k,n and nonnegative integers k as specified below"), and the title "even-colored", although all three cases are included. **MathDB 342364 matches the source.**

**Parse of the final clause.** There are two readings.

* **(P1) Per-k reading, the natural one.** For every k and each of the three cases, infinitely many n give equality. In the source, k is quantified in the preceding sentences, and the clause says the constants 3 and 6 are sharp for each m. Under P1 the conjecture is the conjunction (even equality ∀k∀n) ∧ (4k+1 bound ∀k∀n) ∧ (4k+3 bound ∀k∀n) ∧ (∀k: three infinite equality sets). Negating it needs one k and one case with only finitely many equality n.
  * r130's claim for m = 15 (k = 3) supplies exactly that. The equality set is empty, so this negates P1. I verified the m = 15 bound independently; see B.
  * For the even case the "equality" clause is implied by the even formula, so only the odd cases can fail.
* **(P2) Existential reading.** In each case some k (or infinitely many pairs (k, n)) gives equality. The m ≡ 15 (mod 16) failure does not negate P2. Under P2 the conjecture is true, and r130's full theorem proves it: k = 0 gives m = 1 and m = 3, with equality at every odd n.

**Consequence.** The full r130 theorem (proof lines 30–37) settles the conjecture under either reading: false under P1, true under P2. The refutation-only endpoint (E1: m = 15) settles it only under P1. This is the main qualification.

The trailing "n ∈ N" (with 0) instead of N_+ makes no difference. At n = 0 the difference is 0, which is never an equality case, and an infinite set is unaffected by one point.

## B. Independent mathematics — PASS

### B1. Brute force from the definition (own code, exact Python integers)

`scripts/scan_def.py` computes C^m = C^{m−1}·C by multiplying by the geometric series 1/(1−x^s) for s = 1, 1, 2, 4, 8, …. This is literally the defining product, applied as power-series multiplication. For every (m, n) it checks the conjecture and r130's claimed equality sets.

| Run | Range | Result |
|---|---|---|
| `logs/scan-m1-64-n2000.log` | m ≤ 64, n ≤ 2000 | 0 violations |
| `logs/scan-m1-128-n8000.log` | m ≤ 128, n ≤ 8000 | 0 violations |
| `logs/scan-m129-520-n1000.log` | 129 ≤ m ≤ 520, n ≤ 1000 | 0 violations |

What the scans found:

* No zero differences.
* The even formula holds exactly at every point.
* Both odd lower bounds hold.
* **For every m ≡ 15 (mod 16) up to 511, the bound ν2(n)+6 is never attained.** The minimum excess equals ν2(m+1) − 3: 1, 2, 1, 3, …; for m = 255 it is 5 and for m = 511 it is 6. This is consistent with r130's unclaimed observation max(6, ν2(m+1)+3) for every m ≡ 3 (mod 4) scanned.
* r130's equality sets hold everywhere, with zero "claimed but not equal" cases:
  * every odd n for m ≡ 1 (mod 4) and for m ≡ 3, 7 (mod 16);
  * every n ≡ 2 (mod 4) for m ≡ 11 (mod 16);
  * all n for even m.
* These are sufficient sets, not exact ones. For example, m ≡ 3 (mod 16) also has equality at many even n. The proof only claims sufficiency, so this is not a defect.

### B2. Line-by-line reading of `outputs/342364-proof.md`

**Sections 2–3: framework and reduced operators.**

* **(F1), line 45.** Correct.
* **(F2), line 47.** Correct, since U_2(g(x)h(x²)) = h(x)U_2(g).
* **(F3), line 49.** Correct. The map x → −x sends w to 1/w, and s = (w+1/w)/2 = (1+x²)/(1−x²). The identities y² = w·y_new, y^{2e} = w^e y_new^e and y^{2e+1} = w^e y_new^e (w−1)/2 all hold.
* **Identity (1), lines 53–55.** Correct.
* **(F4), line 57.** Correct.
* **Divisibility by y(1+y), line 61.** Correct. T(F)(s=1) = F(1) and T(F)(s=−1) = (−1)^m F(−1).
* **Lemma R, lines 63–76.** I re-derived it independently. y(1+y) = w(w−w^{−1})/4, so T(y(1+y)R) = 2 y_new(1+y_new) Ψ(w^{m+1}R). Here Ψ(w^k) = U_{k−1}(s), and Ψ is linear over functions symmetric under w ↔ 1/w. Both stated rules follow.
* **Lemma W, lines 82–92.** I checked each monomial case by hand.
  * The only inequality used is bitlen(e+i) ≤ bitlen(e) + bitlen(i). It holds for e, i ≥ 1, and trivially when i = 0.
  * The bound 2i − bitlen(i) ≥ 1 for i ≥ 1 is correct.
  * The exact constant term [y^0]T~(R) = 2(m+1)R_0 + R_1 (line 94) is correct.
* **Readout, lines 96–100.** Correct. It uses C^m ≡ 1 (mod 2) and y(1+y) = x/(1−x)².

Machine checks (`logs/verify-operator.log`, ALL_OK, 0 failures):

1. My T on Z[y] matches U_2(C^m F) computed from honest power series: m ≤ 12, random F, 80 coefficients.
2. Identity (1) holds: m ≤ 16, j ≤ 2, o ≤ 40. Also d_j(0) = d_j(−1) = 0.
3. Lemma R holds in both the binomial and the Chebyshev-U forms: m ≤ 40, E ≤ 15.
4. The T′ rules of Section 5 hold: m ≤ 40, E ≤ 15.
5. The per-monomial gains of Lemma W hold: H-part gain ≥ 2, main-term gain ≥ 1, E = 0 gain ≥ min(1+ν2(m+1), 2); m ≤ 96, E ≤ 69.
6. The constant-term formula holds.
7. Further identities hold:
   * binom(k+a, 2a+1)(2a+1)binom(2a, a) = k·binom(k+a, a)·binom(k−1, a) for k < 200 (also proved by hand: both sides equal (k+a)!/((k−a−1)!·a!·a!));
   * the Pell factorisation T_{2k} − 1 = 8y(1+y)U_{k−1}(1+2y)²;
   * T_m + 1 = 2(1+y)W_h² for odd m.

**Section 4: even m, lines 102–120. Correct and self-contained, with no computer certificate.**

* The coefficients u_{a′} = 4^{a′} binom(k+a′, 2a′+1) are right.
* With Kummer's theorem, ν2(binom(k+a, 2a+1)) ≥ ν2(k) − s_2(a), which gives ν2(ρ_E) ≥ a + 2E − max(s_2(b) + s_2(c)) ≥ a + E.
* ρ_0 = 8k² and ρ_1 = 64k·binom(k+1, 3) are right.
* For b + c = 2^i − 1 there are no carries. The bound 2^{i+1} − 3 − 2i ≥ 0 for i ≥ 2 holds.
* The invariant step I(R, v) ⇒ I(T~R, v+1) is correct. It uses that m+1 is odd, R_1 has ν2 ≥ v+2, and H has weight ≥ v+2 (H_0 is in fact 0).
* I(r_0, a) for r_0 = ρ + T~ρ follows.
* The readout gives ν2 = a + j exactly. **Part 1 is proved.**

**Section 5: odd m, lines 122–150.**

* The factorisation T_m + 1 = (w+1)W_h² is correct. I re-derived the T′ rules through the half-angle z = w^{1/2}.
  * Even rule: y^e W_{m+e}(1+2y).
  * Odd rule: (cos((2N+3)φ) − cos((2N+1)φ)) / (2cos φ) = −sin((2N+2)φ)·tan φ = 2y_new·U_N(s).
* r_0 = 2(T′−1)G / y is correct.
* **Crude bound (2), lines 131–133.** I re-checked each term:
  * even E contributes ≥ 2F + 2 + 2e;
  * odd E contributes ≥ 2F + 3 + 2e;
  * the −G term contributes ≥ 2F + 2.
* **Closed form r_{0,0} = (2/3)m²(m+1)(m+5), line 135.** I derived it by hand: τ_1 = 2m², τ_2 = (2/3)m²(m²−1), and [y]T(y) = 2m+1, [y]T(y²) = 1, [y]T(y³) = 0.
* **Low-coefficient certificate, lines 135–139.** I recomputed it with my own code (`scripts/verify_r0.py`, `logs/verify-r0.log`, ALL_OK).
  * My own degree bound: deg_m [y^E]A_2 ≤ max_{i ≤ 2E+1}(2i + 2(E − ⌊i/2⌋)) = 4E+2, hence deg_m r_{0,F} ≤ 4F+6. Each [y^j]T_N(1+2y) is a polynomial of degree 2j in N, valid for all N ≥ 0.
  * Since r_{0,F}(qt+s) is integer-valued, it equals Σ b_i·binom(t, i) with b_i = Δ^i P(0) ∈ Z. I computed exact values for t = 0..D+6; the tail differences vanish, and the actual degree is 4F+4.
  * Results:
    * m = 4t+3: ν2 ≥ 7 for both r_{0,1} and r_{0,2}.
    * m = 16t+15: ν2 ≥ 11 for both.
    * m = 16t+11: ν2(r_{0,1}) = 7 exactly (b_0 has ν2 = 7; b_i for i ≥ 1 have ν2 ≥ 10).
  * These are rigorous facts for all t ≥ 0.
  * Explicit polynomials, useful for Lean, in `logs/explicit-r0.log`:
    * r_{0,1}(m) = (2m⁸ + 56m⁷ + 476m⁶ + 1400m⁵ + 938m⁴ − 1456m³ − 1416m²)/315;
    * r_{0,2}(m) = (4m¹² + 264m¹¹ + 6380m¹⁰ + 71280m⁹ + 379302m⁸ + 820512m⁷ − 183040m⁶ − 3127080m⁵ − 2604206m⁴ + 2235024m³ + 2401560m²)/467775.
* **Part 2, line 143.** Correct: ν2(r_{0,0}) = 1 + 1 + 1 = 3, and the coefficients for F ≥ 1 have ν2 ≥ 5.
* **Part 3, lines 145–150.** Correct.
  * j = 0: r_0 ∈ 2^6 Z[y].
  * j = 1: the monomial weights are ≥ 6, 6, 5 and ≥ 7, with gains 2, 1, 2 and ≥ 1, so ω(r_1) ≥ 7.
  * Equality cases:
    * m ≡ 3, 7 (mod 16): max(ν2(m+1), ν2(m+5)) = 3.
    * m ≡ 11 (mod 16): ν2(r_{1,0}) = 7 exactly.
* **The m ≡ 15 (mod 16) refutation.** ν2(r_{0,0}) = 3 + ν2(m+1) ≥ 7, and r_{0,1}, r_{0,2} have ν2 ≥ 11, so r_0 ∈ 2^7 Z[y]. The weight step gives ω(r_1) ≥ 8, and ω(r_j) ≥ 7 + j follows. Strictly, only ν2(r_{0,1}) ≥ 8 and ν2(r_{0,2}) ≥ 8 are needed (r130's certificate booleans assert exactly ≥ 8), and ≥ 11 holds. **The claim that equality never holds, for all n, is proved for every m ≡ 15 (mod 16).**

**Polynomial-level chain check.** For m ≤ 80 and j < 7, every invariant and ω bound in Sections 4–5 holds for the actual r_j (`logs/verify-r0.log`).

**Attempts to break it.**

* I looked for a missing base case (m = 1, 3, 11, 15; t = 0 is covered by the binomial basis).
* I looked for a zero difference, which would make ν2 infinite; none occurs, and c_m is strictly increasing for m ≥ 1.
* I tried to find an m ≡ 15 (mod 16) with equality: none up to 511, and the proof excludes it for every such m.
* I looked for a gap in Lemma W at e = 0 and at i = 0; there is none.
* I checked the parity readout's dependence on C^m ≡ 1 (mod 2); it is fine.

Nothing broke.

**Write-up repairs (not mathematical gaps; worth fixing before a paper).**

1. Line 61 assumes d_j ∈ Z[y], and the text never states that T maps Z[y] into Z[y]. It does: T_{N+1}(x) − T_N(x) = (x−1)W_N(x), so the odd rule is y^e·y·W_{m+e}(1+2y) and is integral. Alternatively, an integer x-series that is a polynomial in y has integer y-coefficients.
2. Lines 135 and 171 claim the degree bound 4F+5, while the comment in r130's `certificate_342364.py` says "proved degree bound … 4F+4". The two are inconsistent. Both are harmless, because 4F+13 check points exceed either bound, and my independent bound 4F+6 with vanishing tails confirms the result.
3. Line 150 asserts ν2 ≥ 11 for r_{0,1} and r_{0,2} when m ≡ 15 (mod 16), but r130's certificate log tests only ≥ 8. ≥ 8 is all the argument needs, and I confirmed ≥ 11.
4. Line 147's phrase "the gains above" should cite the per-monomial form of Lemma W explicitly. Its proof is per-monomial, so the statement holds.

## C. Prior art — QUALIFIED_PASS (no resolution found)

All bodies and receipts are in `downloads/` (each file has a `.receipt.json`) and in `receipts/web-searches.json`.

**OpenAlex** (allowed):

* Work W2930810148 (the source) has cited_by_count 2 (`downloads/openalex/cites-W2930810148.json`).
* **Sobolewski**, Ramanujan J. 2023, arXiv:2202.09922. I read the body. It cites the source only for Theorems 3.5 and 4.1, the p ≥ 3 automaticity results (body line 132), and is unrelated.
* **Żmija**, Acta Math. Hungar. 2023, "Arithmetic properties of colored p-ary partitions". The Springer body is paywalled; I read the abstract and reference list. It treats p-adic valuations of the values of p-ary partitions with k(p−1) colours (k = p^α and p^α − 1), not differences c_m(4n) − c_m(n).

**All of Żmija's works** (20) and **Ulas's works since 2019** (36) were listed (`works-zmija.json`, `works-ulas.json`). None addresses the conjecture. I read two bodies:

* Żmija, "High order congruences for M-ary partitions", arXiv:2403.04495 (Period. Math. Hungar. 2024). It covers uncoloured M-ary congruences p_M(m_1···m_r n − 1) and the Folsom–Homma–Ryu–Tong conjecture. Unrelated.
* Żmija, "M-ary partition polynomials", arXiv:2403.07477. It cites the source only in a list of generalisations (line 51). Unrelated.

**Searches.** OpenAlex keyword searches (colored binary 2-adic; Churchhouse congruences; 2019 onwards) and four web searches (one extended) found no statement or resolution of Conjecture 6.1. Other hits:

* Gawron–Miska–Ulas and Yu–Lei–Hong (2026) concern b_m for m = 2^k − 1 (values, boundedness).
* Courtright–Rødseth–Sellers 2008 and Rødseth–Sellers 2002 give uncoloured binary or m-ary congruences.

The classical results the source itself cites (Churchhouse; Rødseth; Gupta; source lines 1719–1725) cover m = 1 only: c_1(4n) − c_1(n) = b(8n) − b(2n). They do not give the colored cases.

**Limits.**

* Crossref, Semantic Scholar and the arXiv search API were not used, as the brief requires.
* The USM honors-thesis hit returned 403 and was not retried.
* The Żmija 2023 body was not available.
* Google Scholar's full citation graph was not checked.

The r130 receipts agree with these findings (proof §7, lines 160–166).

## D. Significance — QUALIFIED_PASS

* **What is genuine.** Before r130, the even equality for all k and both odd lower bounds were open for every m ≥ 2. The source checked them only numerically, for m ≤ 10 and n ≤ 10^5. r130 proves all of them in full scope with a new argument: the Chebyshev operator and a bit-length weight. This is not a routine consequence of a known congruence. The only known case, m = 1, is Churchhouse–Rødseth–Gupta, and Theorem 2.4 of the source concerns ν2(c_m(n)), not differences.
* **What is falsified.** The sharpness clause fails for an infinite, structured family: m ≡ 15 (mod 16). The first case, m = 15, lies just beyond the authors' range. The data indicate the true sharp constant max(6, ν2(m+1)+3), which r130 observes but does not claim. This is a substantive mathematical correction, not a typo-level artefact. On its own, though, refuting a "for infinitely many n" sharpness clause is the weakest part, and it depends on the parse.
* **Recommendation.** Credit only as a full resolution, with the Lean endpoint E2 or stronger:
  * prove the even equality, both inequalities and the explicit equality sets;
  * derive ¬Conj61 under P1;
  * optionally also derive Conj61 under P2.

  The refutation-only endpoint E1 (m = 15) should not be counted alone. It depends on the parse, and on its own it looks like a sharpness or endpoint correction.

## E. Lean feasibility — QUALIFIED_PASS

**The draft.** I read the draft (`lean-draft-UNCOMPILED/Statement342364.lean`, lines 1–56; `PLAN.md`, lines 1–35).

* `c m n := coeff n ((G (n+1))^m)` with `G N = geomStep 1 * ∏_{i<N} geomStep (2^i)` (lines 16–26) is a faithful definition. The truncation needs the lemma `coeff_G_stable` (PLAN line 10).
* **Missing:** a literal definition `Conj61 : Prop` of the full conjunction, with the per-k parse made explicit, and the endpoint `¬ Conj61`. Line 43 states only the m = 15 clause.
* **Valuation conventions.** Mathlib has `padicValInt 2 0 = 0`. Two consequences:
  * The even case correctly also asserts that the difference is nonzero (lines 50–53).
  * The odd "≥" bounds must be stated as divisibility, `2^(ν+3) ∣ d` (the form used at line 37), or with `emultiplicity`, or together with a proof that d ≠ 0. A literal `padicValInt 2 d ≥ …` would be false if d = 0. d ≠ 0 holds because c_m is strictly increasing for m ≥ 1, but that lemma must be proved.
* Including n = 0 in the "infinitely many n ∈ N" set is harmless (PLAN line 12).

**Hard component.** PLAN step 3 (lines 22–24) is the operator identity U_2(C^m F) = C^m T(F) together with Lemma R. Mathlib has no even-section operator on `PowerSeries`, and x ↦ x² substitution support is thin. A coefficient-level "sequence route" (3b) is probably cheaper.

**Moderate components.**

* Chebyshev identities over ℤ: `Polynomial.Chebyshev.T`/`U` exist, but the Pell identity, the T_m + 1 factorisation and the half-angle T′ rules need proofs.
* The bit-length weight via `Nat.size` or `Nat.log`, and Lemma W's per-monomial estimate.
* Kummer: `padicValNat_choose` exists.

**Low risk.**

* The low-coefficient facts. Replace interpolation with the explicit polynomials above: prove r_{0,F}(m) equals them via closed-form Chebyshev coefficients, or derive them symbolically, then check binomial-basis valuations with `norm_num`/`decide` (no `native_decide`).
* m ≡ 15 (mod 16) needs only ν2 ≥ 8 for r_{0,1} and r_{0,2}.

**Even E1 still needs the general-j operator identity**, though only for m = 15. The cost saving of E1 over E2 is therefore smaller than PLAN suggests. That is a further reason to target E2.

## Files in this lane

* Scripts:
  * `scripts/run_capped.sh` (runner)
  * `scripts/fetch.sh` (single-GET fetcher with receipts)
  * `scripts/scan_def.py`, `scripts/sanity_def.py`, `scripts/verify_operator.py`, `scripts/verify_r0.py`, `scripts/explicit_r0.py`, `scripts/summarize_scan.py`
* Logs, each with stderr and receipt:
  * `logs/smoke-scan`, `logs/sanity-def`
  * `logs/scan-m1-64-n2000`, `logs/scan-m1-128-n8000`, `logs/scan-m129-520-n1000`
  * `logs/verify-operator`, `logs/verify-r0`, `logs/explicit-r0`
* Hashes: `hashes/r130-{before,after}.sha256`, the file lists and UTC stamps.
* Downloads and receipts: `downloads/openalex/*`, `downloads/arxiv/*`, `downloads/springer/*` and `downloads/usm/*`. The last is a 403 HTML error page saved under a `.pdf` name.
* Receipts: `receipts/web-searches.json`.
* Machine-readable verdicts: `review.json`.
