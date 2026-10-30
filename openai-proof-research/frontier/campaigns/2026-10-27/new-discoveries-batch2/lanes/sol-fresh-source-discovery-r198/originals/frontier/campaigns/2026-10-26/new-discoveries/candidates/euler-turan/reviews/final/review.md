# FINAL adversarial review — parent-euler-turan (Sokal 1804.04498v3 Conjecture 3.3 / MathDB 338918)

Reviewer: pi-euler-turan-final-review. NEW independent final reviewer; not the author/implementer
and not the preliminary reviewer. Work solo, no children. Own lane only; no shared/candidate edits,
no staging/commits, no external contact, no count changes. Candidate frozen at b1963df3ee;
all 56 hashes in final-review-hashes.json verified on MY OWN byte copy before work
(56/56 match) and re-verified after work (56/56 match). Repo AGENTS.md and ledger counting
standard read. Accepted campaign tally 23/30 and candidate credit 0 unchanged by this review.

## GATE VERDICTS

### 1. SOURCE — PASS

- Fresh arXiv fetch `fresh/1804.04498v3.pdf`, sha256 `e9dac140…4632`, byte-identical to the
  candidate's stored `sources/1804.04498.pdf` AND to a fresh UCL accepted-copy download
  (`discovery.ucl.ac.uk/id/eprint/10059424/1/1804.04498v3.pdf`, same sha256). Submission history
  shows v1,v2,v3; v3 (13 Sep 2018) is latest.
- I rendered printed page 14 to PNG (`fresh/final-p14-14.png`, 150 dpi) and visually read it:
  **Conjecture 3.3** verbatim: "Define Ẽn = En/n!. Then for all n ≥ 0 and j, k ≥ 1, we have
  (−1)^{n−1}[Ẽn Ẽn+j+k − Ẽn+j Ẽn+k] > 0. (3.14)" followed by "I do not know how to prove (3.14),
  but I have verified it for n, j, k ≤ 900." The campaign's (−1)^{n+1} equals the source's
  (−1)^{n−1} (exponents differ by 2).
- I read the actual bodies of the EGF (1.3) (sec t + tan t = Σ En t^n/n!, with the ODE
  E′ = ½[1+E²] and A000111 = 1,1,1,2,5,16,61,272,1385,7936,50521) and of the partial fractions
  (3.3) E2n/(2n)! = Σ_{k∈Z}(−1)^k[(k+½)π]^{−(2n+1)} (symmetric limit at n=0) and
  (3.4) E2n+1/(2n+1)! = Σ_{k∈Z}[(k+½)π]^{−(2n+2)}. I re-derived the normalization
  a_n = 2(2/π)^{n+1}(beta(n+1) even n / lambda(n+1) odd n) from (3.3)/(3.4) myself
  (bilateral (2k+1)^{−s} sum = 2·beta(s) for odd s; 2·lambda(s) for even s).
- Live MathDB 338918 re-fetched (`fresh/338918-page.html`, sha256 50b3b7c9…, 2026-10-27T12:04Z):
  same record id 6205565c-6bdf-40be-8835-ca1e55a5b78f, statement matches, status open,
  lean_formalization_count 0. Recorded as a status pointer, NOT novelty evidence.
- Limits: the typeset published Expo. Math. 38 (2020) 1–26 body (ScienceDirect) was NOT
  separately accessible to me (the UCL accepted copy, byte-identical to arXiv v3, is the
  operative text). Koumandos–Pedersen (Math. Nachr. 285 (2012) 2129–2156) full body 403;
  only its abstract was read (it concerns Turán inequalities for the partial-sum POLYNOMIALS
  of the generating functions — a different object, and it predates the conjecture).
  Sokal's IHP Dec-2023 problem-talk page exposes only the abstract (no problem list).

### 2. MATH — PASS (every load-bearing step independently re-derived)

My own checker, written from scratch (`final-math-check.py`, output `final-math-check-output.txt`;
supplementary `final-determinant-expansion.txt`):

1. Exact rational Taylor coefficients of the literal sec t + tan t (sympy series): E_n match
   A000111 exactly; the series equals the transcendental EGF (t=0.3, residual < 1e−30).
   Sign (−1)^{n−1}(a_n a_{n+j+k} − a_{n+j} a_{n+k}) > 0 verified on 2940 (n,j,k) triples from the
   ACTUAL coefficients — finite evidence only, not proof.
2. Normalization vs source (3.3)/(3.4): a_n = 2(2/π)^{n+1}(beta/lambda) matched against actual
   coefficients for n < 40 (residual < 1e−30).
3. Error sequence: 0 < c_n < 1 and c_{n+2} ≤ c_n/3 verified numerically for n < 60 for the
   ACTUAL series (even: paired differences; odd: positive terms; n=0: c0 = 1−π/4), and
   a_n = 2(2/π)^{n+1}(1+(−1)^{n+1}c_n) for all n < 60.
4. Determinant expansion: I derived by hand AND verified in exact rational arithmetic
   (8000 random instances, all 8 parity/index combinations) that ε_n·D = L + ε_n(−1)^{j+k}X with
   L = a + (−1)^{j+k}d − (−1)^j b − (−1)^k c, D = a_n a_{n+j+k} − a_{n+j} a_{n+k},
   a_m = 1+ε_m c_m. All four parity cases re-derived by hand:
   - j,k odd: L−X = a(1−d)+d+b+c+bc > 0; L+X = b(1−c)+c+a+d+ad > 0 (uses c,d<1). ✓
   - j,k even (b,c ≤ a/3): L−X = (a−b−c)+d(1−a)+bc ≥ a/3 + d(1−a) > 0;
     L+X ≥ a/3 − a²/9 > 0 (a<1). Note d's contraction is not even needed. ✓
   - mixed (c ≤ a/3, d ≤ b/3): L±X ≥ (2/3)(a+b) − ab/3 > 0 since 2(a+b) > ab (b<1). ✓
   The mixed j-even/k-odd case is the same lemma with b,c exchanged (the determinant is
   symmetric in j,k); the Lean `AlternatingCriterion` instantiates exactly this. 200,000 random
   instances of the criterion under the exact hypotheses: 0 counterexamples.
5. Paired-power identity (A²+AB+B²)(A^s−B^s)−(A^{s+2}−B^{s+2}) = AB(A+B)(A^{s−1}−B^{s−1}):
   re-derived by hand (factoring A^s + A^{s−1}B − AB^{s−1} − B^s = (A+B)(A^{s−1}−B^{s−1})) and
   verified symbolically in sympy for s=1..8 (residual 0); contraction follows from
   A²+AB+B² ≤ 1/3 for 0≤B≤A≤1/3.
6. Analytic bridge re-derived by hand: cot derivative at real noninteger points via the UHP
   formula along a+iy with summable majorant |m+a|^{−(k+1)} and dominated convergence; affine
   chain rule for cot(π/4 − z/2) = F(1/4 − z/(2π))/π, F = π cot πz; coefficient identity
   a_n = Σ_m (4m+1)^{−(n+1)}·4^{n+1}/(2^n π^{n+1}) = 2(2/π)^{n+1}·bilateral n; the sec+tan =
   cot(π/4−z/2) identity (verified numerically to 5e−51); n=0 handled directly (a_0 = 1 =
   2(2/π)·π/4). The parent's reconciliation items are confirmed, not adopted blindly: the
   formal route uses c0 = 1−π/4 with π < 63/20 (mathlib `Real.pi_lt_d2 : π < 3.15`) and needs
   NO conditional symmetric-series pairing; the source-known odd log-convexity is n odd with
   j,k BOTH EVEN and the even comparison likewise has j,k even (checked against p14 wording).
   No high-precision numerical certificate is inferred anywhere.

No mathematical error found. Decisive finding: none.

### 3. FORMAL — PASS (fresh isolated strict replay from my own copied bytes)

- I copied the candidate bytes into my lane (`candidate/`), verified all 56 hashes, and ran
  `verification/verify_candidate.py` FROM MY COPY with the explicit absolute Lean
  `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
  (Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52) and packages
  `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`.
  All pinned revisions (mathlib d13f23b7… + 8 dependencies) verified unmodified.
- Result (`build/verified/audit.json`): **PASS, 64 declarations, 11 modules, warnings-as-errors**,
  axioms exactly {propext, Classical.choice, Quot.sound}. All 11 module compile logs are
  0 bytes. Forbidden-token scan (sorry/admit/axiom/unsafe/native_decide) enforced by the script.
- I read ALL 64 actual declaration types and axiom reports myself from the fresh Checks.log
  (`candidate/build/verified/Checks.log`): endpoint `EulerTuran.source_conjecture_338918
  (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)` has ONLY source index hypotheses — no normalization,
  convergence, contraction or optimizer premise. `eulerGenerator` is literally 1/cos + tan on ℂ;
  `normalizedEuler` is its real derivative coefficient; `eulerGenerator_hasFPowerSeriesAt`
  states these are the GENUINE power-series coefficients (HasFPowerSeriesAt with
  ofScalars normalizedEuler); `euler_coefficient_eq_real` proves reality. The audit manifest
  sha256s match my bytes; parent audit hash f30d53e5… confirmed byte-for-byte.
- Post-replay integrity: all 56 manifest hashes re-verified after work — ALL MATCH.

### 4. BOUNDED NOVELTY / ELIGIBILITY — PASS (bounded; independent decision)

The preliminary PASS was NOT taken as a premise. My own checks:

- **All 12 OpenAlex citers now body-checked** (OpenAlex re-query: exactly 12 citing works).
  Previously body-read: Olteanu 2021 (Symmetry; Theorems 1–5 are Hahn–Banach/positive-operator/
  moment-interpolation results; Sokal only in bibliography; the word "Euler" never appears
  outside it — I verified in the fetched MDPI PDF myself), Han 1906.00103 (Trans. AMS; Hankel
  DETERMINANTS, mixed determinants partly null — cannot give all-minors strict positivity),
  Sokal 2206.15434, Pan–Zeng 1910.01747. I newly fetched and body-searched the remaining
  title-only cases: Han–Kitaev–Zhang JCTA 2025 (Strathprints author MS + arXiv 2408.12865:
  permutation statistics/Springer enumeration; zero Turán/log-concavity hits), Chen–Fang–
  Kitaev–Zhang 2411.02897 (multi-dimensional permutation patterns), Boutillier–Raschel
  1912.10410 (Martin boundary; Sokal bibliography-only), Petrov–Scott 2412.21126 (clone Schur
  functions; Sokal cited for the tridiagonal/Stieltjes correspondence only), Deb–Sokal
  2212.07232 (Genocchi; Euler numbers section is definitions/CF only), Szabłowski 2106.10461
  (Kesten moments; Sokal bibliography-only), Choi–Yoon 2407.11313 (toric nestohedra; uses
  Sokal's own KNOWN Prop 3.2 even-subsequence log-concavity as Lemma 7.4 — the known special
  case, not the conjecture), Bostan–Chapoton (HAL v3; Dirichlet-series/J-fraction moment
  lists; Sokal bibliography-only). NONE contains the normalized all-index 2×2-minor sign
  theorem. Limits: for 7 of these I read arXiv/HAL preprint bodies, not final typeset versions.
- **trureturing GitHub repository**: I shallow-cloned the FULL repo
  (the-omega-institute/trureturing, 2.4 GB, 337,684 files, 1,438 problem files) and searched
  it directly: no MathDB 338918, no Sokal 1804.04498, no normalized-Euler/Turán-minor entry.
  The only nearby items (secant-number pure-periodicity refutation mod 27; Deb–Sokal 1.4(c)
  printed-clause refutation; golden Euler-germ zeta sign) are unrelated objects. The "338918"
  string hits are hex-hash coincidences. An earlier Lin rediscovery was already excluded by
  that project itself; no new relevant entry exists.
- **count-ex-machina**: full clone (suvrit/count-ex-machina): 16 counterexample cases, none
  concerning Euler numbers or this conjecture (only an "Euler equations" literary aside).
- **google-deepmind/formal-conjectures**: cloned sparse; no 338918/Sokal-Euler entry.
- Broad searches (multiple angles: alternating Turán Euler, Sokal 3.3 resolution, 2×2 minors
  positivity, moment-sequence follow-ups, MO/MSE): no earlier proof, disproof, or subsuming
  theorem. Koumandos–Pedersen 2013 concerns partial-sum polynomial Turán inequalities —
  different object (abstract-level check; full body 403).
- No inference from empty MathDB activity arrays or zero counts. Classical even/odd subsequence
  results, partial fractions, finite n,j,k ≤ 900 checks and all helper lemmas remain uncredited.
- Decisive finding: none. No earlier or subsuming theorem identified.

### 5. MANUSCRIPT — PASS

- I rendered BOTH pages of `paper.pdf` to PNG and read them in full (`fresh/paper-page-1.png`,
  `fresh/paper-page-2.png`), and read `main.tex` line by line.
- Every formula checked: Theorem 1 = source Conjecture 3.3 (with correct n+1 ≡ n−1 note);
  Lemma 1 c_n definitions and bounds match Lean ErrorSeries/OddError/CombinedError exactly
  (including c0 = 1−π/4, c2 ≤ 1/27 < (1−π/4)/3 via π < 63/20 = 3.15 = mathlib `Real.pi_lt_d2`);
  Lemma 2 matches Lean AlternatingCriterion case-for-case (I re-derived all displayed
  inequalities; the mixed-case bound is correct as stated); the geometric-factor product equality
  4(2/π)^{2n+j+k+2} is correct; pinned mathlib revision string matches verification/pins.json.
- The "Formal scope and status" section accurately describes the actual Lean scope
  (endpoint hypotheses, genuine power-series representation, dominated-limit bridge, direct n=0).
  Bibliography contains exactly one item (Sokal). Credit-zero and pending-review language
  present; no mathematical claims beyond the formal scope; helpers/finite checks uncredited.

## Decisive findings

**None.** No mathematical error, no source-fidelity defect, no formal defect, no subsuming or
earlier theorem, no manuscript defect. All five gates PASS within their recorded limits.

## Access/coverage limits (exact)

1. Published typeset Expo. Math. 38(2020) 1–26 body not separately read (ScienceDirect);
   UCL accepted copy byte-identical to arXiv v3 is the operative text.
2. Koumandos–Pedersen 2013 full body inaccessible (403); abstract only.
3. Sokal IHP Dec-2023 problem talk: abstract page only; full slide deck not retrievable.
4. For 7 of the 12 citers I read arXiv/HAL preprint bodies, not final typeset versions
   (Olteanu MDPI PDF and Han–Kitaev–Zhang Strathprints author MS are actual publisher/author
   files; final JCTA/Symmetry typesetting not compared).
5. MathSciNet/zbMATH unavailable; searches bounded to indexed web + 3 full repo clones;
   no worldwide-priority claim is made or certifiable.
6. Finite checks (2,940 sign triples; 200k criterion instances; 8k expansion instances) are
   evidence, not proof; the proof is the formal certificate plus the analytic argument.

## Reproducible artifacts (in this lane)

- `candidate/` — my byte copy (56/56 hashes verified pre and post work).
- `candidate/build/verified/` — fresh replay: audit.json (PASS/64/3 axioms), Checks.log
  (all 64 types+axioms read), 11 empty module logs.
- `final-math-check.py`, `final-math-check-output.txt`, `final-determinant-expansion.txt`.
- `fresh/` — fresh arXiv/UCL/MathDB fetches, rendered p14, rendered both paper pages,
  9 newly fetched citer bodies, full trureturing and count-ex-machina clones, formal-conjectures
  clone, Koumandos–Pedersen receipt (403), OpenAlex 12-citer re-query.
- `fresh/sokal-ihp2023-problems.pdf` — abstract only (limit recorded).
