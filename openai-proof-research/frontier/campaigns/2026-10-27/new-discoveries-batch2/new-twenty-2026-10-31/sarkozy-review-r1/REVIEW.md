# Independent adversarial review of the MathDB 353800 candidate (sarkozy-review-r1)

Reviewer: Claude Opus 5.5, lane `sarkozy-review-r1`, 2026-11-04. This is a review, not an acceptance. Root decides.

Reviewed: `expanded-corpus-r160/CANDIDATE-353800.md` (the "dossier"), `lean/MathDB353800.lean` (an uncompiled draft), the source LaTeX `sources/eprint/353800-x/main.tex` (arXiv:2203.01293v3) and the MathDB record `sources/353800.raw.jsonl`.

## Overall recommendation: **EXCLUDE**

The mathematics is correct, and I re-verified all of it with my own code. However, MathDB 353800 (Naslund's Conjecture 13) was **already refuted publicly, with a kernel-checked Lean proof, about seven weeks before the discovery lane started.**

- **The public refutation:** JD Jones, GitHub `JD-Jones-ASES/ns-lean`.
  - The repository was created on 2026-09-16T23:10Z, and the pinned commit `035e9b0c147630e35631e4401433660f695d1fba` is dated 2026-09-17T00:10Z.
  - It was imported into the Lean Pool archive (`Vilin97/lean-pool`, `LeanPool/NaslundCounterexample/`) by commit `3cdc9caf54136caa8b9e09d9c97a9dd59733b1d6` on 2026-09-20, with status "verified".
- **What it proves:** Conjecture 13 fails at k = 2, q = 3 for **every** n ≡ 0 (mod 4) with n ≥ 8.
  - The sets have sizes 810^e in P_{3,8e} and 27·810^e in P_{3,8e+4}, against 729^e and 27·729^e.
  - It also proves `16/21 ≤ liminf log D_3(n)/(n log 3)`. So at q = 3 even the **exponent** 3/4 is beaten.
- **Independent check:** I rebuilt its 810-element set in P_{3,8} from its PROOF.md description with my own code and confirmed 0 square differences (`logs/nslean.log`).

The candidate's witness (q = 5, n = 4, |A| = 160 > 125) is therefore a new parameter instance of a conjecture that is already publicly refuted. Its uniform family for q ≡ 1 (mod 4) beats the bound only by a constant factor. Under the ancestor rules ("never count a known theorem, public proof/refutation, … parameter instance, or another variant") neither can earn credit for resolving MathDB 353800.

The dossier's claims "the exponent 3/4 is untouched" (CANDIDATE line 146) and "for q ≡ 3 (mod 4) … there is no uniform proof yet; only q = 3 was checked" (line 142) are contradicted by the public record. Its prior-art screen (lines 151–171) did not search GitHub or Lean Pool.

| Gate | Verdict |
|---|---|
| A. Statement fidelity and retention | QUALIFIED_PASS |
| B. Independent mathematics | PASS (with two corrections to dossier claims) |
| C. Prior art | **FAIL** |
| D. Significance and exclusion screen | **FAIL (EXCLUDE)** |
| E. Lean route | QUALIFIED_PASS on feasibility; moot |

---

## Gate A: statement fidelity and retention (QUALIFIED_PASS)

**Source text.**
- Conjecture 13 is at `main.tex` lines 615–624. The theorem counter is shared (`\newtheorem{conjecture}[thm]`, line 27). Counting the numbered environments (Thm 1 at l.107, Rem 2, Def 3, Lem 4, Thm 5, Lem 6, Prop 7, Conj 8, Thm 9, Thm 10, Rem 11, Ex 12) gives Conjecture 13. ✔
- The conjecture reads: "Let k≥2, and suppose that gcd(k,q−1)>1. For n≡0 (2k), any set A⊂P_{q,n} that does not contain a k^th power difference has size at most |A| ≤ q^{n(1−1/k²)}. In particular, for k=2 and q odd, we conjecture that Theorem [1] is tight."

**Definitions.**
- P_{q,n} is "polynomials in T over F_q of degree < n" (l.92–93).
- A k-th power difference is "two distinct polynomials u, v such that u − v = b^k for some b ∈ F_q[T]" (l.94–96).
- The MathDB literal says "no nonzero kth-power difference", which is equivalent because u ≠ v ⇔ u − v ≠ 0. The MathDB statement otherwise matches. "Theorem should be tight" is a MathDB extraction artefact for "Theorem 1".

**Theorem 1** (l.107–115): for gcd(k, q−1) > 1 and n ≡ 0 (2k) there is A with |A| = q^{n(1−1/2k)}. For k = 2 both Theorem 1's exponent and the conjectured bound equal 3n/4. So at k = 2 the first sentence says max |A| ≤ q^{3n/4}, and the second sentence says Theorem 1 attains it. The first sentence is the conjecture proper (a universal upper bound). The second is its k = 2 specialisation together with Theorem 1.

**Exact negation.**
- To refute the first sentence one needs some q, k, n with k ≥ 2, gcd(k, q−1) > 1, 2k | n and a k-th-power-difference-free A ⊆ P_{q,n} with |A| > q^{n(1−1/k²)}. (q = 5, k = 2, n = 4, |A| = 160 > 125 qualifies.)
- The literal reading of "tight" (max = q^{3n/4}) is refuted by the same witness, since q = 5 is odd.
- An asymptotic reading of "tight" (exponent 3/4) is **not** refuted by the candidate. The candidate's gains are constant factors 1 + 1/q + 2/q². Fu–David (below) paraphrase Conjecture 13 as an exponent prediction ("predicts that 1−1/k² … is the truth"). The public ns-lean result refutes the exponent reading too, at q = 3.

**The source does not contradict this case.**
- Theorem 5 (l.297–304) and Prop 7 (l.356–368) bound only the pair method: r_{2,2}(F_q) = q.
- l.564–569 says explicitly that "one must use a different method to improve the lower bound … beyond q^{n(1−1/k²)}".
- Green's upper bound q^{n(1−c_k)} (l.97–103) is far above. The greedy bound (l.141–143) gives q² = 25 at (5,2,4).
- Nothing in the source implies or forbids |A| > q^{3n/4}.

**Retention in the version of record.**
- arXiv v3 (22 May 2022) thanks the anonymous referee (l.630–631), so it is the post-refereeing text.
- I did not read the version of record (Q. J. Math. 74 (2023), no. 2, 627–637, doi:10.1093/qmath/haac035). I did not try OUP.
- Positive retention evidence from two independent citing works that cite the version of record:
  - ns-lean README (commit 035e9b0c) quotes Conjecture 13 verbatim, matching l.615–624, and cites "Quart. J. Math. 74 (2023) 627–637".
  - Fu–David (Zenodo 10.5281/zenodo.23827027, file sha256 `76ac3e2b…`) cite "[7, Conj. 13]" with the same journal reference.
- So the unread version of record is a qualified limitation only.

Why QUALIFIED: the version of record was not read directly, and the "tight" sentence admits an exponent reading that the candidate does not refute.

## Gate B: independent mathematics (PASS)

All checks used my own code (`scripts/review_check.py`, `scripts/nslean_check.py`), run with `python3 -I` under `scripts/cap.sh` (CPU 120 s, wall 140 s, address space 1.5 GiB), one process at a time. Peak RSS was at most 18 MB. No discovery-lane code was imported or run. Lane slice files were read as JSON data only.

1. **The (5, 2, 4) witness** (`logs/q5n4.log`).
   - X was rebuilt from its definition: the 20 solutions of 4c0c2 − c1² = 2, plus t·(a², 2ab, b²) for t ∈ {1, 4} and [a:b] ∈ PG(1,5).
   - |X| = 32. It equals the dossier listing (CANDIDATE l.33–35), and the Lean `slice` (l.35–67) is the same list in the same order (`logs/lean-slice-compare.log`).
   - For q = 5, I = {1, 4} is all of the nonzero squares, so the 12 added points are exactly S.
   - |A| = 160, all distinct.
   - Every b ∈ P_{5,4} (625 polynomials) was squared by direct multiplication. Exactly 24 nonzero b give deg b² < 4, all of degree ≤ 1, giving 12 distinct nonzero squares. With b = 0 these are the 25 b's and 13 square values.
   - All 25 440 ordered pairs u ≠ v were tested: **0 square differences**. COUNTEREXAMPLE confirmed: 160 > 125 = 5^{4(1−1/4)}.
2. **Lemma 1** holds: over a field deg b² = 2 deg b, and the coefficient form is confirmed computationally. **Proposition 2** follows. ✔
3. **Theorem U** (CANDIDATE l.67–94). I re-derived each step.
   - B(v, s) = 4(z a² − y ab + x b²), with discriminant −c, a nonsquare.
   - |D^{-1}(c)| = q(q−1).
   - D(v + s) = 4t(αb − βa)² for added v.
   - D(u − v) = −4λμ(ad − bc)², so added points are adjacent only along a common isotropic line, where (λ − μ) must avoid the squares.
   - |I| = 2 is achievable for q ≥ 5 by the subgroup-order argument. Every step is correct. I = squares is necessary: with nonsquare t, step 3 fails.
   - Machine check for q = 5, 9, 13, 17, 25, 29, 37, 41, 49 (including the prime powers 9, 25, 49 that the dossier did not test; GF(p²) tables built and field-checked by my code). |X_q| = q² − q + (q+1)|I| = 32, 92, 198, 326, 678, 902, 1446, 1808, 2552, always > q², with 0 violations.
   - Full polynomial-level checks of A = X_q × F_q at n = 4 for q = 5, 9, 13 also gave 0 violations (`logs/unif-*.log`).
4. **Theorem 3** (window lift, CANDIDATE l.105–126). I re-derived the count 2(m−r)+1 free odd positions plus m−r pairs, Case A (b = T^{m−r} b′ with deg b′ ≤ 2r−1) and Case B (extreme index outside W, with partner coefficient a square or 0). The proof is correct for odd q.
   - Full check at q = 5, n = 8, r = 1: |A| = 20 000 > 15 625. For all 20 000 u and all 312 nonzero squares of degree < 8 (from all 625 b of degree < 4), u + b² ∉ A, with 0 violations (`logs/win58.log`).
5. **Lane slices, read as data**:
   - q = 3, r = 2: |X| = 297, |A| = 891 > 729.
   - GF(9): |X| = 99, |A| = 891 > 729.
   - q = 13: |X| = 209, |A| = 2717 > 2197.
   - All have 0 violations (`logs/slice-*.log`).
6. **Hoffman boundary claim** (CANDIDATE l.144): the bound is 9, 49, 121 = q² for q = 3, 7, 11, and 42.08 and 487.2 for q = 5, 13 (`logs/hoffman.log`). So at n = 4 the conjecture holds for q ≡ 3 (mod 4) primes tested, and (5, 2, 4) is the smallest counterexample at n = 4.

**Corrections to the dossier**, which are about scope rather than proof errors:
- l.146 ("The exponent 3/4 is untouched … remains open") is false. The public ns-lean result gives exponent ≥ 16/21 at q = 3.
- l.142 ("no uniform proof yet; only q = 3 was checked") ignores the public q = 3 proof for all n ≥ 8.

## Gate C: prior art (FAIL)

Receipts are in `receipts/fetch-receipts.log`, with UTC time, HTTP code, sha256, size and URL for each fetch. Downloads are in fresh directories under `downloads/`.

1. **Public refutation (decisive).**
   - Web search (2026-11-04) surfaced "Import square-difference-free counterexamples to Naslund's conjecture", github.com/Vilin97/lean-pool/pull/461. That PR URL returns 404 now; I did not retry it.
   - The lean-pool tree at main `01db1d7049cf9668bda1e9e106875ee1278b43e6` (2026-10-07) contains `LeanPool/NaslundCounterexample.lean` and 10 modules. The headers say: "Source: github.com/JD-Jones-ASES/ns-lean … Status: verified". Main declarations are `conjecture_fails` and `liminf_ge`.
   - The directory history shows the import at 2026-09-20T09:38:27Z (`3cdc9caf`), a refactor at 09:47Z, and a root import at 2026-10-01.
   - `Main.lean` proves `conjecture_fails (n) (h4 : 4 ∣ n) (h8 : 8 ≤ n) : ¬ ∀ A, DegreeBelow n A → SquareDifferenceFree A → A.card ≤ 3 ^ (3 * n / 4)`. Its docstring cites "Conjecture 13 … Quarterly Journal of Mathematics 74 (2023), 627–637".
   - Upstream `JD-Jones-ASES/ns-lean` (created 2026-09-16; 13 commits; pinned `035e9b0c`, 2026-09-17T00:10:21Z): the README and PROOF.md give the construction. It is a ten-word code in F_3^4, P = T³ − T, Q = P², and a lift L_m(B) of size 810·|B| from P_{3,m} to P_{3,m+8}.
   - The construction is explicitly limited to q = 3: "nothing is claimed at any q other than 3". It states "As of 2026-09-16 no published construction exceeds q^{3n/4}".
   - DISCLOSURE: the work was AI-assisted (Claude, GPT-6, Grok) and directed by JD Jones, with no human review claimed. I independently confirmed its n = 8 set (810 polynomials, 0 square differences).
   - This is not a campaign output: a scoped grep of the campaign's top-level files and the discovery lane's dossier and receipts found no mention of ns-lean, lean-pool or JD Jones.
2. **Fu, D. & David, R.**, "Improved lower bounds for Sárközy's theorem in function fields from independent sets in products of generalized Paley graphs". Zenodo 10.5281/zenodo.23343474, 2026-10-13; v2 is 23827027, 2026-10-31; PDF read.
   - It covers k ≥ 3 only, within Naslund's method, and stays below q^{n(1−1/k²)}. Its Theorem 1.2 notes k ≥ d. It has no k = 2 content.
   - Its Remark 2.3 (block grouping) is related in spirit but was not pursued.
   - It is not prior art for the candidate, but it is retention evidence for Conjecture 13 (Gate A).
3. **OpenAlex** (W4311051491 = the version of record, published 2022-11-30): 2 citing works.
   - "On Sárközy's theorem for shifted primes" (JAMS 2023, doi 10.1090/jams/1036; authors not checked) is in the integer setting.
   - "Intersective sets over abelian groups" (DCC 2026).
   - I read neither in full. ns-lean's README also records that neither citing paper addresses the conjecture.
   - Keyword searches found Green 2017, Lê–Liu 2013, Li–Sauermann (SIAM J. Discrete Math. 2024), 2609.12499, 2510.27573 and the van der Corput F_q[t] paper. All are upper-bound or other-shift work. The discovery lane read several of them.
4. **Lê–Liu 2013** (Acta Arith. 161, 127–143): the abstract concerns the upper bound D(N) ≪ q^N (log N)^7 / N. UWSpace returned an Anubis bot challenge (recorded, not retried), so the full text is **unread**.
5. **Theorem U** (q ≡ 1 (mod 4), constant factor) was not found in prior art. ns-lean disclaims all q ≠ 3.
   - The symmetric-bilinear-forms and rank-one-matrix-graph literature was only lightly web-searched; a PolyU paper by Sze et al. on rank-one matrix graphs over finite fields came up but was not read.
   - This remains a residual risk only for Theorem U, which has no bearing on the verdict.

Verdict: the MathDB target (the literal Conjecture 13, and even its exponent form at q = 3) was publicly refuted with a verified Lean proof before this candidate existed. **FAIL.**

## Gate D: significance and exclusion screen (FAIL; EXCLUDE)

**Against the precedents.**
- **Public proof or refutation:** the negation of Conjecture 13 is public (ns-lean, 2026-09-17; Lean Pool, 2026-09-20). Under ancestor `AGENTS.md` ("Never count a known theorem, public proof/refutation … parameter instance, or another variant") the literal refutation at (5, 2, 4) earns zero credit. MathDB's "open" status (record lastmod 2026-09-14) predates the refutation and is not novelty evidence.
- **Parameter variant:** (5, 2, 4) and the q ≡ 1 (mod 4) family are new parameters for the same refuted statement. They are also *weaker* than the public result in growth: a constant factor 1 + 1/q + 2/q² versus (10/9)^{n/8} with exponent ≥ 16/21.
- **Small exact counterexamples** (346167, 332037, 369421, 365453) qualified only "when not otherwise excluded". This one is excluded by the prior public refutation.
- Theorem U, the Hoffman tightness at n = 4 for q ≡ 3 (mod 4) primes, and the window lift are pleasant but short algebra. None of them resolves an open MathDB problem: 353800 is already resolved publicly. The one open k = 2 question left, exponent > 3/4 for q ≡ 1 (mod 4) or for general odd q, is not addressed by the candidate.
- Chronology check: our candidate is dated 2026-11-04 and the public record is 2026-09-16/20. "Later independent public counterparts" does not apply, because the public work is earlier.

## Gate E: Lean route (QUALIFIED_PASS on feasibility; moot under D)

**Cheapest literal endpoint.** `¬ Conjecture`, with `Conjecture` quantifying over all finite fields, all k and n, and the real-power bound, exactly as in the draft (l.21–27). The finite core is 32×32 slice pairs against the 12 square vectors (or 25 pairs (b0, b1)), plus the degree lemma deg b² = 2 deg b. That is ≈ 25 600 decided cases with `decide +kernel`, or ≈ 12 300 if one tests the difference against a precomputed list of 12 vectors.

**Draft assessment.** I read it but did not compile it, per the lane restriction.
- The statement is faithful.
  - The `F : Type` universe restriction (l.22) only strengthens the negation.
  - The extra `[DecidableEq F]` binder is harmless.
  - `degree < n` includes 0 (l.25).
  - `u ≠ v → u − v ≠ b^k` matches the source (l.26).
  - The bound is `Real.rpow` (l.27).
- The proof structure is sound: `natDegree_pow` gives 2·deg b ≤ 3, then `eq_X_add_C_of_natDegree_le_one`, a coefficient comparison and `slice_check` (l.124–150).
- Risks to fix when compiling:
  - (i) l.111: plain `decide` on 25 600 cases over `ZMod 5` will likely hit the default recursion or heartbeat limits. Use `decide +kernel`, never `native_decide`.
  - (ii) l.154: `decide` on `Nat.gcd 2 4` is probably fine (the kernel accelerates GMP operations); `norm_num` is a fallback.
  - (iii) l.163: `rw [e, …] at H` needs the instantiated exponent `((4:ℕ):ℝ) * (1 - 1/((2:ℕ):ℝ)^2)` to match `e`'s left side syntactically. A `have : … := by norm_num` followed by `simp only`/`norm_num [Real.rpow_natCast]` is more robust.
  - (iv) l.79 and l.122: `simp [coeff_X_pow, coeff_X, coeff_C]` may need `coeff_add`, `coeff_C_mul` and `coeff_C_mul_X_pow`. This is ordinary API drift.
- Expected axioms: propext, Classical.choice, Quot.sound.

**Why it is moot.** The general `¬ Conjecture` endpoint follows by one-line instantiation (F = ZMod 3, k = 2, n = 8, plus a cast bridge) from ns-lean's public `conjecture13_fails_3_2_8`. Formalising the q = 5 instance would be a "mere formalization / endpoint correction" of a publicly refuted statement.

## Recommendation to root

**EXCLUDE** MathDB 353800 from credit, citing the prior public, kernel-verified refutation (JD Jones, `ns-lean` @ 035e9b0c, 2026-09-17; Lean Pool `LeanPool/NaslundCounterexample` @ 3cdc9caf, 2026-09-20). This needs no further evidence. If root wants a salvage target, the only genuinely open, non-public k = 2 question I see is an **exponent** improvement beyond 3/4 for q ≡ 1 (mod 4), for example by generalising the ns-lean lift (P = T^q − T, codes in F_q^{q+1} avoiding all-square differences). That would be a different problem, not MathDB 353800. I also suggest adding GitHub code search and Lean Pool to the campaign's live-registry screen; the discovery lane checked only OpenAI/math and Omega (CANDIDATE l.166–168).

## Provenance

- **Input hashes:** before is `receipts/inputs-before.sha256` and after is `receipts/inputs-after.sha256`. They are identical: 16 files, including the dossier `20501dc2…`, the Lean draft `eb22f42d…`, main.tex `51355a33…`, the raw record `00a7798f…` and TASK.txt `47c9a7b3…`. (The before-file has one failed path line for the ancestor AGENTS.md, re-hashed on the next line.)
- **Reviewer scripts and logs:** `scripts/`, `logs/` (with `*.time` resource reports), and `receipts/review-outputs.sha256`.
- **Network receipts:** `receipts/fetch-receipts.log`.
  - Denied routes (Crossref, Semantic Scholar, the arXiv search API, ScienceDirect) were not used.
  - One bot challenge (UWSpace) and two 404s (lean-pool PR 461 via API and HTML) were not retried.
  - OpenAlex returned one 400 for a malformed filter.
  - No TLS verification was disabled. There were no git operations, no uploads, no messages and no browser use.
