# Independent adversarial review: MathDB 334207 (Ding–Zhang–Ge, Conjecture 2)

Reviewer: Claude Opus 5.5, lane `bsymbol-review-r1`, 2026-11-01 (UTC 23:21 to 23:40). This is a review, not an acceptance. No credit is assigned here; only root accepts. Campaign count is unchanged at 12/20 beyond 39.

Candidate: lane `expanded-corpus-r78`, `BSYMBOL-ORDINARY-PROOF.md`, `formal/BSymbol.lean` (sha256 d4eecefd…c710), ZIP `334207-proof-source.zip` (sha256 c9f79e98…667d). The inputs were hash-bound before and after the review (471 files); they are unchanged (`receipts/input-hashes-before.txt`, `receipts/input-hashes-after.txt`).

## Bottom line

The mathematics is correct and the Lean development is technically clean and faithful. However, **gate D fails**.

The source paper itself (Ding–Zhang–Ge, Theorem 2.6 / Lemma 3.12) already reduces Conjecture 2 to one question: does a b × n matrix exist whose every b cyclically consecutive columns are linearly independent? The existence of such matrices for every n ≥ b and every q was already public on arXiv in July 2025. It appears as Kurz, arXiv:2507.07728v1, Lemma 3.5 ("faithful" codes), applied with k = b to any [n, b] code. Kurz's paper is a b-symbol coding paper that cites Ding–Zhang–Ge.

So Conjecture 2 follows in a few lines by combining published lemmas:

1. Kurz's Lemma 3.5 at k = b.
2. The source's own Theorem 2.6 / Lemma 3.12, or Liu–Pan's Theorem 5.6.
3. The Singleton bound.

Nobody appears to have stated this explicitly. Under the campaign rules, however, it is a routine corollary of public prior art. The candidate's distinct contribution is a field-independent explicit 0/1 construction with ±1 window determinants, plus a Lean formalization. Neither is enough for credit.

**Recommendation: do not accept (FAIL on significance/novelty).**

## Gate A: source fidelity (PASS)

* I read the source text (arXiv:1609.09236v1, sha256 4fe0e4b2…8630, lane copy).
  * Section 2 gives these definitions, with subscripts mod n: the b-symbol read vector π_b, D_b, wt_b, d_b = min over distinct pairs, (n, M, d_b)_q codes, and "linear" meaning a subspace of F_q^n.
  * Theorem 2.4 is the Singleton bound M ≤ q^{n−d_b+b} for b ≤ d_b ≤ n. An "MDS (n, d_b)_q b-symbol code" is a code with M = q^{n−d_b+b}.
  * Conjecture 2 (page 15) reads: "There exist linear MDS (n, 2b)_q b-symbol codes for q being a prime power, b ≥ 2 and n ≥ 2b." This matches the MathDB record exactly (raw line hash in `results.json`).
* "Linear" is F_q-linear, as in the source's "C is a subspace of F_q^n". The Lean code uses `Submodule F (Fin n → F)`. ✓
* Lean definitions (checked with `#print` in `logs/review-audit.stdout`):
  * `cyc i j = (i + j) mod n`; `bWeight` and `bDist` count i with some j < b where the coordinates differ. This is equivalent to π_b(x)_i ≠ π_b(y)_i. ✓
  * `HasMinBDist b C d` means an attained pair at distance d and all distinct pairs at distance ≥ d. This equals "min = d". ✓
  * `IsLinearMDSBSymbol b d C := HasMinBDist ∧ Nat.card C = Nat.card F ^ (n − d + b)`. With d = 2b ≤ n, the truncated subtraction is exact. ✓
  * `dzg_conjecture2`: for each `IsPrimePow q`, (i) some field of cardinality q exists, and (ii) every finite field `K : Type` with `Nat.card K = q` carries such a code. `dzg_conjecture2_field` is universe-polymorphic over every finite field. ✓
* Independent bridge (`build/ReviewFidelity.lean`, my own definitions):
  * `piB` is the literal read vector in F^b, `Db` counts unequal read-vector entries, `minDb` is the `sInf` over distinct pairs, and `IsLinMDS` uses `minDb = d` together with the cardinality condition.
  * `conjecture2_restated` uses `Fintype.card K = q` with K in any universe. It is proved from the author's endpoints.
  * Axioms: propext, Classical.choice and Quot.sound only.
* Minor fidelity notes (not objections):
  * The existence part of `dzg_conjecture2` is restricted to `Type` (universe 0). That is harmless, since the universe-polymorphic `_field` version covers every field.
  * The published FFA version's body was not accessed; the lane only saw its outline listing.

## Gate B: ordinary mathematics (PASS)

* **Lemma 2** (standard vectors plus remainder): correct.
* **Lemma 3** (bridge). I re-derived every case.
  * Windows avoiding the bridge lie inside [0, Mb) without wrapping, so they consist of cyclically consecutive e_i.
  * (A) α = 0, β < r: a = b − β ≥ 1, z = 0, K = {0..β−1}. The T-window at β is e_β..e_{r−1}, p_0..p_{β−1}.
  * (B) Full bridge: K = {z..z+r−1}. The T-window at r + z does not wrap, because z + r − 1 ≤ b − 1.
  * (C) α ≥ 1: z = b − r + α ≤ b − 1. The T-window at r + z is p_z..p_{b−1}, followed by e_0..e_{α−1}.
  * Exhaustiveness holds. The block positions before and after the bridge are disjoint because a + z ≤ b − r < b ≤ Mb.
  * The transposition and functional argument is valid.
* **Theorem A**: the strong induction is sound. For b = 1, every n % 1 = 0, so Lemma 1 applies. In the recursive call, r < b and b + r ≥ r.
* **Part 2**:
  * (a) The first b columns are I_b, so dim C = n − b.
  * (b) If wt_b(c) ≤ 2b − 1 < n, a zero window exists. After rotation the support lies in [0, n−b−1]. If the support spread is ≥ b, there are 2b distinct nonzero window starts in an integer range of length ≤ n − 1. Otherwise the support lies in one b-window, which contradicts independence.
  * (c) v_b = v_0 = e_0, so δ_0 − δ_b is a codeword with wt_b = 2b.
  * All three steps are correct.
* **Informal remark**: the claim that every window determinant is ±1 over ℤ is only sketched in the text ("signed minor extraction"). It is not used by the proof or the Lean endpoint. I verified it computationally (below) but did not prove it.
* **Attribution defect**: Part 2 is presented as the candidate's own reduction, citing only Liu–Pan. It is in fact the source's own Theorem 2.6 / Lemma 3.12 at d = 2, which states the sufficient condition "any b cyclically consecutive vectors are linearly independent" plus two dependent vectors.

### Reviewer computations (`scripts/indep_check.py`, written from the proof text and the Lean `sv`, not from the author's scripts; all under caps; logs `logs/indep-*.stdout`)

* **L**: the Lean `sv` recursion equals the ordinary-proof construction on 525 (b, n) pairs (b ≤ 15, n ≤ 5b+2).
* **W**: 306 pairs (1 ≤ b ≤ 12, b ≤ n ≤ 4b+5) and 6,810 cyclic windows, all with integer determinant ±1. For b ≤ 9, the windows also have rank b over F_2, F_3, F_4, F_5, F_7 and F_11.
* **BR**: the bridge lemma gives a b-good output for 873 *random* r-good inputs T (q ∈ {2, 3, 5}, b ≤ 8). The lemma does not depend on the recursive T.
* **P2**: for 90 *random* b-good H (q ∈ {2, 3}, b ≤ 4), ker H has size q^{n−b} and minimum b-weight exactly 2b.
* **C**: 132 constructed codes (q ∈ {2, 3, 4, 5, 7}, 2 ≤ b ≤ 6, 2b ≤ n ≤ 3b+2, |C| ≤ 600,000) were enumerated exhaustively. All have |C| = q^{n−b} and d_b = 2b. These include q = 2, b = 5 with n ∈ {11, 12, 13, 14, 16, 17}, and q = 2, b = 6 with 12 ≤ n ≤ 20. Sixteen tiny cases were re-checked over all of F_q^n, without assuming systematic form.
* **N** (negative control): repeating an adjacent column creates a dependent window, and d_b < 2b follows: (b, n, d_b) = (2, 5, 3), (3, 7, 4), (4, 9, 5).
* **K** (prior-art reproduction): Kurz's Lemma 3.5 repair procedure at k = b, run from [I_b | 0], outputs a b-good sequence in all 156 cases (q ∈ {2, 3}, 2 ≤ b ≤ 7, b ≤ n ≤ 3b+3). Its invariants were asserted after each of the 4,396 steps.

## Gate C: Lean technical audit (PASS, with the usual trust limits)

* **Extraction**: safe ZIP extraction rejects absolute paths, `..` and symlinks (`scripts/safe_extract.py`, `receipts/extract.json`). The extracted `formal/BSymbol.lean` is byte-identical to the lane's `formal/BSymbol.lean` and `fresh-replay/BSymbol.lean`.
* **Toolchain**: Lean 4.34.1 (lean sha256 e8baaa71…5550; leanchecker ccef1bfe…fcbe). Mathlib cache at d13f23b723b8a846827a245b89c10fc7d3f11612 (git HEAD verified), used read-only through LEAN_PATH.
* **Caps**: every process ran in a systemd user scope (MemoryMax=6G, MemorySwapMax=0, CPUQuota=200%), with taskset on 2 CPUs, prlimit CPU 120 s and timeout 140 s (`scripts/run_capped.sh`).
* **Strict build**: `lean -j1 -DwarningAsError=true` gave return code 0 with empty output (`logs/build-bsymbol.*`; olean sha256 f527e1a3…6b61).
* **`leanchecker -v BSymbol`**: "replaying BSymbol", return code 0.
* **`leanchecker --fresh BSymbol`**: killed by the 120 s CPU cap (return code 137), the same as the author's attempt. **Not claimed.**
* **All-declaration audit** (`build/ReviewAudit.lean`, built strictly):
  * 157 constants originate in module `BSymbol`, including generated `_proof_`, `match_`, `eq_` and WF auxiliaries.
  * 142 theorems and 14 definitions are safe. All have bodies present, checked with `value? (allowOpaque := true)`; the default `value?` hides theorem bodies in Lean 4.34. None contains `sorry`.
  * There are no axioms or opaques. Every transitive axiom set is ⊆ {propext, Classical.choice, Quot.sound}.
  * The one exception is `BSym334207.sv._unsafe_rec`, the compiler-generated auxiliary for the well-founded `sv`, with `safety = partial`. The transitive dependency closure of both endpoints (21,131 constants, 146 of them local) contains **no** unsafe or partial constant.
  * The forbidden-token scan is clean.
* **No hidden weakening found**:
  * Hypotheses are exactly 2 ≤ b and 2b ≤ n.
  * The code is a genuine `Submodule`.
  * The distance is cyclic.
  * The cardinality uses `Nat.card F`.
  * The d_b equality is two-sided.
* **Controls** (`build/ReviewFidelity.lean`):
  * The zero code is never MDS.
  * F_2^4 is not a 2-symbol MDS code with d_2 = 4: it has 16 codewords, but 2^2 = 4 would be needed.
  * The 3-weight of 10000 in F_2^5 equals 3, by `decide`.
* **Trust limits**:
  * The cached Mathlib oleans were not rebuilt from source.
  * The full fresh kernel replay of imports could not be completed within the caps.

## Gate D: prior art and routine-ness (FAIL, decisive)

1. **The source already contains the reduction.** Ding–Zhang–Ge Theorem 2.6 with d = 2, and Lemma 3.12, state the following. A linear MDS (n, 2b)_q b-symbol code exists if there are n ≥ 2b vectors of V(b, q) such that any b cyclically consecutive ones are linearly independent and two of them are dependent. Their proof of d_b ≥ d + 2b − 2 uses only conditions 1 and 3. The Singleton bound then gives equality, so the "two dependent vectors" condition is superfluous for the MDS conclusion. The source's Theorems 3.13–3.15 are attempts at exactly this sequence problem, including a concatenation trick (Theorem 3.14).
2. **The sequence existence is public.** S. Kurz, *Linear codes for b-symbol read channels attaining the Griesmer bound*, arXiv:2507.07728v1, 10 July 2025 (sha256 ffaca521…c0ca; only version on 2026-11-01).
   * Definition 3.4: a code is *faithful* if its restriction to every b cyclically consecutive coordinates is a [b, b] code. In other words, every b cyclically consecutive generator columns are independent.
   * Lemma 3.5: every [n, k, d]^b_q code with k ≥ b can be converted into a faithful [n, k, ≥ d]^b_q code.
   * Take k = b and start from any [n, b] code, for example the code generated by [I_b | 0]. The result is a b × n matrix over F_q with every b cyclically consecutive columns independent, for every n ≥ b and every prime power q. That is precisely the candidate's Theorem A, without the 0/1 entries.
   * I checked Kurz's proof for this use. The local move u'_h = u_h + u_{h+1} at h = j + i changes only the i-window S_{j+1}, which stays of dimension i, and the (i+1)-window T_j, which gains a dimension. Overall rank is preserved, so the procedure terminates.
   * Kurz's additional remark that the b-distance does not decrease is loosely argued for windows ending at h. It is irrelevant here, because at k = b faithfulness alone gives d_b = n.
   * My reproduction (section K) confirms that the procedure works.
   * Kurz cites Ding–Zhang–Ge, but only for the Singleton bound. He does not mention Conjecture 2. Liu–Pan (Corollary 5.3, Example 5.4) and Shi–Zhu–Helleseth (Theorem 23, cyclic codes) give the same dual objects ([n, b] codes with d_b = n) only for n = tb or for cyclic lengths.
3. **The routine derivation.** Combine Kurz's Lemma 3.5 at k = b with either the source's Theorem 2.6 (conditions 1 and 3) plus the Singleton bound, or Liu–Pan's Theorem 5.6. This gives Conjecture 2 for all q, b ≥ 2 and n ≥ 2b in about one paragraph. It predates the candidate (2026-11-01) by about 16 months.
4. **Explicit resolution.** I found none. My searches covered:
   * OpenAlex: all 47 works citing W2526251771 (DOI 10.1016/j.ffa.2017.10.002), with abstracts screened (`logs/citing-abstract-screen.txt`).
   * Full text of 2109.13764, 2504.10088, 2404.02471, 2309.08920, 2010.04329, 2503.20137, 2110.00805 and 2507.07728.
   * The lane's copies of 2103.16299, 2107.01717, 2206.12668, 2401.04941, 2503.12894 and 2507.07728.
   * Web searches (standard and extended).

   No paper claims Conjecture 2. Its resolution is implicit in the combination above, not stated anywhere.
5. **Unread or blocked**:
   * Huang–Liao–Tang–Zhu, *On the b-symbol weights of linear codes for large b*, FFA 107 (2025) 102647. Closed access; ScienceDirect returned 403 and was not retried. This paper may also treat the b ≥ k regime directly.
   * MDPI *On Linear Perfect b-Symbol Codes over Finite Fields* (Mathematics 2023): 403, not retried.
   * MathSciNet, zbMATH, Google Scholar and the Chinese-language literature.
   * The classical cyclic-burst-detection literature: an [n, n−b] code detecting all end-around bursts of length ≤ b is the same object.

   These can only strengthen the prior-art finding.
6. **Registries** (GitHub `/commits/HEAD` only, 2026-11-01 23:35 UTC):
   * openai/math HEAD is 4eaee87548250b2682affda7d05d947c05554bae, unchanged.
   * the-omega-institute/trureturing HEAD is da96b81f2867ffd6cc399063274c968fcc3000b6 (committed 23:33:20Z; previously seen at 6e37b782). Its HEAD commit has 7 files, with no b-symbol, symbol-pair, MDS or 334207 path or keyword.

   This is a HEAD-commit screen only, not a tree search.

## Gate E: significance (FAIL)

The conjecture is real and published, and the exact MathDB statement is now Lean-verified. However:

* The content that is new relative to the source is only the window-sequence existence (Part 1).
* That existence follows from a public 2025 lemma by a direct specialisation (k = b), applied to the source's own sufficient condition.
* Under the campaign standard ("never count a known theorem … routine corollary"), this is a routine corollary of public prior art.

The explicit 0/1 Euclid-style construction is a pleasant strengthening: it is field-uniform, with ±1 window determinants verified but not proved. It is not what the conjecture asks for, and it does not change the verdict.

## Objections (for root)

1. **(Decisive)** Prior art: Kurz, arXiv:2507.07728v1, Lemma 3.5 at k = b, together with Ding–Zhang–Ge Theorem 2.6 / Lemma 3.12 (or Liu–Pan Theorem 5.6) and the Singleton bound, already implies Conjecture 2. The candidate's prior-art section misses both the source's own reduction and Kurz's lemma, even though Kurz's paper was in the lane's own `sources/`.
2. **Attribution**: Part 2 is the source's own Theorem 2.6 / Lemma 3.12. The proof file credits only Liu–Pan for it.
3. **Unproved remark**: the ±1-determinant claim is stated without proof. It is diagnostic only.
4. **Kernel replay**: `leanchecker --fresh` was not completed within the caps, by either the author or the reviewer. The module replay and the strict build pass.
5. **Unread**: Huang–Liao–Tang–Zhu (FFA 2025), MDPI 2023, citation indexes and the burst-detection literature remain unread.

## Next actions

* Root: record 334207 as *proved in Lean, but implied by public prior art (Kurz 2025, Lemma 3.5 at k = b, plus DZG Lemma 3.12)*. Zero credit. Do not accept as a campaign solution.
* If root nevertheless wants to argue novelty, it must first obtain and read Huang–Liao–Tang–Zhu (FFA 2025) and argue why a k = b specialisation of a published lemma is not routine. I would not support that argument.
* Optionally, preserve the Lean development as a formal artefact. It is clean and faithful.

## Deliverables in this directory

* `review.json`
* `REVIEW.md`
* `scripts/` (`fetch.py`, `safe_extract.py`, `run_capped.sh`, `indep_check.py`)
* `build/` (extracted source, strict olean, `ReviewAudit.lean`, `ReviewFidelity.lean`)
* `logs/` (all runs with receipts)
* `sources/` (OpenAlex/Crossref JSON, arXiv PDFs/text with receipts, registry HEAD JSON)
* `receipts/` (input hashes before/after, extraction record, verbatim prior-art excerpts)

No background jobs were left running.
