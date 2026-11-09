# Expanded corpus r49 — research handback (2026-11-01)

**Two literal counterexamples found, each with a full Lean endpoint that passed a fresh extracted strict replay.** I propose zero credit and do not self-accept. The campaign count stays at **3/20 beyond the 39 prior results**. Only this lane was written; reservation.json was not modified. No git operations, child agents, publication, uploads, external messages or browser tabs were used, and no background jobs remain.

## Candidates for root review

### 1. MathDB 355956: Yip's maximal subfield clique conjecture is false
- **Statement refuted.** Yip, arXiv:2101.09652 Conj. 1.4, restated as Conj. 1.1 in arXiv:2209.00864 / ALCO 6(4) 2023.
- **Counterexample.** Take q = 5⁸ and d = 3. The largest admissible r is 1. In **every** field with 5⁸ elements, F₅ is a clique of GP(5⁸,3) but not a maximal clique. The extra vertex is x = 2θ+4θ²+θ³, where θ is a root of X⁸+X⁷+2X⁶+2.
- **Why it is new to the source.** The ALCO paper says it "confirms" the conjecture, but its Theorem 1.2 assumes p^r > (n−1)². That hypothesis fails here (5 ≤ 49). The paper's checks covered only n ≤ 5, and n = 6 with q ≤ 17.
- **A second conjecture also falls.** F₅ is also a maximal subfield clique: F₂₅ and F₆₂₅ are not cliques. So the paper's remark-conjecture that the hypothesis q > (n−1)² "can be dropped" is false too. This part is a diagnostic only, not in the Lean endpoint.
- **Search.** I searched every q ≤ 5·10⁶ with an admissible case outside the theorem's range: 26 fields, 219 cases. This is the only failure.
- **Lean.** File `lean/Yip355956.lean`. Endpoints: `MathDB355956.yip_conjecture_false` (literal definitions) and `yip_conjecture_SG_false` (the same statement read with Mathlib's `SimpleGraph.fromRel`/`Maximal`). The root of the polynomial comes from a Frobenius certificate plus the splitting of X^|K|−X. The cube roots come from exact integer certificates checked by `linear_combination`.

### 2. MathDB 355701: the v₃-configuration "partial converse" is false
- **Statement refuted.** Bishop–Kuss–Peet, arXiv:2208.06912 = EJGTA 11(2) 2023, Conjecture 1. The published wording is unchanged.
- **Counterexample.** The 9₃ configuration with lines {0,2,3},{2,4,5},{3,5,8},{2,7,8},{1,3,6},{0,6,8},{0,1,4},{4,6,7},{1,5,7}. No 5 of its lines pairwise intersect. Lines 0–3 form a maximal set of 4 pairwise-intersecting lines. Every line 2-colouring has a monochromatic triangle (the minimum is 1). The conjecture fails whether "maximal" means inclusion-maximal or maximum.
- **Context.** The configuration's automorphism group has order 9. The source checked only Fano, Young, Möbius–Kantor, Pappus and Desargues. Its second printed example is not actually a v₃ configuration: point 1 lies on 4 lines.
- **Lean.** File `lean/V3Config355701.lean`. Endpoints: `conjectureInclusion_false` and `conjectureMaximum_false`. Finite checks use `decide +kernel`, connected to the literal Finset definitions by proved lemmas.

### Replay and audit (`replay-receipt.json`)
- **Result: PASS.** The packet was unzipped into an empty directory and rebuilt with `-DwarningAsError=true`.
- **Forbidden tokens:** none.
- **Axioms:** all local declarations were audited (40 + 72, including generated ones). They depend only on propext, Classical.choice and Quot.sound.
- **Environment:** Lean 4.34.1 (binary sha256 e8baaa71…), Mathlib d13f23b7.
- **Trust limit:** the prebuilt upstream oleans were trusted, not rebuilt.

## What the root still needs to do
- Independent fidelity review. The points to check are listed per ID in `results.json`.
- Significance review. Both counterexamples are small. 355956 refutes a published conjecture that its own paper calls "confirmed". 355701 is a 9-line counterexample to a 2023 journal conjecture.
- Write a paper.
- **Limits of my prior-art search** (`PRIOR-ART.md`):
  - Primary bodies read are listed there.
  - Searches were bounded, and citing literature was not fully screened.
  - The OpenAI preprints listing was screened by file path only.
  - Omega HEAD has changed to a87bdf39…; only that commit receipt was taken, so there is no Omega clearance.
  - MathDB/Palomar state was not accessed (inherited 403).
  - No worldwide novelty is claimed.

## The other 38 IDs (`results.json`)
- **Review depth.** 10 IDs got real primary reading (definitions, theorem and conjecture text): 355617, 355701, 355748, 355811, 355892, 355893, 355914, 355956, plus partial follow-up papers. 7 more had sources fetched but bodies not read. 25 got literal-statement and bounded-history review only.
- **Defects only, no credit:**
  - 355892 fails literally at Δ = 2: C₇ has semistrong index 4 > 3. Δ = 3 follows from the source's own theorem, so the real content is Δ ≥ 4.
  - 355617 fails literally by sign: the source's own formula gives χ̃(X(K₃)) = −1 < 0. The intended version is presumably about |χ̃|.
- **Source says already resolved** (bodies unread, held): 355310, 355431, 355850, 355888, 356118.
- **Sustained diagnostic, no result:** 355748 (promotion). An exact exhaustive check over all posets with n ≤ 6 confirms the bound; there is no proof.
- **The rest are parked:** no tractable exact mechanism was found within this pass.

## Reproduction (from this directory; every heavy step ran under systemd MemoryMax ≤ 8G and CPUQuota ≤ 200%)
- `python3 -I extract.py` re-extracts the literal records and hashes, checks all 20 chunk manifest hashes, and redoes the bounded history grep.
- `python3 -I scripts/yip_fast.py 5,8 600` reproduces the counterexample case. `scripts/yip_sweep.sh` runs the full sweep.
- `python3 -I scripts/v3_verify.py` and `python3 -I scripts/v3_search.py 49001 9,...,20 1200` reproduce route B.
- `python3 -I scripts/promotion_deg.py 6 1400` reproduces the promotion check.
- `python3 -I scripts/gen_yip_lean.py`, `python3 -I scripts/gen_v3_lean.py`, then `python3 -I replay.py --pack` regenerate the Lean files and rerun the replay.
- Fetch scripts write new dated receipts each run; they do not replay the original HTTP responses.

Failures and fixes are listed in `failures.md`. Mathematical routes are in `ATTEMPTS.md`, proofs in `PROOF.md`.
