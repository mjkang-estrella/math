# expanded-corpus-r127 — SUMMARY (Claude Opus 5.5 investigator; no Lean/SAT run in this lane)

Reservation: 20 IDs (reserve5 rule; `reservation.json`). Exact raw corpus lines are in `raw/<id>.jsonl`. Provenance
(chunk, 1-based line, chunk/raw/statement sha256) is in `extracted.json` and in each `results.json` entry. History
check: no prior technical review of any reserved ID (`history-matches.txt`: only the r130 tag-listing line for
338887, the launch note and generic greps). Nothing here is self-accepted; credit is 0 until root decides.

## Strong candidate: 338887 — Chan–Levine Conjecture 8.3 (Abelian networks IV, Mem. AMS 2022)

**Claim.** For the sinkless rotor network on the bidirected cycle C_n (n ≥ 3) and m ≥ 1, the number of recurrent
configurations in the recurrent component C_{n,m,i} depends only on gcd(n, m, i). This is the full conjecture,
proved here together with an explicit formula:

  r(C_{n,m,i}) = (1/n) Σ_{e | gcd(n,m)} w_{n,m}(e) c_e(i),  with c_e the Ramanujan sums,

where Σ_m w_{n,m}(e) t^m = V_{n/e}/(1 − t^e)^{n/e} − 2 and V is the Lucas sequence with
p = 2 + q_e t^e, q = (1 − t^e)^2, q_e ∈ {0, 2, −2}.

**Proof idea** (`outputs/338887-proof.md`).
1. The source's cycle test reduces recurrence to "every facing rotor pair, and each Hamiltonian rotor cycle,
   contains a chip".
2. Inclusion–exclusion gives a matching sum, which equals the trace of 2×2 domino transfer matrices
   X_k = [[1+ζ, −ζ(1−tζ^k)], [1−tζ^k, 0]].
3. At a primitive e-th root ζ with e | n, the product is P^{n/e}, where P is the product over one period and
   det P = (1 − t^e)^2.
4. Tr P is a polynomial of degree ≤ e invariant under t ↦ ζt, so it equals 2 + q_e t^e (constant and top
   coefficients computed exactly).
5. Cayley–Hamilton shows the evaluated generating function has rational coefficients depending only on e.
6. Rotation (wt + m) plus Galois invariance via Ramanujan sums gives the gcd(n, m, i) dependence.

**Checks.**
- Exact DP for n ≤ 40, m ≤ 3n (2,451 rows): the conjecture holds and the closed formula matches every row exactly.
- Source Table 8.1 is reproduced.
- The trace identity is verified exactly in Q(ζ)[t] for e ≤ 12.

**Risks for root.**
- (a) Significance and routineness: about one page. It uses only the source's cycle test (plus Lemma 5.19 and the
  §8.3 uniqueness) as a bridge, and rederives the cycle case of the source's Thm 7.11. The root-of-unity, period,
  rotation and degree argument is not in the source, which calls the general case "more mysterious".
- (b) Endpoint fidelity: the Lean draft states the count form; the abelian-network semantics are not formalized.
- (c) Prior art: no resolution found in v1, v2, Chan's 2019 thesis, web searches or registries. The AMS Memoir
  print version and the citing literature are unread.

**Lean.** `formal/ChanLevine338887.lean` is an UNCOMPILED draft. It has definitions, the endpoint, and a main
theorem assembled from four lemmas, which are PLACEHOLDERS (`sorry`). The plan and size estimate are in
`outputs/338887-lean-plan.md` (main effort about 600–1200 lines for `W_primitive`). Root or a Sol worker must
complete and replay it.

## Bounded exhaustive coverage (no counterexample)

- **340073 / 340074** (FHM claw/net e-positivity; one claim, stated twice). Every (claw, net)-free graph on ≤ 11
  vertices is e-positive. The source checked ≤ 9.
  - Classes enumerated: 29,551 on 10 vertices (22,386 connected); 195,956 on 11 vertices (158,791 connected).
  - Self-tests: known expansions, chromatic polynomial check, brute-force stable-partition check.
  - The July 2026 claw-free non-Schur-positive examples (arXiv:2607.21508) contain nets, so they are irrelevant.
  - Next step: a 12-vertex sweep (about 325M candidate extensions; hours in pure Python).
- **339418** (σ_n-k-partition odd-order conjecture). Exact reformulation via comparison sequences that are
  block-constant mod k. A counterexample for k implies one for every divisor k′ > 1 of k, so prime k ≥ 5 is the
  regime the source never searched.
  - Complete non-existence for (n,k) = (9,3), (15,3), (15,5), (21,3), (25,5), (27,9).
  - Partial (timed out): (27,3), (33,3), (35,5), (35,7), (45,5), (49,7).
  - The search reproduces the source's Figure 1 (4 of 9).
- **340286** (Katthän Lecture Hall polynomiality). An exact specialize-and-interpolate test found no negative power:
  every variable for i ≤ 22, and 10 variables for i ≤ 40 (the source checked i ≤ 12). This is evidence, not a proof.
- **338579** (patience-sorting diameter bounds).
  - The upper bound 2n−4 is the source's Lemma 3.4.
  - The lower bound n−1 is open for non-standard elements.
  - New finding: the source's Lemma 3.8 is false at n = 4 (diameter 3, not ≤ 2). That is a source erratum, not a
    resolution.
  - Sweep: all evaluations with n ≤ 5 and length ≤ 9, plus part of n = 6, 7. No violation of either bound.

## Excluded
- 339402: routine bridge from Gledel–Iršič 2018 Theorem 2.4. Numerically, max e = 1.787 < 2 for n ≤ 110,
  reproducing the source's data.
- 338749: proved by Barcelo–Greene–Jarrah–Welker (SIAM J. Discrete Math. 2021).
- 340566: proved by Ho, arXiv:2603.17997 (2026, with a Lean formalization).
- 339257: proved in its own source (also by Guo–Zhou).
- 339304, 339671: imprecise statements.

## Parked (hard, famous, or tooling)
- 338744: BKW list total colouring.
- 339148: Renaudineau–Shaw E2 degeneration; partial results only (Chenal, EPIGA 2026).
- 339770: unimodular dimensions of eternal Galton–Watson trees.
- 339933: SL_4 graphsums.
- 340151: needs Gröbner-fan software; the MathDB formula paraphrase is also defective.
- 340768: #P-hardness.
- 340943: needs extremal-house data beyond the known range.
- 340948: 1/3 gap.

## Registries and access
- OpenAI/math HEAD 4eaee875 (unchanged): cached preprints listing screened.
- Omega HEAD 6ffa76e4 (new since root's b576c901; its commit touches only Bajnok–Beatty files): cached
  b576c901 trees screened. Intermediate commits were not enumerated (HEAD-only rule).
- All HTTP receipts are in `sources/**.receipt.json`. No 403 or 429 was encountered and no route was retried.
- Searches are logged in `outputs/prior-art-searches.md`.

## Resources and process notes
- Every computation ran through `scripts/limited.py` (2 CPUs, 120 s CPU, 140 s wall, 2 GiB sampled RSS, AS 8 GiB,
  MALLOC_ARENA_MAX=2), one process at a time; receipts are in `logs/*.receipt.json`.
- Peak sampled RSS was about 218 MB.
- Runs stopped by the CPU cap: clawnet-gen11-27000 and rotor-formula (first version), both rerun successfully under the same log names; lh-j1 (sympy symbolic route, replaced by lecture_hall_eval.py); psweep-7 (coverage reported is what was logged before the kill).
- One brief overlap: a 600 s tool timeout pushed the σ-orientation loop into the background, and only file reads
  occurred until it finished.
- Scripts that read no downloaded data ran with `python3 -E -P` so they could import the user-site numpy/sympy;
  scripts touching downloads ran with `-I`.
- No Lean, lake, SAT/ILP or Java was run; no git; no files outside this lane; no background job remains.
