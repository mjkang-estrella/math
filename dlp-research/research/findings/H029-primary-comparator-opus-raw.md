# H029 raw delegated report — not accepted wholesale

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h029-primary-comparator-audit-opus-20261008-r1`
Provider/model: claudeAgent / claude-opus-5-5
Status: completed. Retrieved 2026-10-08. Root reconciliation pending; mathematical and source claims below are reviewer assertions.

I found one source worth adding to the project: the 112-bit prime-field ECDLP record paper (Bos et al.). It is an executed full-run comparator, not a new mechanism, and none of its numbers appear anywhere in the repo yet. The other two sources I read give no bridge for single-target full cost. **Complete-work improvement is still NONE.** I made no repo edits, ran no code and launched no children. The downloaded PDFs are in `/tmp/h029lit.4NEx`, outside the repo.

To avoid repeating earlier work, I first catalogued every source already cited in STATE and the findings notes. Already covered there: Bernstein–Lange–Schwabe negation, Bos's thesis §4.6 (tag tracing), Cheon–Hong–Kim, grumpy giants (cited, not fully read), GWZ, Kuhn–Struik, Fouque–Joux–Mavromati, May–Ostuzzi, Bernstein–Lange cuberoot, Corrigan-Gibbs–Kogan, McGuire–Mueller, and the H029 arithmetic/translation-model notes. I read no other H029 initial proposals.

## 1. Bos–Kaihara–Kleinjung–Lenstra–Montgomery, IJACT 2(3) 2012
I read the [EPFL copy](https://infoscience.epfl.ch/record/164550/files/164550.pdf) §§1–3 and 4.6–4.7, plus Tables 1–3.

- **Setting:** prime field, prime-order group, single target, full range (no interval), no preprocessing. The curve has a = −3 and was generated "verifiably at random". The prime has the special form p = (2^128 − 3)/(11·6949), which is what allows "sloppy reduction"; a generic prime would use Montgomery arithmetic instead.
- **Walk:** 16-adding, affine coordinates, *no* negation map. One modular inversion is shared across 400 walks per processor core (SPU), costing about 12 cycles per iteration. Points are distinguished by 24 bits.
- **Measured cost (one solved instance, so one sample, not a distribution):**
  - About 8.5×10¹⁶ curve additions, against the heuristic √(πq/(2(1−1/16))) ≈ 8.64×10¹⁶ and the birthday estimate √(πq/2) ≈ 8.36×10¹⁶.
  - About 456 cycles per iteration with the special prime (6 sloppy multiplications at 322 cycles, 6 subtractions at 30, inversion share 12, unique representation 24, miscellaneous 68). About 580 cycles for a generic modulus.
  - Slightly more than 5×10⁹ distinguished points stored.
- **Heuristic, not proved:** for r-adding walks, expected steps are √(πq / (2(1−Σp_j²))). The reason is that a first collision can't come from a predecessor in the same partition class. Table 1 checks this empirically on 32-bit q over 10⁶ searches:
  - 16-adding without negation: 1.036, versus 1.033 predicted.
  - 16-adding with negation: 1.016, versus 1.016 predicted.
- **Bridge to the upcoming walk/full-work review:**
  - The idealized model in `H029-translation-jump-model.md` (fresh independent-uniform jumps) leaves out this known same-class factor (1−Σp_j²)^(−1/2). Adding it only makes that model cost more, so the H029 negative conclusion is unchanged. But any *positive* claim built on a deterministic partitioned walk would have to include it.
  - A competent baseline should be charged its per-iteration costs: batch inversion amortized over batch width, table/partition fetch, distinguished-point check, and distinguished-point storage.
  - The paper's ECDLP tag-tracing remarks repeat Bos's thesis §4.6, which the project already has. Text extraction garbled the fractions there, so I'm not quoting them.

## 2. Rotem–Segev, ITC 2022 (preprocessing with explicit hash functions)
I read the [Dagstuhl copy](https://drops.dagstuhl.de/storage/00lipics/lipics-vol230-itc2022/LIPIcs.ITC.2022.12/LIPIcs.ITC.2022.12.pdf) §§1–2 (intro, overview, model and Theorem 1). Until now the project only cited it in a hypothesis card.

- **What it proves:** in the unit-cost RAM model, success probability Ω̃(ST²/N) for any S, T with S − T = Ω(S), counting the hash description length and evaluation time. The proof is asymptotic, hides polylog factors, works in the generic group, and is over a uniform target in Z_N (full range).
- **Caveats:**
  - Each walk step is h·g^f(h) with f into Z_N, which is a full exponentiation per step, not a single r-adding addition. The proof does not transfer to r-adding EC walks.
  - Preprocessing time (about ST) is outside the stated tradeoff.
- **Why there's no bridge:** for one target with constant success, total cost is at least ST + T = N/T + T ≥ 2√N. So it cannot beat rho on single-target full cost; it only matters for amortized multi-target or precomputation-only settings. At most it is a citable rigorous model for charging explicit hash cost.

## 3. Neamah, J. Comput. Sci. 11(9) 2015
I read the full text from [arXiv 1607.05901](https://arxiv.org/pdf/1607.05901). It is a rejected comparator.

- The "new collisions" only check whether the walk hits one of the fixed points {O, ±P, ±Q}. That is 5 points out of q, so it needs about q/5 steps on its own, versus about √q for ordinary rho collisions.
- The paper's claim of a "five times" higher collision probability is false: the walk is compared against about i previously visited points at step i, not just these five.
- Its examples are hand-picked starts (for example R₀ = P) on 3–4 digit primes. There is no analysis.
- A web search summary attributed a "≈0.8× steps" figure to this paper. That figure is not in the text, so I treated it as a summarizer error.

## Retrieval failures
- ePrint 2022/583 PDF returned 403; the Dagstuhl copy worked.
- I also tried ePrint 2009/389 for Bos et al. and got 403. I never confirmed that number is the right paper; the EPFL copy worked.

Nothing else turned up: my searches for 2025–2026 prime-field rho or time-memory-tradeoff results returned no new primary source. I'm not claiming anything is novel just because I didn't find it.
