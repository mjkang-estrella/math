# H031 retained giants: raw Opus prior-art review

UNREVIEWED report preserved verbatim; see H031-memory-disposition.md for root
corrections. Do not accept hardware ratios, compulsory index bits, comparator
rankings or model constants from this report without their separate justification.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h031-retained-giants-priorart-opus-20261008-r1
Provider claudeAgent; model claude-opus-5-5; COMPLETED, no pending children.

I've finished the review. The main finding: keeping solved targets' points as known-log entries is published prior art. Separately, Card1's claimed ~9% key saving is probably wiped out by the extra table operations it needs. So I don't recommend a numerical pilot yet.

I ran no experiments and wrote no files. I edited nothing in the repo, launched no children and hit no safety interruption. The source PDFs were piped straight to text, so nothing was saved to disk.

## Sources read

Local files: `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md` (lines 1–80; `TEAM.md` does not exist), `research/STATE.md` (H031/H030 sections), `research/findings/H031-memory-factory-raw.md` (all of it), `H030-storage-priorart-disposition.md`, and `H030-storage-reconciliation.md`.

Primary sources, read in full text:
1. **Kuhn–Struik, SAC 2001, LNCS 2259 pp. 212–229**, from [cr.yp.to/bib/2001/kuhn-rho.pdf](https://cr.yp.to/bib/2001/kuhn-rho.pdf). I read §§1–4 and §5.1 through the start of §5.2 (pp. 212–225).
2. **Bernstein–Lange, "Two grumpy giants and a baby" (2012-07-09)**, from [cr.yp.to/elliptic/grumpy-20120709.pdf](https://cr.yp.to/elliptic/grumpy-20120709.pdf). I read §§1–2 and §6 (pp. 1–5 and 14–15).
3. **Bernstein–Lange, "Computing small discrete logarithms faster" (2012-09-19)**, from [cr.yp.to/dlog/cuberoot-20120919.pdf](https://cr.yp.to/dlog/cuberoot-20120919.pdf). I read the abstract and the multi-target passages (pp. 1, 3, 8–9, 14–15).
4. **Fouque–Joux–Mavromati, ASIACRYPT 2014**: only the authors' slides, from [iacr.org](https://www.iacr.org/conferences/asiacrypt2014/9-1_Multi-user%20collisions%20Applications%20to%20Discrete%20Logarithm,%20Even-Mansour%20and%20PRINCE.pdf). The full paper (ePrint 2013/761) was blocked by Cloudflare.

Not read, so nothing below relies on them: GWZ's improved BSGS (the ePrint is blocked), Silverman–Stapleton, Hitchcock–Montague–Carter–Dawson (I know it only through BL's account), and keyhunt's multi-target BSGS mode.

## Claims the sources support

**Retention is known.** Kuhn–Struik §4 (pp. 218–219):
- Once x_i is solved, every distinguished point g^{a_j}h_i^{b_j} from its computation becomes a known-log point g^c, with c = a_j + x_i b_j.
- A later collision with one of these gives x_k = (c − a)b⁻¹.
- They credit the idea to Silverman–Stapleton.
- Theorem 1 gives E_L ≈ √(πN/2)·Σ C(2t,t)/4^t ≈ √(2NL) for L ≪ N^{1/4}. That idealized model counts draws until L collisions, so it effectively assumes every drawn point is stored.

BL's small-DL paper calls this "the classic algorithm" (pp. 3, 8). So "keep solved targets' points as known-log table entries" is prior art in rho/distinguished-point form.

**Different strides that make giant–giant collisions useful are known for one target.** In BL grumpy §6 (p. 14), Giant1 uses stride n and Giant2 uses stride n+1, chosen coprime "for good coverage of slopes". Their slope/anti-collision counting is the right way to assess whether coverage overlaps.

**Card1 combines these** (deterministic signed babies, giants kept per target, pairwise-prime strides, sequential solving). I did not find that exact combination in what I read. That is not a novelty claim; it looks like a direct synthesis of known parts.

**A transfer caveat that helps Card1.** BL's small-DL paper (p. 9) reports HMCD's finding that walks depending on the target miss cross-walk collisions. That penalty does not carry over to Card1, because kept BSGS records are points, and any point equality is detected.

## Cost ledger, priced against Card1's own unverified numbers (B≈0.35, Γ≈0.56, W≈0.906)

- **Keys:** 0.906 vs 1.0 √(qK)·C_x, about 9.4% fewer.
- **Inserts:**
  - Card1 inserts B+Γ ≈ 0.91√(qK) records into a dynamic table.
  - The baseline bulk-builds 0.5√(qK) records into a static one.
  - Net extra ≈ 0.41√(qK) inserts.
- **Probes:** Γ ≈ 0.56 vs 0.5, so +0.06, and into a table about 1.8× larger.
- **Break-even:** Card1 only wins if the average extra table operation costs ≲ 0.094/0.47 ≈ 0.2·C_x, before any memory price.
  - At 256-bit field sizes, an unbatched DRAM miss is roughly the cost of one C_x.
  - Batched or radix-partitioned inserts may fall below the break-even.
  - So whether Card1 wins depends on the platform, and it is marginal at best.
- **Setup (negligible when K ≪ √(qK)/log q):**
  - Blinding: K scalar multiplications.
  - Strides: K multiplications to get D_sG, plus ℓ offsets per target that can be discarded once that target is solved.
  - K pairwise-coprime strides (primes are only one convenient choice): Δ ≈ K·ln(2b), with tiling waste ≈ 1.4·√(K/q)·ln b.
  - Final verification: one scalar multiplication per target.
- **Index recovery and false positives:**
  - Kept records need roughly log₂R index bits plus a fingerprint long enough that the false-hit resolve cost (about log q group operations each) stays below the probe cost.
  - The "10×/16× bits" figure is not supported. The real ratio is (log₂R + f) divided by the bits per baby in a tuned hierarchy, and it depends on q and K.
- **Peak memory:** B + Γ records, plus the current target's giant buffer (≈ q/(2B) records), plus K stored logs.
- **Amortization assumptions:**
  - The gain needs a large K. It is zero at K=1 and smaller for early targets.
  - The range of validity is not established (compare Kuhn–Struik's L ≪ N^{1/4}).
  - Like shared BSGS, B has to be chosen knowing K in advance.
- **Comparators:**
  - **Cheaper than Card1 in keys, low memory:** Kuhn–Struik retention with negation gives about √(qK) rho steps at 5M+S each, versus Card1's C_x keys.
  - **Worse in total:** BL precomputation optimized for solve-all-K. Their measured constants (1.24, 1.77; no negation) give roughly 3√(qK) multiplications.
  - **Not priced:**
    - a growing/interleaved shared baby table across all K targets (GWZ-style);
    - using cross-target giant relations before anything is solved (FJM-graph style, which the slides claim at √(NL)).

## Unresolved objections

1. **Memoryless hazard not shown.** Blinding makes k_s uniform, but target s scans an arithmetic progression with stride D_s against a union of progressions with strides D_t. Its hits are lattice-correlated, not Poisson, so the "constant hazard 2R/q" is not shown. (That belongs to the native math review.)
2. **Integer non-collision is the wrong test.** Integer non-collision of ΔjD_s = Δj′D_t does not rule out coverage overlap mod q, or under negation (sum relations ≡ k_s + k_t). The right test is BL-style distinct-slope counting.
3. **Not priced:** the 0.906 optimum itself, finite-K behaviour, the interleaved comparator, and the memory price at matched bits.
4. **Scope:** this is a many-target constant factor only. It does not change the single-target baseline.

## Cheapest meaningful falsifier, on paper with no pilot

1. Recompute B and Γ independently. That is the native reviewer's job.
2. Write out the break-even inequality:
   0.094·C_x > 0.41·C_ins + 0.06·C_probe(bigger table) + memory price
3. Check it against one declared platform's C_ins, C_probe and C_x, both in a RAM-bound regime and with batched inserts.

If no declared platform satisfies it, or if the recomputed optimum is ≥ 0.95, park the card without simulating. Run an integer simulation only if the inequality holds on a declared platform, because only then can the result change the decision. I'm not accepting any coefficient.

**Status:** verified improvement is NONE, and the single-target baseline is unchanged.
