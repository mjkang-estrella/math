# H034 windowed-source cost report

UNREVIEWED report. Broad finite/peak-memory dominance and proposed regrouping
require separate checking; not automatically accepted by root.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h034-windowed-source-cost-opus-20261008-r1
Provider/model: claudeAgent / claude-opus-5-5. COMPLETED, no pending children.

I read the paper end to end, including Appendices A and B, and found nothing that survives. None of the paper's published variants beats the existing H019/GWZ schedule on field-operation count in any regime where the two get the same working memory. So it gives no full-range ECDLP improvement, the 1/2 exponent is unchanged, and verified improvement stays NONE.

I made no edits, ran no experiments, imported no experiment modules, launched no children and made no commits. I read RESEARCH_LOOP.md, RESEARCH_TEAM.md, research/STATE.md, H033-primary-audit-corrections.md, H019-xonly-baseline-screen.md and the full archived text `/tmp/h033lit/c.txt`. Its SHA256 matches the hash you gave. That text is the only revision I checked. All costs below are operation counts from the paper or worked out by me (labelled). None of them is a clock time.

## 1. What the paper says, re-derived per lookup key

Notation: s = S/M (squaring cost over multiplication cost), r = I/M (inversion cost over multiplication cost), W = window size, L = one lookup. The "exact" column keeps the batch-inversion correction of −3/W or −1/W per pair.

| Variant | Paper's display | Per key, exact (my derivation) | Status |
|---|---|---|---|
| Alg 7, unsigned windowed (pp. 8–9) | 12M+4S+I/W+L | 12−3/W+4s+r/W | measured ("+Windowed") |
| Alg 10, signed co-Z, JacAffADDSUB 15M+4S (pp. 10–11) | 20M+5S+I/W+2L per pair | (20−3/W+5s+r/W)/2 | measured ("+Co-Z") |
| Alg 13, ZADDC (6M+3S) + JacAffADDUPDATE (10M+3S) (App. A) | 21M+7S+I/W per pair, 2L left out | (21−3/W+7s+r/W)/2 | not in the result tables |
| Alg 15, ZADDU (5M+2S) + BatchInversionChain (App. B) | 14M+4S+2I/W+2L per two keys | 7−1/W+2s+(r+s)/W | **not implemented** ("underway") |
| Alg 16, ZADDSUBU (claimed 11M+3S) + chain (App. B) | 14M+3S+I/W+2L per pair | (14−1/W+3s+(r+s)/W)/2 as claimed | **not implemented**; formula not shown |

Your correction holds. The 15M+4S pair kernel leaves out normalization and lookup. The full figures are 20M+5S+I/W+2L per pair (signed) and 12M+4S+I/W+L per key (unsigned).

**Problems I found in the paper:**
- **The 11M+3S figure for ZADDSUBU is unsupported.** The paper never writes the formula out. Adapting its own Alg 9 to co-Z in the obvious way drops U and V (−3M−1S) but has to rescale Y_S (+1M). That gives 13M+3S, so 8M+1.5S per key rather than 7M+1.5S. The conclusion below holds even if I accept 11M+3S.
- **The inversion chain is correct but not new.** Z_j = Z_{j−1}·H_j gives (Z_{j−1}⁻¹)² = (Z_j⁻¹)²·H_j². It only works because each walk adds a fixed step. It cannot be used in rho or kangaroo walks, where the next step depends on the point's affine x-coordinate, so the inversion cannot be deferred.
- Alg 15 and Alg 16 print the old and new lines side by side, so they read ambiguously. The cost analysis treats the new lines as replacements.
- Section 5 says the zaddc variant "computes a different pair of outputs". Appendix A says it outputs Pm±jS directly. The two don't agree, and no zaddc numbers are reported.
- The Alg 6 input gives the baby range as i ∈ [1, 2^{ℓ1−1}), which would miss scalars where r = M/2. Section 2.5 and Alg 4 give [1, M/2]. This is probably a typo, but any reimplementation must include M/2.
- **The "O(W) ≈ 50 KB" memory figure leaves out the baby table**, which takes 5.58 GB at ℓ1 = 30. This is not low-memory ECDLP.

## 2. Comparison with H019/GWZ under the same table, order and stopping rule

Hold the baby table, giant index order, signed coverage and stopping rule fixed, and swap only the generator for giant keys. The accepted H019 per-key cost factors as:

  Cx(k,ℓ) = s + ((ℓ+1)/(2ℓ+1))·(5 + (r−3)/k)

This decreases in ℓ, with infimum 2.5 + s + (r−3)/(2k).

**Cost inequality.** Paper variant V reduces matched complete work by a fraction δ only if

  N_g·[c_V(W) − Cx(k,ℓ)] + Δsetup + Δwaste < −δ·W_total

for every (k, ℓ) that H019 may use under the same working-memory budget. Here N_g is the number of giant keys, Δsetup and Δwaste are the setup and stopping-waste differences, and W_total is the complete matched work including baby build, lookups and verification.

- **Setup.** The paper needs about one scalar multiplication. H019 needs O(k) center initializations plus ℓ offsets, and the offsets don't depend on the target.
- **Stopping waste.** Up to T·W pairs for the paper versus up to k(2ℓ+1) keys for H019.
- **Inversion overhead.** ⌈N_g/(κW)⌉·I for the paper versus the inversion term already inside Cx.
- All three are O(block) and vanish against N_g ≈ √q. The leading condition is therefore c_V(W) < Cx(k, ℓ).

**Even the paper's best case loses.** Take Alg 16 with its own claimed 11M+3S. It wins only if

  k < (r−3) / (9 + s + (r+s−1)/W),

that is, only if H019 is held below about (r−3)/(9+s) parallel centers.

**Matched memory removes that regime.**
- An H019 center needs X, Y and a prefix product: 3 field elements.
- A paper window pair needs Xadd, Xsub and H² (or Z): also 3 field elements.
- The ℓ offsets are shared across targets.
- With k = W, H019 is cheaper for any realistic W.

In the limit the paper's best is 7M+1.5S (as claimed) to 10M+2.5S (as measured) per key, against 2.5M+S for H019.

There is a further sharpening, which is my simple implication and not yet reviewed. Fold each center's advance denominator into the same Montgomery batch as its ℓ side denominators. Even a single sequential stream (k = 1) then costs s + (5ℓ+2+r)/(2ℓ+1) per key. At equal memory (ℓ = W) this beats every paper variant for every W ≥ 1. Root should check this before relying on it. The conclusion does not need it.

**Coverage, early stopping and batch storage** are neutral. Both sides use the negation map. A contiguous T-way split with a shared stop flag gives an expected total of N/2, the same as one sequential walk.

**At the algorithm level**, single-target non-interleaved BSGS averages about 1.0√q keys (best B = √q/2) against GWZ's interleaved 0.943√q. That gap is known and not specific to this paper.

## 3. Prior art and unsupported assumptions

**Known techniques (none is a new attack):**
- Montgomery simultaneous inversion.
- Tang et al.'s FastECDLP. Its search phase over a stored giant table is already 2.5M+S per key.
- The GWZ 2017 block generation that H019 is built on. The paper cites GWZ only for point symmetry.
- From memory, not re-checked now: Meloni's co-Z ZADDU; Goundar–Joye–Miyaji ZADDC (the paper cites it as [17]); Longa–Miri and Dahmen–Okeya–Schepers, which turn co-Z chains into affine points with a single inversion; Bernstein–Lange's small-DL tables for multi-target amortization.

**Paper-wide limits:**
- **Appendix B is projection only.** Its "40%" and "32%" improvements are operation counts, not measurements.

**Simple implication (operation counts only, not a clock claim):**
- In the paper's own AHE setting, a GWZ/H019-style generator with O(ℓ) offset points would also remove the stored giant table, at about 2.5M+S per key. That looks better than the paper's variants by a factor of 2.4 to 3.6 in operation count. It does not show anything about clock time, and it is not an ECDLP improvement.

**Unsupported assumptions, any one of which a "gain" would need:**
- A hardware limit that caps parallel affine centers or shared offsets below about r/(9+s) while still allowing a W-long window. This is unproven and needs measurement.
- That Alg 15 or Alg 16 actually achieve their displayed counts. They are not implemented, and ZADDSUBU is not written out.
- Carrying the bounded-plaintext features over to full range. Proposition 1 depends on a bounded sum, and range hints and divisibility narrow the secret's range. Both are excluded under RESEARCH_LOOP.

## 4. Did any gain survive?

**None.** No published variant (Alg 7/10/13/15/16) materially reduces matched full-range complete work in the operation-count model. It is not just that there is no benefit: each variant costs more per key than the accepted baseline.

**Cheapest conclusive check (not run):**
1. **Zero cost, on paper.** Have root, or one independent reviewer, verify the Cx factorization, the ZADDSUBU count, and optionally the regrouped batch. That settles the operation-count verdict, which already holds under the paper's own optimistic 11M+3S.
2. **Only if a clock-level claim matters.** Run a same-library, single-thread comparison of Alg 10 against the H019 giant generator, emitting the same index-ordered stream of x-keys. Cross-check both streams against a reference and instrument the operation counts. Report only the measured time ratio on that machine. It would change nothing for ECDLP unless the paper's generator came out at least 2.4× faster than its operation counts predict.

The ordinary full-range reference is unchanged: square-root work with known constants and tradeoffs.
