# H033 primary-literature reviewer report

UNREVIEWED reviewer report; root acceptance/corrections recorded separately.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h033-primary-algorithms-opus-20261008-r1
Provider/model: claudeAgent / claude-opus-5-5. COMPLETED, no pending children.

I found no recent primary paper that changes the classical baseline for full-range, prime-order, ordinary prime-field ECDLP. Best supported work is still the generic square-root reference with known negation/automorphism constants, and verified improvement is **NONE**. Five newly screened classical claims all fail or fall outside scope. The search was bounded, so this is not a proof that no such result exists.

Constraints were respected: no repo edits, no experiment modules, no numerical runs, no children, no commits. Downloaded PDFs are only in `/tmp/h033lit`, outside the repo.

## How sources were accessed
- **Accessed directly:**
  - arXiv API listing for "discrete logarithm" + elliptic, newest first, 60 entries back to 2019.
  - ePrint search pages (submitted after 2024-06-01) for: ECDLP, Pollard rho, kangaroo, summation polynomial, point decomposition, index calculus elliptic, baby-step giant-step, elliptic curve discrete logarithm.
  - Several broader web searches on summation polynomials, rho/kangaroo constants, ML attacks, records and journal venues.
- **ePrint PDFs returned 403** to both curl and WebFetch. I read Wayback snapshots of 2024/1923, 2025/015, 2026/2102 and 2024/1321 instead. Those snapshots may not be the latest revision; 2025/015 was revised 2025-09-02.
- **Mage** (arXiv 2512.12483): read via the arXiv abstract plus a WebFetch summary of the v3 HTML.
- **ePrint 2026/1976, 2026/1299, 2024/1330:** abstract or landing page only.
- **Already scoped in the repo, not repeated:** Mahalanobis 2607.09814 and the minors line (including 2005.05039), Arif–Imran, Gupta, Lin et al. (ICN 2026), Alman–Vassilevska Williams 3SUM, Stange and Bhakta, Trimoska et al., Neamah 1607.05901, Petit et al. 2016 (PKM), Amadori et al., Semaev, Huang et al. 2020 (quasi-subfield), Delaplace–May.

## Screened mechanisms

**1. Hu, ePrint 2024/1923, "pseudo-index calculus" — rejected.**
- **Input family:** any curve over F_p with a group of order N. Factor base U = {±iP : i prime ≤ r}, with r = exp(√(ln p · ln ln p)). It tries prime multipliers s until Q, Q+sP or a related point lands in U.
- **Claim:** none favourable. The author says it is "extremely inefficient": per-trial success is about 2r/N, worst case O(p/ln p).
- **Baseline:** this is a baby-step table limited to primes. Expected work is about N/(2r) scalar operations, which loses to rho unless r ≥ √N, and at that point it is just BSGS.
- **Hidden costs:** each trial needs a scalar multiplication, and no relations or linear algebra are actually used.
- **Unresolved:** the paper's §VI says Semaev's S3 is wrong, citing "2P+3P+23P=O" with x = 2, 3, 18 in a group of order 1019. As printed, 28 ≢ 0 mod 1019, so the counterexample is internally inconsistent.
- **Cheapest check:** substitute three points with P1+P2+P3 = O on the paper's stated curve into the standard S3, by paper arithmetic. This needs root approval, since I ran no numbers.

**2. Hu, ePrint 2025/015, IICA "integer up/down" — out of scope.**
- **Input family:** Z_p^* only (the setup in §2 is p prime with N = p−1). It claims about a 2× better success probability for finite-field index calculus.
- **No bridge to elliptic curves is given.** The abstract's line about ECC systems is not backed by any elliptic-curve algorithm in the text.
- **Cheapest check:** none needed for our problem. The prime-field DLP claim would need its own audit.

**3. Cenk–ElSheikh–Paksoy–Hasan, ePrint 2026/2102, windowed-batch BSGS — known techniques, bounded range only.**
- **Input family:** plaintexts m < 2^ℓ with ℓ ≤ 64. A bounded secret range is excluded from our challenge.
- **Mechanism:** Jacobian giant steps, Montgomery batch inversion over a window W, and a co-Z add/subtract for the signed range.
- **Paper's costs:** about 2^ℓ₂·(12M+4S) + I/W per step; co-Z gives 15M+4S per pair of steps. It reports up to 2.3× over FastECDLP at 54–58 bits.
- **Transfer to full range:** this is a single-stream memory optimisation. My expectation, from recollection and not verified in this source, is that W interleaved affine streams with batched inversion cost about 5M+1S + I/W per step, which is cheaper than 12M+4S. Full-range BSGS is also dominated by its √q table.
- **Cheapest check:** a paper-only per-step comparison of the W-window Jacobian loop against multi-stream batched affine, charging each stream's initial scalar multiplication.

**4. Talotti–Paier–Miculan, ePrint 2024/1321 (ITASEC 2024), weak keys in small subgroups — secret-structure class, rejected.**
- **Input family:** keys k lying in small subgroups of the multiplicative group of scalars mod the group order (the paper writes Z_p^*). Implicit BSGS runs over the d-order subgroup in about √d steps.
- **Their own secp192r1 figures:** about 2^109.0 weak keys, testable in about 2^55.6 group operations. For a uniform key the success probability is about 2^−83. That gives roughly 2^138.6 group operations per expected success, far above the generic ~2^96. This is arithmetic on their reported numbers, not a new run.
- **Status:** structured-key detection, essentially secret-range narrowing. No full-range transfer.

**5. Mage, arXiv 2512.12483 (transformer "cracking" of secp256r1) — no algorithm.**
- **Result:** about 99% training accuracy, which is memorisation. Held-out per-byte accuracy was about 0.0042 against chance 1/256 ≈ 0.0039, with no significance test, and eval loss rose during training. The headline break claims are extrapolations, not measurements.
- **Cheapest check:** none needed; the paper's own held-out numbers already refute any generalisation claim.

## Excluded after a short look
- **ePrint 2024/1330** (Feng–Luo–Chen–Nitaj–Pan, CRYPTO 2025): the landing page now resolves the earlier H013/H015 access gap at abstract level. It is a provable tool for asymptotic Coppersmith small-root bounds, not an ECDLP algorithm. Its theorem has still not been read.
- **ePrint 2026/1976** (Shirase, "Me operation"): a different, non-associative problem. The abstract gives no ECDLP reduction.
- **ePrint 2026/1299** (Dryło): compression-function arithmetic. G-compressions need a K-rational kernel G, which a prime-order curve lacks except trivially. Abstract only.
- **ePrint 2026/1823** (HyperSolver): supersingular isogeny path-finding; judged from the title only.
- **Quantum resource papers:** 2607.13816, 2606.02235/2026/1128, 2026/280, 2026/2014, 2609.05625 and others were excluded by brief.
- **No 2024–2026 source** found improving the one-dimensional rho or kangaroo constants. Mukhopadhyay 2023/160 is multi-dimensional Gaudry–Schost.

## Wave report
- **Best supported complexity:** generic square-root with known negation/automorphism constants; unchanged.
- **Verified improvement:** NONE.
- **Hypothesis tested:** that recent primary literature contains a classical large-characteristic ECDLP claim that changes the work assessment. None found in this coverage.
- **Evidence:** five claims rejected or out of scope for the reasons above. Evidence quality is limited: three papers were read only through archive snapshots, three only at abstract level, and the search was bounded.
- **Next options for root:**
  - If constants matter, do the paper-only per-step cost comparison for item 3 against the repo's existing batched-affine baseline.
  - Optionally record the ePrint 403 access workaround and the 2024/1330 scope correction.
  - Otherwise nothing here justifies an experiment.

Sources: [ePrint 2024/1923](https://eprint.iacr.org/2024/1923), [ePrint 2025/015](https://eprint.iacr.org/2025/015), [ePrint 2026/2102](https://eprint.iacr.org/2026/2102), [ePrint 2024/1321](https://eprint.iacr.org/2024/1321), [arXiv 2512.12483](https://arxiv.org/abs/2512.12483), [ePrint 2024/1330](https://eprint.iacr.org/2024/1330), [ePrint 2026/1976](https://eprint.iacr.org/2026/1976), [ePrint 2026/1299](https://eprint.iacr.org/2026/1299), [ePrint 2023/160](https://eprint.iacr.org/2023/160), [arXiv 1607.05901](https://arxiv.org/abs/1607.05901), [Wang–Zhang 2012](https://emis.univie.ac.at/journals/HOA/JAM/Volume2012/635909.pdf), [arXiv 2607.13816](https://arxiv.org/abs/2607.13816), [arXiv 2508.14011](https://arxiv.org/pdf/2508.14011), [ePrint 2017/609](https://eprint.iacr.org/2017/609.pdf), [PKM16](https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf)
