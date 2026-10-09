# H039 hybrid prior-art review — raw Opus report

Unaccepted reviewer report. Root qualifications will be recorded separately.

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h039-hybrid-priorart-opus-20261008-r1`

Provider: claudeAgent / claude-opus-5-5. Completed.

I've finished the review. The opening survives, but only as a narrow, conditional and probably impractical window. It is not an improvement, and the work isn't novel. I made no edits, ran no code or experiments, and imported nothing. The numbers below are my own hand arithmetic, good to about three digits, and should be re-derived before anything is recorded.

## Sources actually read
I read these through `curl --fail -L … | pdftotext -layout - -`, with nothing saved.
- **Bernstein–Lange, "Two grumpy giants and a baby"** (`cr.yp.to/elliptic/grumpy-20120709.pdf`): abstract, §1, all of §2, the start of §3 (Brent–Pollard V and 1−Σp² heuristics), the start of §5, and all of §6. §§4–5 were mostly unread. The eprint 2012/294 copy returned 403.
- **Kuhn–Struik, SAC 2001** (`link.springer.com/content/pdf/10.1007/3-540-45537-X_17.pdf`): all of §4 (Theorem 1 and its proof), and §5.1 (Theorem 2, Corollary 1, Remarks 3–4). For §3 I only saw the headings.
- **Galbraith, *Mathematics of Public Key Cryptography* ch. 14 v2.0**: introduction, the opening of §14.2.2, and the passage around Exercises 14.2.17–14.2.22, including the Kuhn–Struik / Hitchcock et al. remark.
- **Galbraith–Wang–Zhang 2017** (the H019 URL): Table 3 with §2.2, the start of §3, §4.1–4.2 boundary, the end of §4 (the 0.404 block speedup, and parallel rho with the Montgomery trick at 0.53 → 0.47), and §§6–7.
- **Bernstein–Lange, cuberoot 2012**: §2 generic review, covering BSGS with the W=ℓ^{2/3} memory reduction, rho with distinguished points, and Pollard's kangaroo, where the wild walk checks every step against a stored trap.
- **Bernstein–Lange–Schwabe, negation 2011**: abstract and the start of §1 only. I used nothing quantitative from it.
- **Not read:** Hitchcock–Montague–Carter–Dawson 2004, Silverman–Stapleton, Bos–Kleinjung–Lenstra, Cheon–Hong–Kim. One extended web search found no source describing this exact blend. That is weak evidence, not a novelty search.

## Novelty qualification
Every component is known:
- Checking each walk step against stored known-log points is Pollard's kangaroo trap, as described in cuberoot §2.
- Known-log stored points plus walk self-collisions sharing one birthday urn is Kuhn–Struik §4 (credited there also to Silverman–Stapleton). Their next-log law is the random-table-size version of exp[−(t²+2bt)/q].
- The cheap progression table is GWZ §4 / H019, and a memory-capped static BSGS is cuberoot §2.
- In the generic model of grumpy-giants §2, the blend is just "baby line plus random slopes".

The only distinguishing feature is the cost asymmetry: babies cost c_b = 2.5M+S (x-only, H019), walk steps cost c_w = 5M+S, and the walk does a full lookup on every step under a memory cap below what BSGS wants. That supports at most "not found in the sources read". It is not a novelty claim. With GWZ's full-point blocks (3.5M+S) instead of x-only babies, the best gain at β=0.1 drops to about 2%.

## Arithmetic check (S=0.8M, so c_w=5.8, c_b=3.3, rho = 5.14 in M·√q)

| β | hybrid at P=0 | gain vs rho | static BSGS | largest P that still beats rho |
|---|---|---|---|---|
| 0.05 | 5.03 | 2.2% | ≫ | 0.13M |
| 0.10 | 4.94 | 3.9% | 8.58 | 0.25M |
| 0.19 | 4.83 | 6.1% | 4.97 | 0.43M (only 0.20M if it must also beat BSGS) |

- The hybrid loses to static BSGS for β ≳ 0.197. Its best point (β≈0.34, 4.76) loses to BSGS (3.54) and badly to interleaved signed block BSGS (about 0.943·3.3 ≈ 3.11).
- The whole window is therefore: memory capped at roughly 0.05–0.2·√q records, P below about 2–7% of c_w, and an ideal ceiling of about 6%.
- "Small β" is still Θ(√q) memory. For a 256-bit q that is around 2^125 records, so the window only physically exists at small q. A lookup cost P under 0.43M (less than one field multiplication, including the hash and a random memory probe) is a hardware premise with no supporting evidence. At sizes where the table leaves cache, it is implausible.

## Fixed-group amortized vs fully paid single target
- **Single target, fully paid:** the only regime with any opening, and only under a hard memory cap.
- **Amortized over a fixed group:** the hybrid is dominated. For large β, g(β) ≈ 1/(2β), so online cost per target is about (c_w+P)·q/(2b). Bernstein–Lange distinguished-point tables give about √(q/T) online for T stored records, because stored trails cover many points per record.
- **Batch of K targets:**
  - Hybrid total, minimised over table size: √(2·c_b·(c_w+P)·K·q) ≈ 6.19√(Kq) at P=0.
  - Shared-table BSGS: c_b·√(Kq) ≈ 3.3√(Kq).
  - Kuhn–Struik with negation, by my extrapolation: about 5.8√(Kq), with almost no memory.

  So no amortized claim should be admitted.

## Unpriced items (beyond self-collision detection memory and DP overhead)
- Distinguished-point detection delay of roughly (number of parallel walks)/θ, which batched inversion requires.
- Negation fruitless cycles also waste lookups.
- r-adding walk non-randomness (Brent–Pollard V; grumpy §§3–4) reduces only the t² self-collision term, so it must be matched on both sides.
- Fingerprint-compressed tables bring false positives, each costing a scalar-multiplication verification.
- Table construction, insertion and sorting.
- The ideal survival law treats table hits and self-collisions as independent; that is assumed, not proved.

## Strongest comparators
- **Below a cap of about 0.2√q:** batched negation rho at 0.886·(5M+S)·√q, matched on walk, distinguished points and fruitless-cycle handling.
- **Above the cap, or with no cap:** GWZ/H019 interleaved signed x-only block BSGS.
- **Amortized:** Bernstein–Lange precomputation (H015), and shared-table BSGS for batches.

## Falsifiable admission gate
Admission is root's decision. The H034 cap stays consumed, so a run would need fresh admission and must not reuse it.

1. **Freeze first:** the q range, a hard memory cap b = β√q with β ≤ 0.19, x-only babies, and one shared implementation, field library and machine.
2. **Measure P as a cheap first falsifier:** the incremental cost per walk step of the lookup (hash, probe, false-positive verification), with the walk, distinguished-point and negation handling identical on both sides. **Reject if P/c_w ≥ 0.07**, or if P exceeds P*(β) = [c_w(g0−g) − c_bβ]/g at the frozen β.
3. **Only if step 2 passes:** declared seeds, end-to-end mean cost per solved target including table build, distinguished points and cycles. The hybrid must beat both matched batched negation rho and capped signed block BSGS by more than the confidence-interval width at the same β.
4. **Reporting rule:** label any pass as a finite, capped-memory, single-target constant-factor result. Never call it an exponent or amortized gain.

The H038 Farey/height-lattice and H006 roles were not revisited, and the H034 cap was not touched.

Sources:
- [Two grumpy giants and a baby](https://cr.yp.to/elliptic/grumpy-20120709.pdf)
- [Kuhn–Struik SAC 2001](https://link.springer.com/content/pdf/10.1007/3-540-45537-X_17.pdf)
- [Galbraith ch. 14](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch14.pdf)
- [Galbraith–Wang–Zhang 2017](https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf)
- [Bernstein–Lange cuberoot](https://cr.yp.to/dlog/cuberoot-20120919.pdf)
- [Bernstein–Lange–Schwabe negation](https://cr.yp.to/elliptic/negation-20110102.pdf)
- [Kuhn–Struik bibtex](https://cr.yp.to/bib/2001/kuhn-rho.bibtex)
