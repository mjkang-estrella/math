# Sources, reading scope, and the exponent audit

Date: 2026-10-14. Pinned OpenAI mathematical corpus: revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (2026-10-08), recorded in `sources/upstream.json` (sha256 `3784eb61f1efa141ed49d00c5d13a5206502c4081759abff4f64c99183b5f30c`). Theorems in that revision may be used as true. Every statement used below was read. New deductions are in `proofs.md` and are not stipulated from I343 or I347.

## Campaign files

| File | sha256 |
| --- | --- |
| `proposal.md` | `ed4b9d8005c5ac357b62a237ba8ef3712d06625bbe6aa1e6229a97981053cbcc` |
| `proofs.md` | `86987fc0eb4b4534b6472a3378d4a0b2c12ae57dc6576ab56807e755d697c423` |
| `exponent_check.py` | `59c30f039095051fadc67068c1e2e6aca58262dd9816ba48e9a4a7183f3d5196` |

`exponent_check.py` is an arithmetic check of the majorants in `proofs.md`. It samples no clauses and is not evidence for a central limit theorem. The run recorded below exited 0.

## Local inputs, hashed in this pass

I347, all matching the files read or cited:

| File | sha256 |
| --- | --- |
| `frontier/iterations/i347-sat-quadratic-variation.md` | `5797930bde786a28b2b88bd0d27f60693291300d3365181c6f27b9a2875f3790` |
| `frontier/iterations/iteration347-sat-quadratic-variation-brief.md` | `17180f3fafccb27e2db5b6120df7d2d6d83b980248d98f476ae5742432e2d114` |
| `frontier/experiments/i347_sat_quadratic_variation/analysis.md` | `99f1221cec0211262408ca16efb9c1fcf5eb37cd8e7807b8259d1a9932573b73` |
| `frontier/experiments/i347_sat_quadratic_variation/reading-and-failures.md` | `ef623372b9e2a6752317be2fa477f7611a7a2e0ec0d86cd001511b436a449683` |
| `frontier/experiments/i347_sat_quadratic_variation/input-authentication.json` | `e78758bbd001e03177451639be5dc4fa85f4c1312223226f2d647aa4b546f760` |
| `frontier/sources/i347_sat_quadratic_variation/literature.md` | `27d37f030c667f5660a4884edf6b9b39de75ef19add4156b020ce3ef03bc5140` |

The five detached I343 hashes in the I347 brief match the files on disk:

| I343 file | sha256 |
| --- | --- |
| iteration | `f052aa073aaebd122563a9807c9da9be6ef28b5c8f12295cd20f33835c57b56b` |
| analysis | `226d3441b5b7575f09f8160bae96fff5c5cafbf1b573fc3085432f0bb7052f36` |
| reading | `c94ef724d38ed43c5911e9427f372634ca3716245c75d5e3e1fbc15cd10a4669` |
| authentication | `0c2977d8b7944f1b07e9a6728166e2811f5fa7e7a6764b938a4816bb88613500` |
| literature | `e058109ae0ef49f3c881b10308c481337180eba7ffb1c0ecd65f0749cf3e74d4` |

R022 finding file sha256 `21d9c3b94b1c0560fc93585bd80d9f5b8eadc159de644c0df1f7b80059b2f8cc`. Statements (S) and (P) were read. They concern bounded functions on the cube with bit noise. No random clause process appears. There is no overlap with (R), with identity (6.2), or with a hitting-time CLT.

## What was read for the new argument

- I347 `analysis.md`, Sections 1–4 and 6–8, including the deletion-moment proof (2.1)–(2.11), the posterior identity (6.2)–(6.3), and targets (G1) and (G2). The comparisons (2.8) and the \(v=k-1\) summand were recomputed and agree with that text. The cooperative-killing witness was not reopened and is not used.
- I347 `literature.md`, in full. It records Major’s conditions (1.2)–(1.3) and Chatterjee’s Theorem 2.2 as already narrowed: the cubic term is paid, the kernel variance is not.
- Pinned `preprints/Variance-of-the-Random-k-SAT-Hitting-Time-September-27-2026/build/source/sections/introduction.tex`, fetched from the pinned revision in this pass. Theorem `thm:variance` and display `eq:intro-first-moment` are the variance input and the first-moment tail. The introduction states a finite-size centering and does not state a Gaussian limit. Carenini’s \(O(n^{1+2/k})\) variance and \(O(n^{1/2+1/k})\) window are cited there as coarser bounds. No Carenini theorem is used.
- Péter Major, *Central limit theorems for martingales*, notes at `https://www.renyi.hu/~major/probability/martingale.pdf`. Local PDF sha256 `f643baf42a28ba5c56afd2b340217cba9fa6522fadfbf6fcf4c570dfc5a4af7e`. Pages 1–3 were extracted. The martingale-difference theorem requires (a) the difference property, (b) stochastic convergence of the sum of conditional variances (1.2), and (c) conditional Lindeberg (1.3). Brown, *Ann. Math. Statist.* 42 (1971) 59–66, is the source Major modifies. Brown’s article was not re-read in this pass. The publisher page was previously iframe-only.

## What was not read in this pass

- Chatterjee, arXiv:math/0611213. A previous HTML fetch returned no theorem text. The criterion is cited only as I347 already recorded it. This campaign does not improve that kernel.
- Wilson, arXiv:math/0005136, beyond the pinned introduction’s use of Corollary 4 as the variance lower bound. No bystander estimate is a lemma here.
- Carenini’s papers, beyond the pinned introduction’s summary. No Carenini bound is used.
- The deletion and occupation source files of the k-SAT variance paper, in this writing pass. The moment input is I347’s general-\(k\) writeup, which was read.
- I343 `reading-and-failures.md` and `input-authentication.json`, line by line. Their hashes match the brief. The moment consequences used here are those rederived in I347 Section 2.

## Exponent audit

Command: `python3 exponent_check.py` in this directory. Exit status 0. Final line: `exponent checks passed`.

Selected rows of the unit-constant majorant. `post_eta` is the power of \(n\) in \(n(\mathbb E|S|^4)^{1/2}\) under the \(r\)-moment Markov bound. `fourth_only_post` is the same power if the tail is controlled only by the fourth moment.

| \(k\) | \(r\) | \(\theta\) | post \(\eta\) | far \(\eta\) | fourth-moment-only post |
| --- | --- | --- | --- | --- | --- |
| 6 | 5 | 0.2000 | 2.2500 | 1.7500 | 2.3000 |
| 7 | 6 | 0.3333 | 2.0000 | 1.5000 | 2.1667 |
| 8 | 7 | 0.4286 | 1.7500 | 1.5000 | 2.0714 |
| 9 | 8 | 0.5000 | 1.7500 | 1.5000 | 2.0000 |
| 10 | 9 | 0.5556 | 1.7500 | 1.5000 | 1.9444 |
| 17 | 16 | 0.7500 | 1.7500 | 1.5000 | 1.7500 |

The \(k=10\) fourth-moment-only value is \(35/18\). The script checks \(\eta<2\) for every \(k\) from 8 through 30, \(\eta=2\) at \(k=7\), and \(\eta=9/4\) at \(k=6\).

The ratio \((\ln n)^3 n^{-1/4}\) was \(8.34\times 10^{1}\) at \(n=10^6\), \(2.11\times 10^{1}\) at \(n=10^{12}\), and \(1.69\times 10^{-1}\) at \(n=10^{24}\). At \(n=10^{24}\) the \(k=7\) far majorant still has ratio \(1\), while the \(k=8\) window ratio has fallen below 1 and continues to fall at \(n=10^{30}\) and \(n=10^{36}\). These numbers audit the powers. They are not SAT fluctuations.
