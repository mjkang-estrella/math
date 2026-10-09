# Parent integration check for arithmetic round 3

Date: 2026-10-08. **AP, RC, and A+ remain unaccepted candidates.** This note records the parent's preliminary checks; the fresh independent analytic proof review is pending. The original author report is preserved byte-for-byte for that review.

## Reproduced evidence

All 59 inherited manuscripts plus the separately fetched pinned PD bibliography match their SHA-256 and Git-blob hashes and the immutable preprint tree: **60 pinned files**. Five external primary-source downloads match their recorded SHA-256 hashes. The author's “65 source hashes” total therefore comprises 60 pinned manuscript files and five literature downloads, not 65 upstream manuscripts.

The original experiment reproduces byte-for-byte, including 833,272 exact residue identities (243,782 with nonunit source residue), 63 rational convolution checks, 1,392 Fourier identity checks, 189 admissible signed bases and 18,488 quadratic-class prime instances. Fourier error is about 4.07e−13; those checks are floating-point transcription checks. All recorded author input and artifact hashes matched before parent integration. [Machine-readable verification](parent-verification.json).

These computations do not establish the analytic lemma, prime asymptotics, or literature novelty.

## Read source contracts and preliminary assessment

The parent read the actual pinned D `06-correlations.tex` statements `prop:graph-transfer` and `prop:ideal-family`, the physical endpoint bounds, insertion separation, stripping normalization and collision estimates, the comparison multiplier and local Mellin-energy setup, and the first-endpoint low-frequency calculation. It also read P's `lem:marked-coefficient-transfer` and `alg:quadratic-progression`.

The general pairing statement requires independence from selected marks, not independence from integer position. Multiplication by a position-residue indicator preserves that requirement and the stated norm bounds. The stripping formulas expressly give n=D_R w, D=D_R D_C and cutoff Ψ(w/(xD_C)); the comparison kernels exclude shared labels. These observations support the proposed interface but do not independently certify every subsequent estimate or the extraction argument.

The exact new finite identity is correct: for a unit d modulo M, the two conditions tw=r and t(w+d)=r+1 force t=d⁻¹, and then w=rd. Averaging over units gives φ(M)⁻¹1_(w=rd). It does not divide by r or w and includes nonunit predecessor residues. Recovering this average from shared prime labels still requires the full-interval mixing, collision, and uniform-error arguments in the proposed lemma.

The Fourier identity for a residue restriction is also correct, and the source permits arbitrary fixed logarithmic precision. The fresh review must check its use with enlarged rational denominators and time windows, all dependence on free labels, the order of analytic parameter choices, and every extraction error under the external residue restriction. No final proof verdict is issued here.

## Primary-source and MathDB correction

The parent independently opened [Bharadwaj–Rodgers v4](https://arxiv.org/html/2402.11884v4), whose Theorem 7 requires level-one well-distribution, and [Moree v1](https://arxiv.org/pdf/0707.3062v1), whose Theorem 1 states the GRH-conditional progression asymptotic. These do not establish the candidate from the currently accepted premises by themselves. This is a targeted source check, not an exhaustive priority search.

**Correction to the author's §9 MathDB sentence:** the [page retrieved by the parent](https://mathdb.com/p/370026/artin-s-primitive-root-conjecture) states the infinitude formulation, describes classical results and unverified 2026 claims, and marks its progress summary as of August 2026. It does **not** contain the claimed summary of the accepted OpenAI corpus's x/log²x result. Do not cite that page for the corpus comparison. The relevant pinned P introduction is the source for that comparison. The page provides no freshly verified “Celebrated” badge or numerical rank in this reading.

The stronger target is precise regardless of that metadata: upgrade the accepted per-base x/log²x count to a positive lower proportion x/log x with index exactly one. Even if the candidate passes, it would not establish existence or the predicted value of the natural density. Its conditional scope remains the user's accepted-corpus premise.

## Disposition

Preserve the candidate and verification as a research record, without creating an accepted finding or increasing the success count. The full original brief, prior corrections and objections, and the fresh review task ID are in [the round-4 receipt](../../iterations/iteration3-arithmetic-progressions-r4-task.json). Incorporate that verdict before considering acceptance.
