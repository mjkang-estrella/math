# R010 — Factor-count residues independent of prime-predecessor factor sizes

Date: 2026-10-08 (session date). **Accepted as the fourth substantial deduction under the stipulated pinned corpus.** The [complete proof](../iterations/i10-complex-prime-modes.md), with its [integration clarifications](../iterations/i10-complex-modes-proof-integration.md), passes [independent proof review](../reviews/i10-complex-prime-modes-r2.md). The separate [final prior-art and significance audit](../reviews/i10-complex-modes-novelty-r3.md) recommends acceptance as one nonroutine advance. The parent read both reports in full, reproduced the relevant checks and verified their source and artifact identities. Worldwide priority remains unverified.

## Exact theorem

Assume every applicable theorem in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` as instructed. Fix integers M>=1 and m>=3, a reduced residue b modulo M, a residue a modulo m, k>=1, and a continuous complex-valued function H on [0,1]^k. For each prime p>=3, let V_i(p) be the decreasing logarithms of the prime factors of p-1, counted with multiplicity, divided by log(p-1), and padded by zeros. Let (V_i) have the Poisson–Dirichlet PD(1) law. Then

\[
 \frac{1}{\pi(X;M,b)}
 \sum_{\substack{3\le p\le X\\p\equiv b\pmod M}}
 \mathbf 1_{\Omega(p-1)\equiv a\pmod m}
 H(V_1(p),\ldots,V_k(p))
 \longrightarrow \frac1m\,\mathbb E H(V_1,\ldots,V_k).
\]

The same limit holds on terminal dyadic intervals normalized by the number of primes in the fixed progression. Every displayed parameter is fixed before X tends to infinity. There is no claimed rate, growing-modulus uniformity, arbitrary-multiplicative-function theorem, or extra squarefree conditioning in this statement.

Thus the number of prime factors modulo any fixed m is asymptotically uniform and independent of every fixed continuous test of the ranked logarithmic factor sizes. Uniformity follows by taking H=1; the conditional PD law follows by dividing by the limiting residue probability 1/m. These are consequences of one theorem, not additional findings. The modes m=1 and m=2 are inherited from R006 and R008.

## Proof dependencies and the new bridge

The complete written argument linked above is the proof; the following explains its contribution and dependencies.

For each fixed nonreal root of unity z, the new analytic conclusion is prime-normalized cancellation of z^Omega(p-1) against every fixed nonempty interior prime-factor tuple statistic, in every fixed reduced progression. The ordinary Selberg–Delange principal density is nonzero for such z. Consequently the parity argument cannot be extended merely by replacing -1 with z: its zero-principal arbitrary-log bound would be false.

The argument constructs a single principal model on actual integer positions, using the full y-smooth part n_y for y=exp((log x)^.46). This model includes every retained term of the rough Selberg–Delange density expansion. It has exact covariance under multiplication by small-prime labels, matches the local Fourier and presieve progression principal terms, and satisfies

\[
 \|\mathcal B_x\|_\infty
 \ll_{z,N} (\log x)^{-.54(1-\Re z)}.
\]

A separate discrete high-time estimate and summed presieve argument control the residual. The model is independent of the active set used in the physical graph comparisons and combinatorial allocations. Reversing the entire signed allocation and coin expansion before taking absolute values leaves this common model multiplied by a retained-event probability in [0,1], inside a positive proxy of total mass O(x/log x). The total principal contribution is therefore o(x/log x), without a logarithmic loss that could overwhelm the saving for fixed roots close to one.

The resulting zero weak complex-measure limits are dominated by the unsigned PD measures. Endpoint control, size-biased sampling and the unseen-mass bound transfer them to ranked coordinates. Finite Fourier inversion then combines the nonreal modes with R006 and R008.

The pinned inputs are the prime-predecessor paper's physical graph, comparison, Mellin, long-prime/log-phase, sieve and allocation interfaces; the weighted dilation graph pairing; the primitive-root paper's coefficient transfer; and the September 30 quasi-Riemann-hypothesis zero-free region, with the principal pole retained. The two classical distribution inputs are the versioned de la Bretèche–Tenenbaum Selberg–Delange theorem and Granville–Shao centered progression theorem identified and checked in the proof package. Exact labels, ranges and immutable files are retained in its manifests.

The integrated proof retains four explicit conventions: use real nonnegative cutoffs for the positive sieve and extend by linearity; preserve the exact high-time scales rather than only their x^{1+o(1)} shorthand; use the actual convolution-inverse class hypothesis in Granville–Shao; and retain every signed allocation coefficient before applying the positive aggregate bound, whose constant may depend on the fixed presieve parameter.

## Significance and prior-art limits

The contribution is the common covariant principal model together with its compatible analytic estimates and final aggregate cancellation. Selberg–Delange expansions, phase replacement in Type II, Fourier inversion and probability sorting are inherited or standard ingredients, not independent novelty claims.

The final audit compares actual statements of the strongest pinned companions and fifteen primary PDFs, including published distribution theorems and current versioned preprints. It distinguishes the full joint fixed-shift conclusion from several close results:

- Ford's shifted-prime Kubilius model controls truncated small factors; its vanishing-error regime leaves a large-factor cofactor whose residue is not determined by that marginal.
- Timofeev's root-of-unity distribution inequality is not an equidistribution asymptotic. Its shifted-prime asymptotic requires a character-pretentiousness hypothesis not met by these nonreal modes. The present scalar specialization treats a concrete family within the remaining nonpretentious cancellation problem, not the whole conjecture.
- Gaussian factor-count limits do not control a fixed lattice residue. Ordinary-integer correlation theorems and growing shift averages do not by themselves isolate this prime-normalized fixed shift, much less its ranked-factor marks.
- R006 and R008 alone determine unsigned PD and parity, but not other cyclic modes. The final review gives explicit countermodels to those proposed logical implications.

No direct reduction to a stronger inspected theorem was found. The positive contribution judgment rests on the explicit nonzero-principal obstruction and its resolution, not on unsuccessful searches. A finite literature search cannot certify worldwide priority. No MathDB score or featured status is asserted.

## Validation and acceptance boundary

The independent proof audit gives PASS with no unresolved universal estimate. The parent read its full 326 lines, reproduced the exact diagnostics, and verified 90 unchanged inputs, 30 review artifacts, and 38 prior, 11 candidate and 14 fresh pinned-source identities. This integration was committed as `1b384f1`.

The independent significance audit recommends ACCEPT while preserving that proof verdict. The parent read its full 208 lines and reproduced its exact logical-reduction checks. The parent also verified all 101 sealed artifacts, 158 sealed dependencies, 36 freshly retrieved pinned files and sealed read ranges. The audit retains fifteen successful primary PDF retrievals and explicitly records inaccessible sources and version limitations. The [parent verification record](../experiments/i10-complex-modes-novelty-parent-verification.json) identifies the exact reviewed bytes.

These finite checks establish algebraic identities and provenance; they do not experimentally prove the asymptotic theorem. The accepted deduction rests on the complete proof, the source premises and independent reviews. There is no claim of independent validation of the stipulated corpus, worldwide first priority, human peer review or formal proof certification. No external publication or submission has been made.

**Parent decision:** accept this as one fourth substantial, nonroutine deduction under the stated premises and bounded novelty assessment. Historical candidate and draft status lines remain preserved; this record and TEN-FINDINGS.md govern current acceptance. The user's instruction is to pause research at this fourth finding after its separate commit, leaving the ten-finding objective incomplete and paused.
