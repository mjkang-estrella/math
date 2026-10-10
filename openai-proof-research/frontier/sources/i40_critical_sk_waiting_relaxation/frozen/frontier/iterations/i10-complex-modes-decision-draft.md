# Complex prime-predecessor modes — decision record prepared for final review

**Not accepted.** The independent proof audit passes under the stipulated corpus, and its four integration clarifications are retained. Final prior-art/significance review is still running. This draft assigns no finding number and does not change the accepted count of three. It may be promoted only after the parent reads and verifies that separate review, resolves any objections, and makes a separate finding commit.

## Exact candidate theorem

Fix integers M>=1 and m>=3, a reduced residue b modulo M, a residue a modulo m, k>=1, and a continuous complex-valued function H on [0,1]^k. For a prime p>=3, let V_i(p) be the decreasing logarithms of the prime factors of p-1, counted with multiplicity and divided by log(p-1), padded by zeros. Let (V_i) have the Poisson–Dirichlet PD(1) law. The proposed conclusion is

    (1/pi(X;M,b)) sum_{3<=p<=X, p=b mod M}
        1_{Omega(p-1)=a mod m} H(V_1(p),...,V_k(p))
      -> (1/m) E H(V_1,...,V_k).

It also holds on terminal dyadic intervals normalized by the number of primes in the fixed class. All displayed parameters are fixed before X tends to infinity. There is no rate, growing-modulus assertion, arbitrary-multiplicative-function theorem, or additional squarefree conditioning in this candidate's stated theorem.

The interpretation is joint asymptotic independence of the number of prime factors modulo a fixed integer from every fixed continuous test of their ranked logarithmic sizes. The m=1 and m=2 cases are already R006 and R008. The new content would be the nonreal Fourier modes, not a second count for Fourier inversion or probability bookkeeping.

## Proof package and the claimed new argument

The complete argument is [the 856-line candidate](i10-complex-prime-modes.md), read together with [the independent audit](../reviews/i10-complex-prime-modes-r2.md) and [the integration clarifications](i10-complex-modes-proof-integration.md). This decision record is not a replacement for those proofs.

For a fixed nonreal root of unity z, the analytic target is cancellation of z^Omega(p-1) against every fixed nonempty interior prime-factor tuple statistic, at scale o(x/log x). The nonzero ordinary Selberg–Delange principal density prevents simply replacing the parity sign in R008 by z.

The proposed bridge constructs one principal model on actual integer positions, using every prime at most y=exp((log x)^.46) in the smooth part. It has exact covariance under multiplication by the physical small-prime labels, agrees with the relevant principal progression terms including their lower-order density coefficients, and has uniform size O((log x)^(-.54(1-Re z))). A separate discrete high-time argument and summed presieve estimates control the residual. The model is common to all active sets. Reversing the signed coin expansion and allocation before taking absolute values turns the total model contribution into a bounded retained-event probability times a positive proxy of mass O(x/log x). This avoids amplifying the small model by the many signed patterns.

The proof then obtains zero weak complex-measure limits using unsigned PD domination and endpoint control. Sorting finitely many size-biased draws and bounding the unseen mass transfers the limit to ranked coordinates. Finite Fourier inversion combines these nonreal modes with R006 and R008.

All applicable OpenAI premises are stipulated true at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The source contracts include the prime-predecessor paper's physical graph, comparison, Mellin, long-prime/log-phase, sieve and allocation interfaces; the weighted dilation graph pairing; the primitive-root paper's coefficient transfer; and the September 30 quasi-Riemann-hypothesis zero-free region with the principal pole retained. The classical inputs are the versioned de la Bretèche–Tenenbaum Selberg–Delange theorem and Granville–Shao centered progression theorem identified and checked in the proof package.

## Completed validation

Independent proof verdict: PASS under these premises, with no unresolved universal estimate. The parent read the complete audit and retained its explicit nonnegative-cutoff convention, high-time scale definitions, convolution-inverse hypothesis and full signed allocation identity.

Parent verification in commit `1b384f1` reproduced the finite algebra diagnostics and checked 90 unchanged input hashes, 30 review artifacts, and the 38 prior, 11 candidate and 14 freshly retrieved source identities. The diagnostics cover nonunit congruences and extra valuations, Ramanujan invariance, density coefficients, roughness envelopes, smooth-part covariance, and signed allocation. They do not prove the asymptotic theorem; that conclusion depends on the complete written argument and source-contract review.

## Pending decision gate and stop condition

The separate [final significance task](iteration10-complex-modes-novelty-r3-task.json) must compare the precise joint law and its analytic bridge against the strongest source companions and primary literature. Unmarked equidistribution or an Erdos–Kac marginal does not automatically establish the joint PD statement; conversely, lack of a matching search result is not evidence of novelty. A review may still demote the work as a routine transfer even if the mathematics is correct.

Before promotion the parent must read the entire final report, inspect all material distinctions and caveats, reproduce its relevant checks, and verify immutable source and artifact identities. Only a favorable contribution decision supports the fourth count. Worldwide priority, human peer review and formal proof certification must remain explicitly unclaimed.

If this candidate is accepted as finding four, the user's instruction is to pause immediately after its separate commit. Preserve and halt remaining delegated work, record exact task identifiers and artifact status for resumption, and set the ten-finding goal to paused. If it is demoted, it does not satisfy that milestone.
