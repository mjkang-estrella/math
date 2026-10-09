# Parent preliminary review — full parity candidate

Date: 2026-10-08. Status: candidate only; fresh independent proof audit pending.

The report proposes full Liouville cancellation on prime predecessors, jointly with their ranked-factor PD(1) law, in every fixed reduced progression. This would strengthen the accepted band's parity/infinitude result. It is not yet an accepted second substantial finding.

The parent reproduced `experiments/i05_parity_pd/check.py`. The complete result matches the author's output, including its finite prime screen, byte-for-byte against the artifact manifest. All 81 recorded artifacts match; the 60 upstream files match their SHA-256 hashes, Git blob hashes and complete pinned tree entries; six successful external downloads match. The sole changed input is the shared iteration index, updated during the intervening joint-Artin integration. R006 inputs are unchanged. See `parent-verification.json`. These checks establish neither analytic cancellation nor novelty.

Source-contract spot checks support the proposed mechanism:

- D `03-determinant.tex`, lines 70–115, and P `08-type-ii.tex`, lines 125–149, put the invariant predecessor factor outside a Cauchy square. Replacing it with full Liouville times the invariant factor introduces the fixed sign for the selected primes and a modulus-one factor of the remaining variable; that factor disappears in this particular square. This does not license twisting the scalar coefficient discrepancy by Liouville.
- D `06-correlations.tex`, lines 807–858, proves the sparse bound using an unweighted Gram kernel and the coefficient square norm, followed by a separate long-prime saving. The proposed signed residual coefficient is compatible with this norm calculation if its decomposition and scale conditions are justified. The signed low-time estimate and full extraction still need independent checking.
- D's long-prime appendix requires a prime-slot scale bounded between fixed positive powers of x, a logarithmic lower frequency threshold, and upper frequency x². These ranges must survive every decomposition; the candidate explicitly retains a nonempty long-prime tuple.

The parent also opened the actual primary classical sources. [Pintz, equation (1.5), page 2](https://arxiv.org/pdf/1004.1067v1) states the ordinary-integer Liouville distribution estimate with level below one half. [Shao, page 961](https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf) records the corresponding Bombieri–Vinogradov statement for both Möbius and Liouville. These inputs concern ordinary progressions; they do not themselves assert parity cancellation along shifted primes.

The fresh audit brief is `../../iterations/iteration5-parity-pd-r2-task.json`. It requests independent checks of the determinant transfer, all signed comparison patterns, low/high frequency estimates, progression remainders and positive sieve splitting, prime extraction and limit order, signed-measure tightness, and the joint squarefree consequence. Any material gap blocks promotion. The author report and its prior-art discussion remain provisional; no worldwide-priority conclusion is recorded here.
