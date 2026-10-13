# I322 parent primary comparison

2026-10-13. The parent read the mathematical body of [Mosca–Zalka, arXiv:quant-ph/0301093v1](https://arxiv.org/html/quant-ph/0301093v1), Sections 1–5, web-extracted lines 42–151. No raw body was retained; no raw-response hash is claimed.

Section 3 gives exact discrete logarithms through an exact Fourier transform. Sections 2 and 4.2 use computed rotations; 4.2 explicitly isolates an input-dependent angle for adjusting success to one quarter. Section 3.1 separately proposes averaging the ordinary discrete-logarithm success rate but leaves efficient computation of that average unresolved there. Section 5.1 discusses composite orders and an iterative factor-discovery variant, still using the precomputed special gates.

This is a model-specific comparison, not a claim that no later paper resolved fixed-gate discrete logarithms. The I322 candidate uses the pinned polygonal transform, conditional per-label exact counts and dyadic completion. Its contribution must be assessed against both this predecessor and later work. A search did not establish worldwide priority. Third-party summaries and a Reddit search hit were not treated as theorem evidence.

## Additional primary comparison, 2026-10-13

Read [Imran–Ivanyos, *An exact quantum hidden subgroup algorithm and applications to solvable groups*](https://www.rintonpress.com/xxqic22/qic-22-910/0770-0789.pdf), web-extracted lines 108–265: the model discussion and full Theorem 1 statement, not its algorithm proof. The theorem charges calls to an exact Fourier-transform oracle. The authors distinguish a finite basis from infinite bases and input-dependent gate parameters; their stated fixed-basis consequence is for fixed modulus. This does not provide I322's implementation for all growing primes. No raw hash or rendered-page inspection is claimed. A separate Python raw download failed with HTTP 465; web extraction succeeded. No external body was retained.

Read [Hadfield, *Quantum Approximation Complexity of Classical Optimization Problems*, arXiv:2610.09584v1](https://arxiv.org/html/2610.09584v1), Appendix F, lines 588–632, including Definition 16 and full Theorem 17 proof. Despite the abstract's wording about an exact optimizer, the theorem explicitly promises bounded-error quantum optimization; its proof uses capped Shor trials with a fallback majority hypothesis. It therefore supplies no probability-one fixed-gate discrete-logarithm implementation. The surrounding abstract/introduction was inspected for context, not the full paper. No raw hash or external body was retained.

These checks narrow two specific comparisons. Neither proves priority or supplies a contribution verdict for I322.
