# Source register

Reviewed 2026-10-08 UTC (2026-10-07 America/Los_Angeles). These are starting points,
not a comprehensive or current novelty search. Keep source claims separate from
our conjectures. Do not copy whole copyrighted papers into the repository.

- **Motivation:** [George Hotz, Polynomial Time Factoring Algorithm, 2026-03-16](https://geohot.github.io/blog/jekyll/update/2026/03/16/polynomial-time-factoring.html).
  Predicts efficient classical factoring and argues for P = BQP; supplies no
  executable candidate or proof. Neither prediction is an assumption of this lab.
  The post's broad consequences for asymmetric cryptography do not follow from
  factoring alone; distinct cryptographic problems require separate reductions.
- **Quantum benchmark:** [Peter Shor, Polynomial-Time Algorithms for Prime
  Factorization and Discrete Logarithms on a Quantum Computer](https://arxiv.org/abs/quant-ph/9508027).
  Establishes quantum algorithms; does not supply an efficient classical order
  finder. An order-finding oracle must never be treated as free classical work.
- **Primality:** [Agrawal, Kayal, Saxena, PRIMES is in P](https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf).
  Deterministic polynomial-time prime/composite decision is distinct from
  splitting composites. Our toy generator uses exact trial primality testing,
  not an implementation of AKS.
- **Classical baseline context:** [Menezes, van Oorschot, Vanstone, Handbook of
  Applied Cryptography, Chapter 3](https://cacr.uwaterloo.ca/hac/about/chap3.pdf),
  sections 3.2.1–3.2.7. Covers trial division, rho, p−1, ECM, square methods,
  quadratic sieve, and number field sieve. Useful historical baseline context,
  not evidence of novelty in 2026. Rho's common square-root-in-the-small-factor
  heuristic is not a proved worst-case polynomial bound in bit length.
- **Quantum barrier:** [Raz and Tal, Oracle Separation of BQP and PH](https://eccc.weizmann.ac.il/report/2018/107/).
  An oracle separation, not an unconditional separation of unrelativized classes.

For each future mechanism, add its primary prior art, retrieval date, the exact
claim used, and whether the result is unconditional, heuristic, or conditional.

