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

## H003 factor-sum sieve

Reviewed 2026-10-08 UTC: [Hittmeir, Integer Factorization as Subset-Sum Problem](https://arxiv.org/html/2205.10074v1),
2022 preprint / Journal of Number Theory 2023. The paper studies hyperbolic sieve
sets, their CRT construction and a multiple-choice subset-sum reduction. Its
Fermat refinements include a rigorous method and a separate heuristic time-space
tradeoff. H003's proposed sieve is prior art; its parent-owned cardinality gate
only examines the cost of materializing the complete allowed residue set.

## W002 comparison refresh — 2026-10-08

The coordinator made a bounded primary-source follow-up while the three W002
constructors ran. This is not an exhaustive novelty search or a new proof audit.
The comparison bounds in W001-baselines.md remain the working benchmarks.

- [Gao–Feng–Hu–Pan, arXiv:2512.19076v1](https://arxiv.org/html/2512.19076v1),
  submitted 22 December 2025: the introduction, technical overview and
  Theorem 1.1 were read directly in the full HTML text. The stated
  N^(1/5) log^(13/5)(N)/(log log N)^(3/5) bound retains the balanced-semiprime
  promise. This adds an accessible primary version to the earlier IACR entry;
  it does not change the exponent or establish an all-composite replacement.
- [Harvey–Hittmeir, arXiv:2601.11131v2](https://arxiv.org/html/2601.11131v2),
  5 June 2026: Theorem 1.1 and its output contract were rechecked. For
  1<=D<N-1 it returns a factor or an element of order greater than D.
  Its O(sqrt(D) log(D) log(N)/sqrt(log log D)) time is not a guaranteed
  splitting time. The advertised space bound remains stated without details.
- [Lee–Venkatesan, arXiv:1805.08873](https://arxiv.org/abs/1805.08873):
  the primary version history still lists v1. Its abstract's rigorous target
  is square congruences. The previously inspected useful-congruence condition
  remains part of our comparison; this metadata check supplies no new
  productive-root theorem.

### Additional batch primitive, with scope kept explicit

[Altman, arXiv:2509.12705v1](https://arxiv.org/html/2509.12705v1),
16 September 2025. Read Theorems 1.1 and 3.1, associated scope remarks,
Section 3's product-tree construction and the beginning of Section 5;
the full proof was not independently audited.

For a monic irreducible degree-d integer polynomial of height H and
splitting-field degree m, Theorem 1.1 states simultaneous factorization
modulo all primes below X in pi(X)*(m log H)^O(1)*log^5(X) time.
The dependence is on m, potentially d!, not automatically polynomial in d.

Root finding alone has a stronger degree dependence: Theorem 3.1 uses
W=log H+d log X and time
pi(X)*O(W log(XW) log^3 X + W log W log(dH) log X).
Its Section 3 accounting uses a multitape Turing model and constructs the
integer evaluations before batch divisibility processing.

Coordinator interpretation: this is useful prior art for constructing a
small-prime root table. It does not provide an unknown prime divisor of an
input integer, sublinear-in-X total work, relation supply, or a productive
square congruence. It supplies no new complete factoring improvement here.

### CM anomalous-curve gate

The coordinator checked the existing scalar-N CM factoring route and
class-polynomial construction costs. The [source gate](../research/findings/CM-priorart-gate.md)
records primary links, exact versions, read scope, GRH/rounding/success
qualifications, archived bytes and failed retrievals. The mechanism is
existing special-purpose prior art. No new N-only discriminant-selection
algorithm or improved complete factoring bound is supplied.
