# Scaled Tepper identity — MathDB 354537

**Result:** complete universal proof, with a stronger nonzero real step parameter. Source: Bayat and Teimoori Faal, [arXiv:2205.04237v1](https://arxiv.org/html/2205.04237v1), Conjecture 4.5, equation (13).

For every real polynomial P of degree n, every real x, and every positive integer l,

\[
\sum_{k=0}^{n}(-1)^k\binom nk P(x-lk)=a_n l^n n!,
\]

where a_n is the leading coefficient. The certificate proves this for every nonzero real l. It also handles constant and zero polynomials under Lean's natural-degree convention.

## Proof

An elementary source-based proof is enough: let R(t)=P(lt). It has degree n and leading coefficient a_n l^n. Apply the source's already proved Theorem 4.3 to R at x/l. Its kth summand is R(x/l-k)=P(x-lk), which proves Conjecture 4.5. This reasoning works whenever l is a nonzero real number.

The Lean proof independently uses the pinned library's established finite-difference theorem. For Q(t)=P(x-lt), the nth forward difference at zero equals n! times the leading coefficient a_n(-l)^n. The standard binomial expansion of this difference is

\[
\sum_{k=0}^{n}(-1)^{n-k}\binom nk Q(k).
\]

Multiplication by (-1)^n gives the asserted identity. The parity simplification is itself proved in Lean; polynomial composition, degree, leading coefficient, and evaluation are all linked to the original P.

## Formal coverage

- `ScaledTepper.sign_identity`: the parity identity for all k ≤ n.
- `ScaledTepper.scaled_identity`: every real polynomial, every real x, every nonzero real l.
- `ScaledTepper.mathdb354537`: exact positive-integer-step statement with degree explicitly identified as n.

The proof imports `Mathlib.Algebra.Group.ForwardDiff` and the standard polynomial degree API. It uses no conjectural source statement as an axiom. The primary substantive library dependency is `Polynomial.fwdDiff_iter_degree_eq_factorial`; the finite-sum expansion is `fwdDiff_iter_eq_sum_shift`.

## Prior status and novelty

The retrieved MathDB record lists zero solutions, comments, model attempts, and formalizations. The 2022 source labels equation (13) conjectural, immediately after proving its unit-step counterpart. Targeted live searches on the paper ID, title, and scaled formula did not identify a separate posted resolution. These observations do **not** establish mathematical novelty: the conclusion is an immediate rescaling of the same paper's Theorem 4.3 and a standard finite-difference fact. Claim only a complete answer and local formalization of this distinct MathDB question, not a new-to-literature theorem.

The packet contains a versioned source snapshot and hash manifest, the complete Lean code, compiler/axiom reports, and `paper/main.tex`. The final paper is `main.tex` and its release PDF is `paper.pdf`. Full third-party source bodies are retained locally and are not redistributed.


## Reproduce the release

From the campaign root run `python3 verify_outcome.py outcomes/scaled-tepper`. From an extracted standalone release run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. The release includes pinned dependencies in `pins.json`, exact theorem/axiom logs in `receipts/`, and the complete independent review.
