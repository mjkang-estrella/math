# Validation record

All checks below were performed on 2026-10-08. Upstream statements are
assumed true; the object of validation is each new deduction. No result is
claimed to be Lean-verified or externally peer-reviewed.

## Independent proof review

| Finding | Review | Outcome |
|---|---|---|
| F001 | [Quadrature r1](reviews/quadrature-r1.md) | Accepted; clarified finite dual norms, finite-set limit, and angle-independent endpoint obstruction. |
| Supporting rotation note | [Rotation r1](reviews/rotation-r1.md) | Correct; demoted to an equivalent reformulation, with attribution and endpoint corrections. |
| F002 | [Graph r1](reviews/graph-r1.md) | Accepted after precise classical attribution, small-degree cases and a quantified log-log improvement. |
| F003 | [Singular quartics r1](reviews/singular_quartics-r1.md) | Accepted; normality, rational chart, encoding and height impossibility verified. |
| F004 | [Cyclic actions r1](reviews/cyclic_actions-r1.md) | Accepted; fixed schemes, finite-flat quotient, branch multiplicity and simultaneous stabilization verified. |
| F005–F006 | [Diophantine sums r1](reviews/diophantine_sums-r1.md) | Both accepted with classical circuit/Specker attribution and an explicit real-degree convention. |
| F007 | [Haldane r1](reviews/haldane-r1.md) | Accepted; all commutator factors and constants checked; thermodynamic claims distinguished from finite-volume derivatives. |
| F008 | [Power-free signs r1](reviews/powerfree_signs-r1.md) | Accepted; original-function hypothesis, affine rescaling, double limit and local factors verified. |
| F009 | [Divisor law r1](reviews/divisor_law-r1.md) | Accepted; repeated-prime mass, marked PD tails, moments and conditional nonconcentration checked; closer classical literature added. |
| F010 | [Incidence r1](reviews/unbalanced_incidence-r1.md), [r2](reviews/unbalanced_incidence-r2.md) | Main proof accepted; false optional comparisons removed; corrected text independently accepted again. |

The parent independently checked the central reduction or estimate in each
finding. Reviews are preserved as written, including suggestions later
adopted and exploratory remarks not adopted. The final finding files and
the screening register resolve those remarks.

## Finite computations actually run

From the repository root, all of these require only the Python standard
library. Each completed with exit code zero.

| Command suffix after `python openai-proof-research/experiments/` | Observed result | What it does not prove |
|---|---|---|
| `rotation_quadrature.py` | 60 finite Fourier duality cases; maximum duality residual 8.58e-13 and telescoping residual 3.38e-13. | Infinite-series convergence, an irrationality bound, or an asymptotic error estimate. |
| `complexity.py` | Exact rational exponent balances for r=4,…,10; 40 finite-field Woodbury/factorization identities. | Asymptotic constants, literature priority, or transfer of characteristic-zero runtime bounds to finite fields. The matrix checks concern an unpromoted secondary candidate. |
| `algebra_geometry.py` | 101,250 exact rational Jacobian checks and chart checks; 1,296 matrix-unit identities. | Undecidability or the full geometric proof. Matrix-unit checks concern an unpromoted secondary candidate. |
| `independent_scout.py` | Exact reciprocal-block, separated-digit and natural-gate checks; a largest-prime-factor sieve through 10⁶. | Existence of explicit numerical single-fold polynomials or convergence of the sieve statistics. |
| `probability_dynamics.py` | Exact rational spin Casimir and double-commutator checks, both linear and exponential; XY annihilating polynomial. | The accepted upstream many-body gap. The operator norm is established analytically by self-adjoint blocks. |
| `number_theory.py` | Exact Dirichlet moments: 1/8, 7/384 and covariance 1/384; sieve over 78,497 primes through 10⁶. | The upstream PD law or a quantitative convergence rate. Finite-size bias remains visible. |

The optional archived `combinatorics.py` was also run successfully in an
isolated temporary environment with `networkx==3.7`: two Ramsey blowup
examples, 106 small graph/cycle instances, and two finite lattice-copy
counts. These concern scout corollaries, not the proof of F010. The dependency
is recorded in `experiments/requirements-optional.txt`.

The unfinished NumPy/SciPy experiment in `experiments/parked/` is excluded.
The parent did not run or adopt it; no complete associated proof report was
delivered before that exploration was closed.

## Numerical evidence that was deliberately not used

The F008 review describes a sieve for square divisors p² with p≤10⁶ while
testing n⁴+1 for n≤10⁶. This is a **truncated local sieve**, not exact
squarefreeness over that range. Larger prime squares can divide those values.
Its observed proportions are not adopted as validation of the theorem.

The largest-prime-factor and divisor experiments display nontrivial
finite-cutoff bias. No error term is inferred from apparent movement toward
a predicted limit. Conversely, failure to look close to an asymptotic limit
at a finite cutoff is not a disproof of the stipulated theorem.

## Provenance and repository checks

- The 18 directly cited upstream source files passed byte-size and SHA-256
  verification against `sources/used-sources.json`.
- Every accepted finding has its own initial commit; the index records the
  hashes. Final documentation cleanup may adjust prose without introducing
  additional mathematical findings.
- Commits were scoped to `openai-proof-research/`; pre-existing untracked
  sibling research directories were not added.
- Local Markdown links, Python syntax, and whitespace were checked before
  the final documentation commit. No push or pull request was created.

## Limits of the conclusion

The ten statements have complete reviewed deductions from the stipulated
premises. This research does not certify those premises, settle publication
priority, supply effective constants where the source is ineffective, or
provide executable coefficients for existential single-fold polynomials.
Those limits do not stand in for missing steps in the accepted proofs;
they specify what was and was not established.
