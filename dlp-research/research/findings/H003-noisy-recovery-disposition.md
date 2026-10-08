# H003 conditional Fourier recovery: mathematical review and remaining gates

Current decision: accept the Fourier/importance-sampling argument as a reviewed
paper derivation, conditional on a cheap fixed predicate of sufficient magnitude.
No implementation, Lean theorem, novelty claim or ECDLP improvement. Factory
Fable's independent numerical/bit-cost review has completed; both reviewers
accept polynomial bit complexity after explicit arithmetic repairs. Preserve the
original proposal and raw Opus review; neither's numerical constants are a benchmark.

## Accepted mathematical scope

The normalized parity Fourier formula, multiplicative frequency transport,
unbiased interval-energy estimator and bound |Z|<=H are correct under the stated
real-valued fixed-predicate assumptions. Fresh independent samples per interval
allow a conditional union bound even with adaptive refinement. Enforced test and
width caps bound failed runs as well as successful ones. Candidate scalars are
verified by multiplication, and both base and target searches are charged.

Absolute full-domain correlation >=2*epsilon suffices; positive or known
orientation is unnecessary. This narrowly supersedes the orientation gate in
H002-eds-initial-diagnostic.md. A guaranteed nonzero heavy Fourier coefficient
would also suffice without parity correlation. Neither exists as an established
large-instance property of our EDS candidate. Identity exclusions are B=0 and
use numerator/q, not numerator/eligible_count. Changing domains or selecting
features from test results still needs paid selection and independent evidence.

For randomized B, define f as its mean and use independent coins for every call,
including two calls at the same point when y=0; one call squared is wrong.
No independent-errors assumption across distinct inputs is needed. A known
magnitude floor/cap is needed for bounded work; the sign correction does not
make an unrestricted epsilon-search free or terminating.

The paper derivation gives a conservative sufficient epsilon^(-6) times
logarithmic factors bound when predicate, point, sampling and numerical costs
are polynomial in log(q). If epsilon=q^(-beta), beta<1/12 is sufficient under
those assumptions. It is NOT an optimal or necessary threshold for all recovery
methods. The review's phrase 'exactly when' overstates what an upper bound
establishes and is not adopted. No asymptotic statement follows from small q.

## Constants and implementation obligations

The reviewer checks ||hat(g)||_1<=2+ln(q)<=H+2. Thus the integer upper bound
L=H+2 may replace 4H+4 in a future frozen specification, avoiding a need to
compute a logarithm just to set the threshold. Do not silently change the
original proposal's constants. The review's comparison factor of about4^6 is
only rough: log bases and the precise chosen L matter.

The reviewer gives a geometric-series precision argument. A nonzero denominator
has magnitude >=4*|y|_q/q, which can still be small; the O(log q) extra precision
must be implemented and paid. Its explicit small constant is not yet independently
accepted. All rounding stages, predictor evaluation error, summation, transcendental
enclosures, exact random sampling and capped failures await the separate cost
review. There is no constant-time real-number oracle.

The raw illustrative epsilon=1 is outside the premise for B in[-1,1]:
|correlation|<=1 entails epsilon<=1/2. It can only be a coefficient convention,
not a realizable predictor example. Do not use those numbers as a measured
speedup. A1 at q≈139 is far below useful sizes for this deliberately conservative
procedure, even if its finite correlations were certified perfectly.

Optional sample reuse could reduce predicate calls to epsilon^(-4) up to logs,
but the proposed explicit interval arithmetic still costs epsilon^(-6). It is
not accepted as a full-work exponent improvement or implemented optimization.
Single-target f0 preprocessing is charged; amortization changes the challenge.

## Next decision

No larger EDS arithmetic run from the existing data alone. Native Astra is now
examining exact character/divisor cancellations or a concrete exceptional-family
mechanism that could predict sufficient magnitude. This is separate from the
numerical-cost review and the p-adic section work. The next qualifying experiment
must have a magnitude threshold tied to the complete recovery cost and held-out
synthetic cases; an unexplained tiny-instance correlation is not enough.

Validation: ./scripts/check.sh > /tmp/ecdlp-h003-review-check.log 2>&1 exited0.
No Lean claims changed, so Audit.lean is unchanged. This is paper-level conditional
analysis and a correction to an experimental decision gate, not a proof artifact.

## Completed independent bit-cost review: accepted and rejected parts

Factory Fable rederived the estimator and supplies a real trigonometric quotient,
exact modular argument reduction, fixed-point accumulation and precision growing
polynomially in log(q), log(1/epsilon). This supports implementability without a
real-arithmetic oracle. Root accepts the polynomial precision conclusion, not
an executable certified implementation or its exact 8H rounding constant. A
conservative absolute-precision implementation from the mathematical review is
also polynomial. There is no need to build either without a surviving predicate.

The raw 40-bit mantissa illustration does not remove H-bit arguments, integer
reduction, exponent range, enclosure construction, or predictor-output rounding.
Its y=0 square is valid only for deterministic f; randomized predictors still
need two independent invocations. Any sampling cap must receive its own failure
budget. An unknown-epsilon halving schedule requires an explicit stopping floor;
verification alone does not force termination. 'Optimal delta=1/2' is unproved.

Do NOT adopt the raw group-add prices, fixed-base table assumptions, trig prices,
phi-cost guesses, rho constant as a calibrated matched comparator, or finite-size
break-even claims. They are hypothetical unmeasured inputs. Nor adopt the claim
that 41 comparisons are near-independent: negative generators and overlapping
windows create explicit dependence, already recorded in the diagnostic. Its
sigma discussion supplies no valid p-value or model of this deterministic data.

The suggested roughly ten-million-evaluation kill test is NOT funded. It greatly
exceeds the original instrumented cap and supplies no mechanism for a persistent
bias. Moreover a new candidate-specific coordinate identity may provide an
analytic bound for every fixed window, making that pilot unnecessary; independent
source/mathematical review is now running. Baseline and verified gain are unchanged.
