# Research contract v1

## Primary problem

Input is the ordinary binary encoding of an arbitrary composite integer N > 1.
Set n = floor(log2 N) + 1. Output an integer d with 1 < d < N and d dividing N.
The input contains N only: no factors, totient, group order, useful square roots,
factor interval, precomputed advice, or corpus-family label.

The deterministic target is one finite classical program A and constants C > 0,
k >= 0 such that, for every composite N, A(N) returns a valid d using at most
C n^k bit-machine steps. Include reading, preprocessing, arithmetic, storage,
and output. A loop polynomial in N is exponential in the input length n.
An unbounded integer operation is not a constant-cost step. Code depending on
input size, lookup tables, and advice need their own construction/size costs.

Splitting plus primality testing and recursive splitting yields full prime
factorization. The splitter must cover *all* composites to support this reduction;
balanced semiprimes alone do not suffice. The factor tree has at most n leaves
counted with multiplicity. This reduction is mathematical background, not yet a
Lean proof of a complete prime-factorization implementation. AKS provides the
primality ingredient; primality testing itself does not produce factors.
[AKS](https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf)

## Randomness is a separate claim

A bounded-error target uses one finite algorithm, at most poly(n) uniformly random
bits, a poly(n) worst-case running-time bound, and success probability at least
2/3 on **each** composite N. A valid factor is efficiently verifiable, so invalid
answers can be filtered. Expected polynomial time with always-correct output
(Las Vegas) requires a different expected-cost theorem, including restarts.
An average over sampled N or over two seeds proves neither guarantee.

The Lean random-tape definition counts successful equally likely tapes exactly.
It is a specification and is not intended to enumerate tapes in an experiment.
No probabilistic complexity theorem is presently proved.

## What Lean checks, and what it does not

`Factoring/Contract.lean` defines bit length, the witness relation, and the
composite-input promise. It proves acceptance equivalence, existence of a
cofactor, a strictly smaller cofactor, and rejection of trivial factors.
`Factoring/Baseline.lean` proves soundness and completeness of exhaustive search.
Its allocation and search are deliberately inefficient; no polynomial bound is
asserted. Two closed examples are evaluated through the kernel.

`Factoring/Goals.lean` specifies deterministic and randomized polynomial splitting
*relative to a supplied machine model*. It intentionally supplies no model or
proof of either goal. Its abstract interface alone cannot certify uniformity,
binary parsing, computability, or cost honesty. An oracle implemented as an
arbitrary Lean function could inhabit that interface: this is a visible trust
boundary, not a factoring result. Before accepting a complexity claim, instantiate
a fixed finite-program classical machine and prove the candidate's refinement.
Do that only for a concrete surviving algorithm; do not expand a generic machine
library as a substitute for algorithm research.

Python implementations and their timings are not refined to Lean. Passing Python
tests is not a proof, and compiling a goal definition does not prove the goal.
`Audit.lean` prints the assumptions of the proved theorems. The source screen is a
convenience check, not protection against a malicious contributor.

`Factoring/ResidualNormalization.lean` proves pointwise integer identities for
removing the exact reciprocal component of a rational certificate: preservation
of its error, recovery expression and public exponent, plus a nonzero-constant
guard and the exact-reciprocal degeneracy. These are algebraic invariants only.
They do not implement polynomial division, prove a modular-power consumer,
bound approximation error, supply useful certificates, or prove a speedup.

`Factoring/ConicParametrization.lean` proves integer identities for a rational
line parametrization of a conic: preservation of its norm, exact cancellation
of a common factor, and cross-numerator identities determining the original
root's sign when the relevant denominators are units. These identities guard
the W020 class-halving attempt against assuming independent modular roots.
The module does not formalize the modular unit/gcd argument, class groups,
root acquisition, sampling, or an end-to-end complexity bound.

## Experimental accounting

The solver boundary passes only N, algorithm RNG seed, and public resource limits.
Each attempt starts in a fresh subprocess. The generation seed, hidden factors,
and family are not passed to the solver. The public development corpus and shared
filesystem still permit deliberate cheating: this is **not** a security sandbox.
Candidate review must reject file/network lookups, hardcoded answers, factor
libraries, and uncharged preprocessing. The OS process timeout kills a worker
that ignores the cooperative event meter; it does not constrain its descendants
or provide an OS memory limit. Run only trusted, reviewed local code.

Recorded diagnostics: arithmetic event vector, peak operand width, sum of squared
operand widths, solver seconds, cold process seconds, and peak Python allocations.
The squared-width sum is only a descriptive proxy: gcd, isqrt, division, randomness,
control flow, memory access, and Python interpreter work do not share a certified
unit cost. Native allocations and child processes are not covered by tracemalloc.
The measured solver time includes RNG setup, candidate preprocessing, restarts,
and witness validation, with tracing enabled. Parent validation and corpus
generation are outside solver time and identified separately.

Event-budget exhaustion, hard timeouts, errors, missing factors, and unstarted
trials remain in results. Timeout counters are unknown, never zero. Limits are
identical across algorithms within a config. The wave deadline includes corpus
setup elapsed time; setup and report writing are bounded ordinary code rather
than independently killed workers. A failed time-limited attempt is a censored
measurement, not a proof that the algorithm is incorrect on that input.

## Evidence levels

1. **Idea:** precise mechanism, unsupported step, prior art, and cheap falsifier.
2. **Screened:** correct measured outputs and matched finite experiments; censored
   trials and special-family wins disclosed.
3. **Mathematical candidate:** correctness argument and full complexity analysis,
   including all constants/parameters needed for polynomial uniformity.
4. **Verified theorem:** reviewed semantics, checked refinement, all-input
   correctness and cost proofs. Independent critical review before acceptance.

Never promote a fit to a theorem. Beating these toy baselines is not beating the
number field sieve, nor a practical RSA result. A current primary-literature
review and appropriate implementations are prerequisites for a novelty claim.

## Separate quantum claim

P and BQP are decision classes; factoring is a function/search problem. Use
"factoring in FP" for the deterministic search claim. Polynomial classical
factoring alone does not prove P = BQP. Conversely, P = BQP would let one replace
bounded-error quantum decision predicates used to recover factor bits by
deterministic polynomial-time decisions, given the standard reduction.
[Shor](https://arxiv.org/abs/quant-ph/9508027)

A general classical *randomized sampler* of uniform quantum circuits with a
controlled total-variation error (e.g. < 1/12) would support BQP ⊆ BPP after
amplification, not by itself BQP ⊆ P. Exact amplitudes, estimating a designated
probability, and sampling whole outputs are different tasks. Specify the gate
set, uniformity, circuit size, error metric, precision cost, and randomness.
An easy circuit subclass does not cover all BQP circuits. No quantum-circuit
simulator or P = BQP formalization is installed in this first environment.

Oracle separations constrain black-box reasoning; they do not settle the
unrelativized P versus BQP question. [Raz–Tal](https://eccc.weizmann.ac.il/report/2018/107/)
