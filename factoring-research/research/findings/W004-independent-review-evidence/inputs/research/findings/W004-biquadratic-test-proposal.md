# W004 — optional later finite coverage falsifier

2026-10-08. **PROPOSED ONLY; NOT RUN.** This is separate from the symbolic
[construction](W004-biquadratic-construction.md). The parent owns any later
implementation and authorization. Obtain the new independent review first.
No input values, numerical witnesses or experimental outcomes were generated.

Test only the finite assertion: every tested promised input either exits through
a verified early factor/root or has a useful packet in the report's two bounded
families at M=bit_length(N)^2. This assertion is not claimed in the report.
One fully completed failing input refutes this cap-coverage assertion; it does
not refute larger caps, other row families, or factoring algorithms generally.

## Frozen proposed inputs and information boundary

Use the first twelve increasing integers N in [128,512) which are composite,
coprime to 30, and have at least two distinct prime divisors. Corpus generation
may use exhaustive trial division to apply this public finite filter. For each
N form and sort the distinct unit-square residues. If their count is h, choose
the residues at zero-based indices 0, floor((h-1)/3), floor(2(h-1)/3), h-1,
deduplicating indices. There are at most 48 cases, processed by increasing N
and then R. This rule, not a hand-picked successful list, determines the corpus.

The inner worker receives only N,R and the public cap/budgets. Never pass its
generating root, factors, phi(N), or the full corpus-generation transcript.
There are no random choices: corpus seed, worker seed and restart seed are
all **NONE (deterministic)**. No cold restarts are permitted in this screen.
The deterministic two-list Norm2 tie rule, eligible-prime scan, finite-field
pair order, CRT representatives, shifts and every early exit are exactly
those of the report. Scan both anchored rotation families before the reciprocal
family; preserve all attempts and their order. No family label enters the worker.

## Budgets and required record

- At most 48 cases; setup and corpus generation at most 10 seconds.
- At most 1 second and 200,000 recorded arithmetic events per fresh worker;
  at most 60 seconds for the whole wave, including setup and launch overhead.
- M=n^2, with no adaptive enlargement. Fixed degree two; no auxiliary solver,
  elliptic-group computation, factoring library, or alternative Norm2 routine.
- Maximum exact operand width 4096 bits; exceedance is BUDGET-UNKNOWN.
- Soft traced Python allocation budget 32 MiB per worker, checked at accounting
  checkpoints; native allocations are not thereby bounded. This is not a
  claimed operating-system memory limit.
- At most 1 MiB of records per case and 64 MiB total archived run output;
  stop with an explicit evidence-budget status rather than drop records.

Charge and record Norm2 construction/sorting, all prime and character work,
CRT, every square test, gcd, nonunit, rejected parameter, exact field-root
calculation, derivative clearing and modular verification. Store input and
source hashes, cap, candidate coordinates, maximum width, elapsed time,
event counts and final status. Distinguish early factor/root, anchored mixed
target, reciprocal mixed target, fully exhausted failure, timeout, budget
exhaustion, validation error and unstarted cases. The archived worker inputs
must remain free of hidden roots and factor metadata.

## Rejection and interpretation

Reject the finite cap-coverage assertion upon the first promised case whose
entire specified finite program completes with FAILURE after all candidates.
An invalid returned root, false field identity or invalid cleared denominator
instead rejects the implementation/algebra at that exact witness and must be
investigated before any coverage interpretation. Timeouts, budget exhaustion
and unstarted cases are UNKNOWN, never evidence of nonexistence.

If no counterexample completes, the result is inconclusive. Even all 48
successes give no all-input probability law, point-height bound, relation
smoothness theorem or complete factoring improvement. Record early successes
separately so that they cannot be mistaken for successful common-target
construction. Do not enlarge the cap or tune the corpus after seeing outcomes.
