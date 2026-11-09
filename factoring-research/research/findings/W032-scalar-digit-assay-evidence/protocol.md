# W032 scalar digit assay — immutable pre-execution protocol

This protocol, the full task brief, parent protocol, imported interface, source,
and expanded cases are frozen and hashed before the single numerical execution.
Source design and static syntax inspection do not execute candidate arithmetic.
No exploratory candidate invocation, data-dependent tuning, or rerun is allowed.
The sibling W031 normalized screen and symbolic W032 review are outside scope.

## Fixed cases and input boundary

R=4 throughout. Indices 0..142 are (N,a)=(143,index); indices 143..154 are
N=323 with a=1,2,3,5,7,11,13,17,23,31,47,61 in that exact order. All 155
records remain in results, including skip, failure, stop and unstarted records.
There is no random seed, sampling, adaptive selection, or success-rate threshold.
The full 143 domain is a finite census; the 323 list is a fixed public holdout,
not an adversarially blind or statistically representative holdout.

candidate.py gets N,a,R, a meter, an output record, and public setup derived only
from N,R. Its initial gcd is separate. For a=0 it skips normalization; for a
proper initial gcd it retains that ordinary factor without computing digits.
Every reached unit computes all four digits and gcds regardless of earlier hits.
Known factors (11,13) and (17,19) occur only in configuration/reference work.
They are supplied reference facts, not acquired by the candidate. The reference
checks their product, size threshold, gcd(N,30), and formula denominators; it
does not run a new primality test of these known small primes.

## Frozen implementation choice

For each N, globally compute N^0 through N^11 with a short paid multiplication
chain, and (-4)^((N-1)/2) mod N^9 by binary powering. Cache public N^2, N^9,
N^11 and N^(2r), r=1..4. This public power array is not a polynomial jet.
Reference inverses 24^-1, 640^-1 modulo each N, and 2^-1 modulo 143^11 are
computed once and paid, with paid inverse identity checks. The per-unit
normalizing inverse is computed directly with pow(denominator,-1,N^9).

Set z=N*a and Delta=z*z-4. Initialize pair accumulator (A,B)=(z,1) to the
leading exponent bit. For each remaining bit of N, square using

    aa=A*A, bb=B*B, dbb=Delta*bb, ab=A*B;
    (A,B)=(aa+dbb,ab+ab), all modulo N^11.

For a one-bit, multiply by (z,1) using

    az=A*z, db=Delta*B, bz=B*z;
    (A,B)=(az+db,A+bz), all modulo N^11.

There are seven pair squarings/four base multiplies at N=143 and eight/three
at N=323. No literal N-step exponent loop is used. On unit inputs z and Delta
are already nonnegative and below N^11, so their initial reductions are omitted.
All later pair outputs are canonical. The construction does not use finite
differences, coefficient lists, root lookups, factorials, or known factors.

Divide the canonical A by N^2 with divmod and reject a nonzero remainder. Form
the canonical V=(A/N^2)/(a*(-4)^n) modulo N^9. Extract each digit by floor
division by the cached N^(2r), followed by remainder modulo N; compute gcd(d,N).
Discarded odd base-N digits are retained in V and are not subtracted away.

## Independent controls and rejection rules

For every unit check A divisibility, V mod N^2=1, canonical V/digits,
d1=a^2*24^-1 mod N, and

    r=(-a^2) mod 24,
    d2=(3*a^4)*640^-1 - (a^2+r)/24 mod N.

The second quotient must be an exact integer; record it and its remainder.
Record d1's unit gcd as an explicit check. Formula controls run after the
candidate has produced all digits. No formula value feeds the candidate.

For N=143 and exactly a=1,2,3,5,7, calculate D(z)^N directly as dense 2x2
matrices, D(z)=[[2*z,-4],[1,0]], reduced modulo N^11. Its own binary loop
performs ordinary matrix multiplication with eight scalar modular products and
four sums per product. It calls no pair routine and never uses Delta. Compare
(trace mod N^11)*inverse(2) mod N^11 to A. Canonical trace is never integer-halved.
This independently checks the algebra representation, while sharing the scalar
arithmetic meter and interpreter. It is not an independent implementation of
integer arithmetic or a proof of the symbolic trace identity.

For every initial/digit gcd, record 1/proper/N category, cofactor, divisibility
of N and the tested value using two explicit divmods, and support among the
supplied reference primes. The support is derived from the measured gcd, not
a second independent gcd algorithm. Validate the gcd's range, both exact
divisibilities, and membership in {1,p,q,N}. No trivial gcd is counted as a split.

Any false formula, divisibility, representation, canonical-range or factor
check, noninvertible denominator, or implementation exception is failure. Stop
globally at the first failure; preserve its partial record, every completed
record, all unstarted indices, and the event trace. Never fix-and-rerun. A cap
stop is censored/inconclusive rather than a false mathematical identity.
Passing all controls supports only this fixed finite diagnostic.

## Accounting frozen before the run

The whole assay has one global cap of 20,000 completed arithmetic/control
events and one 60-second wall cap. Candidate setup, reference setup, all cases,
formula checks, factor-property checks and the five matrix controls share both
caps. No per-case reset, warmup, second run, cap increase or fallback is permitted.
Each primitive checks remaining budget before performing its arithmetic.

One event means exactly one invocation of the following wrappers:

- integer multiply, add or subtract: one event each;
- modular multiply/add/subtract: one fused arithmetic operation plus its canonical
  reduction, one event (not two); record unreduced intermediate bit width;
- standalone remainder: one event;
- integer divmod: quotient and remainder together, one event;
- gcd: one event for Python math.gcd, with input/output widths;
- inverse: one event for Python pow(x,-1,M), including internal Euclidean work;
  the internal iterations and intermediate widths of gcd/inverse are opaque;
- power_begin: one event declaring base/parameter, full exponent and modulus;
- power_square_stage / power_multiply_stage: one additional event per executed
  binary operation stage, covering bit inspection/control; scalar operations
  within that stage are still separately charged;
- public_power_stage: one event per step of the fixed N-power setup chain;
- trial_stage and digit_stage: one event per entered case/extracted digit;
- branch_classification: one event for the stated gcd decision/classification;
- control_check: one event per named predicate, possibly a compound bounded
  range/product/identity predicate. Arithmetic producing its operands is charged
  separately. Each frozen payload hash validation is also one control event.

Binary-string conversion and iteration mechanics are covered by power_begin
and stages, not counted as separate Python instructions. Fixed matrix i,j
indexing belongs to the matrix stage; each scalar product/sum is still metered.
Loop/index increments, dictionary/list access, logging, JSON, SHA-256, clocks,
event/count accumulation and output summarization are administration rather than
candidate-number arithmetic. They are not extra arithmetic events and their wall
time is included. No arithmetic or checks of diagnostic identities are deferred
to unmetered postprocessing. Human report writing and final packaging occur after
execution; they do not rerun candidate/reference functions.

Events are not bit costs. Record every event's operands, results, scope, trial,
operand/intermediate/result bit widths, plus global and per-case vectors/maxima.
Widths use abs(x).bit_length(), with zero width 0; intermediates include the raw
product/sum before modular reduction. The sum of squared maximal widths is an
uncertified descriptive proxy only. No internal gcd/inverse width bound, Python
allocation bound, or machine complexity theorem follows from this instrument.

An analytic pre-run source count places this fixed schedule close to the cap;
this is not a measured pilot. If the accounting nevertheless consumes the cap,
retain censoring rather than reducing checks or increasing the cap.

## Time guard, retention and evidence

launch_once.py creates RUN-ONCE.json exclusively; an existing marker prohibits a
second launch. Its 60-second deadline starts before marker creation and child
startup, and is passed to the meter. The launcher kills the child at the external
deadline if needed. The child checks time before events and after the cases.
Cold child import, hash verification, setup, logs, summary and results serialization
are included in the launcher's wall measurement. No post-deadline computation is
accepted as passing. Timeout kill/retention overhead is reported separately by
the observed launcher duration and never called a successful in-budget execution.
The tiny interpreter startup of the launcher itself precedes its start timestamp.

events.jsonl is flushed after each event; records.jsonl after each completed
case; progress.json before a case and after the candidate, and after completion.
The normal result retains partial failure records and all unstarted records.
On a hard kill, launcher recovery combines these durable files without restarting
any mathematics, labels unknown accounting as unknown, and retains every index.

Frozen inputs and all source bytes are SHA-256 inventoried in freeze-manifest.json,
which receives a terminal hash BEFORE execution. A final delivery manifest lists
the report and every evidence payload, excluding only the manifest itself and its
anchor file to avoid self-reference. The anchor file contains the manifest hash,
and that same hash is printed independently in the external terminal/final handoff.
Shared project checks are the parent's responsibility after evidence intake.

Verified complete improvement: NONE. No factoring baseline, statistical
generalization, asymptotic success law, or factoring complexity claim is made.
