# W032 lift-sweep diagnostic: fixed protocol before execution

Registered by parent, 2026-10-08. **Not run.** This is a finite diagnostic
of W032-lift-breakpoint-sweep.md, not an asymptotic scaling study or a
factoring benchmark. Verified complete improvement: **NONE**.

## Frozen cases and candidate

Use exactly b in [9,13,17], in that order. Diagnostic setup uses exact
trial division to choose p as the first prime at least 2^b and q as the
first prime strictly greater than p+2^floor(b/2). Set N=p*q. Prime
generation and validation are charged to the same global budgets. p,q
are available ONLY to the diagnostic and never to the candidate, whose
input is N. No replacement case or alternate prime gap may be selected.

For each N use exactly R=ceil(bit_length(N)/4), a0=1, m=2R+1. There is
one deterministic lift family per N, no tuned depth or seed. Candidate
checks denominator factors and all 2R+2 initial points; retain ordinary
proper/full gcd exits and failed branches. It acquires the base lower
polynomial/remainders and sweeps all w in [0,N) through the exact integer
breakpoint algorithm. Process tied thresholds simultaneously. Do not stop
the diagnostic at the first proper factor: retain the entire finite family
unless a declared budget expires. Actual early-exit work may be reported
as a separate prefix, without deleting subsequent evidence.

At each of the FOUR fixed controls w=0,1,floor(N/2),N-1, independently
reevaluate the lower polynomial at the actual unwrapped lifted points
a_i+12*N^(2R-3)*w. Compare its normalized finite-difference quotient with
the sweep value at that w. Also perform ONE full quadratic-algebra scalar
control for the first N only, at w=0, comparing the filtered top digits
with the gcd-equivalent negative carry quotient modulo N. Its full setup,
wide powers and point computations are charged. No additional controls
are selected after results. R=1 is proved symbolically, not a new case.

Candidate data structures and direct-polynomial controls may share the
frozen coefficient definition, but the scalar control must implement the
original pair-powering normalization separately. Do not claim this makes
the finite test an independent proof of all parameter values.

## Budgets and one-run rule

Use standard-library Python only. There is ONE frozen execution with a
GLOBAL cap of 20,000 declared arithmetic events and 60 seconds wall time
including setup, all candidate groups, controls and recording. Declare the
meter schema and exact source/config hashes BEFORE the first execution.
It must price integer products, additions/subtractions used in arithmetic,
modular reductions, divisions, powers or their actual repeated operations,
gcds/inverses, comparisons in threshold sorting, and reference computations;
record operand/result bit widths. An event is not a bit-operation bound.
List/index administration may be described separately; do not silently
package a whole polynomial evaluation or exponentiation as one cheap event.

Retain every completed, failed, stopped and unstarted group/control, with
contiguous event IDs and explicit budget reasons. Never increase the cap,
retune inputs, repair-and-rerun, or repeat under a new output directory.
If source fails in its single execution, retain that run as failed. A
symbolic issue identified BEFORE execution may stop the assay with a clear
report; it does not license an unrelated substitute experiment.

Freeze a complete source/config/input manifest before execution. Preserve
source snapshots, the exact protocol, timings, all event records, all
interval records and controls, plus the delivery manifest with external
terminal hash. Any unread/unchecked scope must be stated. Candidate code
is owned only by the assigned evidence directory, not shared algorithms.py.
The parent will run required project checks after new code is delivered.

## Measurements and falsifiers

Record every maximal constant interval [start,end], its c, gcd(c,N),
length, all tied events, and whether the actual value is zero, unit,
full-gcd or proper. Check interval coverage of all N integer w values
without iterating over them. Compute distinct c count and max bit length.
The length-weighted proper total divided by N is the EXACT success
probability of a uniform lift parameter for this single finite family,
provided the identities and complete sweep pass. It is not a law for other
inputs or depths. Report all proper factors with independent divisibility
checks. Hidden p,q may verify outcomes and the ordinary uniform-residue
gcd probability (p+q-2)/(pq), never choose candidate parameters or events.

Any failed control, divisibility, tie update, factor verification or
coverage invariant rejects the implemented mechanism's correctness in this
run. A complete family with no proper output is an exhausted finite
family, not a proof that no factoring algorithm exists. If all three
families exhaust without a split, this pilot supplies no positive factor
yield evidence. Zero/unit/full outcomes remain in all denominators. A
budget stop makes the corresponding measurements incomplete, not a
successful zero-cost screen. No regression, fitted exponent, adaptive
case extension, probabilistic independence of intervals, or improved
end-to-end factoring bound may be inferred from these three inputs.
