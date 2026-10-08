# H025 exact finite signed-layout screen v1 — frozen before execution

Root implementation, independent STATIC review before first run. No run/import
self-test has occurred. This is exact generated-key coverage, not a full EC
solver, hardware benchmark, asymptotic proof or claimed new attack.

Run cases in fixed order: q509 then1009; control,A,B on each. All q scalars
uniform. Primes and fixed layouts are from the pre-run independent reviews.
M=floor(sqrt(q/2)), h=max(1,floor(floor(log2(q))/16)), B=h(2h+1)=3 here.
Control: b=(0,1,2),s=(1,M,−(M+1)),c=0.
A: b=(0,1,3,7),s=(1,M,−(M+1),M+2),c_i=floor(q/17)*b_i² modq.
B: b=(1,2,4,8),s=(M,−(M+1),M+2,−(M+3)),c_i=floor(q/73)*b_i² modq.
Labels are(b_i,c_i+j*s_i), meaning b_i Q+(c_i+j*s_i)G.

Control/A extend nonnegative intervals. B starts−floor(B/2)..ceil(B/2)−1,
then alternates positive and negative frontier blocks each whole-family round.
Negative blocks enumerate descending indices to keep transient intervals
contiguous; only completed blocks are inspected, so this preserves the declared
sets. Family order cyclic. Main cap=floor(3ceil(sqrt(q))/B)*B generated keys,
allowing a cap mid-round. B's intermediate midpoints drift: no perfect-centering
or unproved short-coverage formula is used.

Main and fallback each install public labels O=(0,0),G=(0,1),Q=(1,0): three
logical records, paid comparisons and setup, zero NEW generated keys. Initial
coverage{0,1,q−1}. Compare every emitted label with supplied inputs and all
previous same-phase labels, including earlier outputs in the current block.
For each sign, nonzero e=b−epsilon*b' gives k=(epsilon*a'−a)/e modq.
Zero denominators discover nothing. Include direct infinity when b!=0.
All signed denominator inverses are expanded and cached during phase setup;
inner candidate loops increment a modular arithmetic progression.

Main stops when all q scalars are covered or its cap is reached. On any main
miss, charge clearing all main records (generated+3), reinstall inputs and
run full fallback: b=(0,1),c=0,s=(1,−D0),D0=ceil(sqrt(2q)), indices0..H,
H=ceil(D0/2), including whole-block overshoot. Alternate fallback families;
run its entire declared range even if coverage becomes full earlier. No main
records participate in fallback comparisons. Preserve global discovery bitmap
ONLY to compute reach probabilities, not as an extra solver lookup table.

Before every block add B*(q−covered_before) to exact mean numerator. Check
against the sum of every scalar's first completed-block key cost (input hits0).
One5% gate per candidate/prime:20*N_candidate<=19*N_control. A candidate passes
the declared gate only on BOTH primes. No float, retuning, omitted failure,
warmup, replacement or cap reset. This wrapper's control is GWZ-style, not an
exact reproduction of a published asymptotic constant.

Separate cross-only bitmap counts UNION of all cross-family emitted-output
candidate scalars, irrespective of who first discovered each scalar. Inputs and
same-family matches are excluded from this diagnostic. Reset cross bitmap by
phase, but not global first discoveries. Compare to t²−sum L_i² using actual
prefix lengths, never the raw erroneous equal-length budget. This describes
finite overlap; it is not a hardness/gain claim.

Report mean numerator/q, each block's coverage, direct/signed updates, zero
coefficients, first-discovery array, main failure count, peak generated+3 search
records, and clearing record numerator/q separately. Supporting EC points,
scalar initialization, hashing and eventual verification still need a real EC
implementation; none is inferred from key count. Candidates use extra frontiers
and nonzero shifts. Equal main key cap is not equal total memory or an equal-cap
comparison against H019's smaller two-family table.

One GLOBAL1M-event/60-second cap, external timeout60s and python3 -B. Reuse H018
Meter/Field/prime_trial. Bounded-word modular-RAM operations, loop/comparison,
dynamic-array/cache accesses, candidate-update events and trace record creation
are charged; inversions and integer roots are expanded. Fixed register accesses,
assignments, Python object administration, counter/timer machinery, source hashing
and JSON encoding are administrative (wall time included externally). This is
not bytecode, bit-cost or a hardware work ledger. Output-only metadata field
updates are administrative; record creation is explicitly charged. The raw
884120 and Fable candidate-count bounds are not relied upon. Review the concrete
loop and guard; a cap is inconclusive, retaining partial cases/blocks/arrays.
No promise that every phase fits a reservation. Failed correctness assertions
also mark the whole run inconclusive and must not become a performance result.

A finite pass/fail only addresses this declared key-count comparison. Setup,
small-size rounding, linear coverage terms and fallback may dominate. Neither
outcome proves or refutes an asymptotic gain or full-size hardness change.

Partial evidence refinement before execution: attach the first-discovery array
before filling it, and retain pending-block metadata while candidates are being
enumerated. A partial block's provisional mean is not a completed-block result;
any interrupted run is globally inconclusive. Metadata-only progress writes do
not count as search operations under the stated administration convention.
The initial case shell survives even an early setup interruption.

Pre-run admission: native Astra static correctness review and native Sol static
budget review both GO for ONE capped run, with no execution/import/self-tests.
Inner recurrence bound14 events is checked; setup/outer/input overhead is extra,
and aggregate completion below1M is not certified. A cap remains inconclusive.
