# H005 I1 first whole-attempt falsifier (pre-run draft)

No execution authorized yet. One tiny synthetic profile, not a scaling claim.
Root owns this protocol; a separate implementer owns inverse_walk.py and an
independent reviewer must check both before the root's single capped run.
No general machine/Lean infrastructure. Main improvement remains NONE.

## Frozen inputs and admission

E/F59: y^2=x^3+28x+27, prime order q=73, G=(34,35), Q=(4,47).
These coordinates are retained public points from the already-recorded H002
fixture (generator seeds7 and19); no secret scalar is supplied to either solver.
Selection is independent of this score. This is one selected tiny instance,
not random-curve evidence, full-size evidence or a restricted-secret problem.
Validate p,q prime, discriminant nonzero, enumerate curve cardinality with an
O(p) squared-ordinate dictionary, assert #E=q, q!=p and nonzero trace. Validate
G,Q on curve and [q]G=[q]Q=O. Admission is charged diagnostic setup, separate
from both solver costs; no enumerated point/log table is exposed to a solver.

## Candidate, exact restart distribution and cost

Use the exact I1 score and map in H005-information-proposal.md. Exact 2D Gauss
reduction starts with vectors (p,0),(int(x),1), uses integer dot products, squared
norms, nearest-integer quotient with a frozen deterministic tie convention;
order the vectors by increasing squared norm and STOP when
2*abs(dot(u,v)) <= norm(u), including equality. Only outside that condition
subtract the nearest integer multiple of u from v, then reorder. This avoids
half-tie oscillation; return norm(u). Independently review termination and the
shortest-vector argument. No floating point or score lookup cache.

Setup H=[(q+1)/2]G, -H, -G once per complete solver. An attempt samples uniform
r in [0,q), computes R=Q+[r]G and starts a=1,b=r. Enumerate ALL73 possible r
in the diagnostic to measure its exact uniform attempt law. A solver does not
receive that enumeration or outcomes. A real uniform draw uses b=ceil(log2 q)
unbiased bits with rejection; record expected bit draws b*2^b/q and expected
raw draws2^b/q separately per attempt. Also charge per raw draw one rejection
comparison and one draw-loop event; per drawn bit one unbiased-bit event, one
left-shift, one OR, and one bit-loop event. Thus these category expectations are
explicit multiples of2^b/q, added to each expected attempt vector; do not treat
diagnostic enumeration as a free online sampler. Independent unbiased bits are
an explicit randomness-model primitive, not a measured physical entropy source.

Freeze transition cap T=2*ceil(sqrt(q))=18. At each state (including time0 and
stateT), first check R=O and R=-G and recover k=-b/a or(-1-b)/a modq immediately.
Then look for R in this attempt's point->(time,a,b) dictionary. A first repeat
has its actual adjacent cycle length; invert a_old-a only if nonzero and recover
k=(b-b_old)/(a_old-a). A zero denominator fails the attempt. If no hit/repeat and
time=T, fail as timeout. Otherwise save the state and take one transition:
U=[(q+1)/2]R via direct binary scalar multiplication, V=U-H, compare exact scores,
update a=inv2*a and b=inv2*(b-d) modq, and continue. No cached halves/scores.
Every claimed answer is checked by actually computing [k]G and comparing to Q.
A false verified answer is an implementation-validation failure that stops the
whole diagnostic, not an ordinary failed restart.
All dictionary/comparison, coefficient arithmetic, inversion, verification,
failed attempts and state formation costs are charged. Peak stored records are reported separately, never added or divided as work.
Memory is O(T) records;
this is the dictionary implementation, not a claim about constant-memory rho.

For each r retain outcome, transition count, actual cycle length where found,
recovered scalar if verified, and attempt event vector. No output from a partial
attempt enters a mean. If all73 attempts finish, u=successes/73 and exact expected
solver work in this event model is setup + sum_r C(r)/successes, categorywise,
plus the sampler expectations/u. If successes=0, expected work is infinite.
This formula includes failures and timeouts. It is the exact uniform-restart law
for THIS fixed Q, not an average over uniformly random secrets/curves. No
empirical successful-only mean.
All inputs to a new attempt are reset; H setup is paid only once per solve.

## Matched executable reference

One frozen signed BSGS baseline, target Q and generator G exactly as above.
m=floor(sqrt(q/2))=6. Build jG for j=0..m by repeated addition, keyed by x for
nonidentity points and an identity sentinel. Keep j and y to recover the sign;
assert no duplicate x keys (m<q/2). Set step=[2]([m]G)+G with two group additions.
For i=0..ceil((q-1)/(2m+1)), inspect W=Q-i*step, match to a stored baby by x,
check its y or negation, and recover k=i*(2m+1) +/- j modq. Identity uses j=0.
Verify [k]G=Q. A false answer or exhausting this guaranteed-covering reference
is a fatal implementation-validation failure. Advance W by subtracting step only when another giant is needed.
This covers the entire scalar domain by intervals i*(2m+1)+[-m,m]; it does not
know k, use a target-dependent m, or receive the diagnostic's full-domain table.
Charge all baby setup, point arithmetic, lookups, comparisons, scalar recovery
and verification. This is a reference implementation, not the fastest known
possible implementation; known paired arithmetic or optimized inversion could
improve it further. Candidate and reference share the same affine arithmetic
and explicit field-inversion implementation, without shared secret advice.

## First gate and accounting scope

Compare categorywise expected candidate cost with the complete reference cost;
report group additions, field arithmetic/inversions, integer/lattice work,
lookups/comparisons and stored records separately. No arbitrary category-weight
sum is a CPU runtime. If the candidate loses even with its score/integer overhead
omitted and has no offsetting charged resource advantage, park this frozen
implementation. This is a finite implementation screen, not a universal exclusion
of rational scores, all timeout choices, inverse walks or an asymptotic theorem.
Do not optimize the timeout/score after seeing the result.

Only if it survives this first cost gate, propose a NEW independently reviewed
protocol for increasing parameter sizes/generator seeds and random-score controls.
Those controls are diagnostic; a full random rank table is not free solver advice.
No improved solver/work estimate is accepted from this single profile alone.

## Global budget and reproducibility

One cap covers admission, candidate setup/all attempts, reference and all executed
checks: <=1,000,000 instrumented events and <=60 monotonic seconds. CLI may lower
caps only. Count actual field add/sub/mul/inversion (inversion via explicit
binary exponentiation or explicitly counted Euclid), group operations/scalar
bits, integer arithmetic/divmods, lattice reduction iterations, table accesses,
comparisons and loop events. Explain overlaps and exclusions: not every Python
instruction, bit operation, allocation, hash, serializer or hardware transaction.
No built-in modular pow/inverse or hidden numeric libraries. No scalar-to-point
or inverse-log table is consulted by solver code. Diagnostic admission/enumeration
is isolated, and its work is visible. No experimental warmup/test run permitted.

On cap/failure write completed attempt records, active phase/partial vector,
total counter reconciliation, source/protocol SHA256 and explicit incomplete
status. An incomplete attempt/domain has no expected-cost verdict. Exit2 on
incomplete/error, exit0 only full completion. Preserve failures; never reset cap.
The root will specify the exact execution/output command after source review.
Syntax-only checks are allowed to the implementer with caches outside repository.
