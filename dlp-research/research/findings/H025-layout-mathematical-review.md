# H025 signed layouts: independent mathematical review

2026-10-08. Native Astra reviewed Sol's two explicit schedules; root checked
its derivations and separately raised midpoint/initial-input objections. No
coverage experiment yet. Verified gain NONE. Budget/code/memory review remains
separate; mathematical executability is not a complete-work improvement.

## Accepted chart argument, limited coverage rationale

Write d=17 or73, D=q/d−theta with0<=theta<1. A signed candidate obeys

    k/q=Delta/(d*e)+h/e+(v−theta*Delta)/(e*q).

All residue charts h/e must be included. The finite error bound
(|Delta|+|v|)/(|e|q) follows. Distinct Delta/e modulo d, with denominators
invertible modulo d, implies disjoint limiting origin sets. The proposal's
fingerprints check up to the common sign. ACTUAL finite neighborhoods must
also be disjoint; no critical-prefix gain is established by these facts.

A's12L²−3L is conditional CROSS-FAMILY coverage: each baby pair combines
signs into indices−(L−1)..L−1, giving2L²−L under injectivity; three baby
pairs plus six nonbaby signed channels give the count when finite patches are
disjoint. Same-family negatives and infinity can add more. Sufficient local
conditions include2L−2<M, no-wrap inequalities and chart-neighborhood separation.
They have not been established uniformly through the main stopping range.

B's strides M and−(M+3) have gcd3 when3 divides M. Index differences
Delta j=(M+3)/3, Delta r=−M/3 repeat their channel numerator. At q73,M6,
pairs(j,r)=(-1,1) and(2,-1) already duplicate after the first positive extension
of family0. This disproves unrestricted channel injectivity, not the layout.

Freeze B's initial interval as−floor(B/2)..ceil(B/2)−1. Appending a positive
block shifts its midpoint by B/2; the following negative extension restores it.
Individual family interleaving therefore changes patch centers temporarily.
The fixed-center rationale holds only at paired-round boundaries; exact
enumeration must use actual block order and this intermediate drift.

## Fallback, finite mean and initial inputs

D0=ceil(sqrt(2q)), H=ceil(D0/2), signed fallback indices0..H including
completed-block overshoot cover all k via jD0±i,0<=i,j<=H. Zero signed
coefficient discovers nothing; no tautological relation counts as recovery.
The all-q uniform generated-key mean is exactly

    sum_blocks B*(q−|C_before|)/q.

Include within-block pairs. Main discoveries remain in a diagnostic probability
bitmap during fallback, but cleared main records are not compared with fallback
outputs. Setup/clearing/support/verification are additional costs, with fallback
work weighted by its reach probability in a later complete-cost analysis.

Root proposed and Astra independently checked the initial convention: both
main and fallback phases install three public labels for O,G,Q, namely
(b,a)=(0,0),(0,1),(1,0). Their tests give C0={0,1,q−1}. No new generated
keys are charged for supplied points, but work and three logical records are
charged. Every emitted label compares with public inputs and same-phase records.
Fallback clearing deletes all records then reinstalls those three; no other
cross-phase pairs. Precomputed centers/offsets not explicitly inspected yield
no search coverage, although constructing them remains paid. Peak table counts
are generated records plus3; support/scratch is additional. No inverse advice.

## Admission scope

Exact enumeration can test the q73/509 finite key gate after protocol and code
review. It MUST replace all unproved coverage formulas and include actual
fallback/order/initial inputs. Passing is not a large-curve or asymptotic result;
failing these tiny rounded cases alone does not disprove an asymptotic family.
Candidate updates/loop work and public-input extra pairs must enter the actual
budget; the original20853-update estimate is not automatically retained after
this initial-state clarification. No full EC solver or broad Lean stack needed.

## Completed Fable protocol review: root reconciliation before implementation

Fable's raw cost review is retained separately, with several claims NOT accepted.
It usefully identifies setup dominance and suggests primes509,1009 instead of
73,509 BEFORE any run. Root will freeze509,1009 for the first key-only screen;
no previously observed data informed this change. These are still small exact
finite tests, not evidence about an asymptotic constant.

Keep the already independently reviewed all-q prior and initial C0={0,±1}.
Excluding zero is not required to fix a bias: it already incurs zero generated
keys. Removing it simply changes a common denominator fromq toq−1, leaving
candidate/control mean ratios unchanged. Charge the input tests and records.
Do not silently change the challenge or leave those input pairs out of counts.

The raw equal control lengths are wrong at the cap with whole blocks:
q509 gives23 blocks,B3,f3 lengths(24,24,21), not(23,23,23);
q1009 gives32 blocks lengths(33,33,30), not(32,32,32).
Recompute budget ceilings from actual counts, including public-input pairs.
No per-pair inverse: precompute signed denominator inverses and progression
increments, with expanded setup arithmetic. Static per-iteration accounting and
one global1M/60s guard are required; the old884120 estimate is unaccepted.

Cross-channel diagnostics must track a SEPARATE union of all cross-family
candidate scalars, even those first discovered by infinity/same-family/input
comparisons. Tagging only global first discoveries biases the proposed ratio.
Reset the cross-only bitmap by phase, preserve the total discovery bitmap for
fallback probabilities, and pay all extra accesses. Use actual prefix lengths
in the ceiling t²−sum L_i². This ratio is descriptive, not a solver gain gate.

Report clearing as expected record work separately from generated-key mean.
At these sizes, extra shifted-start scalar multiplications and block rounding
can dominate EC work; even a5% exact key saving is NOT an arithmetic/complete
solver improvement. Equal main key caps are not equal total auxiliary memory,
or an equal-cap comparison to H019's smaller two-family allocation.

Next authorized action: root implements the frozen finite enumerator, then an
independent static code/budget review before ONE run. No code exists yet at
this checkpoint. The main target remains complete ECDLP work; this cheap screen
can only select or reject the declared finite key-count hypothesis.
