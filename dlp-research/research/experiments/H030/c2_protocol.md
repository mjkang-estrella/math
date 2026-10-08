# H030 C2 diagnostic v1 — proposed frozen contract

2026-10-08. Root integrates native Sol's protocol after separate Astra/root
admission review. Independent native Astra protocol review gives conditional GO;
the five required orientation/stopping clarifications are incorporated below.
Source construction is authorized; execution is NOT yet
admitted. A separate protocol/source review precedes the single command below.
Question: does coefficient-steered deferred execution implement its stated
logical walk, and what finite stopping/event costs erase its arithmetic credit?
This is not a complete rho implementation, timing benchmark, or gain claim.

## Inputs, limits and sampling

Process these (p,A,B,q,Gx,Gy) fixtures in order, with paid recertification and
no replacement/search:

    (59,28,27,73,34,35)
    (101,2,31,103,0,43)
    (251,1,4,271,0,2)
    (8191,1,5,8053,0,789)

Per fixture, target seeds 7 then19. Candidate r=8,tau=2; y-canonical control
r=32. Four TOTAL starts per arm, initially live, at most32 synchronous rounds.
No replacement starts, restart, tuning, fallback, or continuation after cap.
One global1,000,000 instrumented-event cap and55-second work guard; outer60s.
Cap is inconclusive and retains partial counters/results. Invalid certificate
or correctness mismatch is fatal, with partial evidence. No warmup or selftest
outside this same cap. No promise that all fixtures finish.

Use 32-bit LCG state s <- (1664525*s+1013904223) mod2^32; output
u=s xor(s>>16). Initialization (tag xor p xor q xor seed) mod2^32.
Fixed tags: jumps 0x4A554D50, targets 0x54415247, starts 0x53544152,
hash parameters 0x48415348. Jumps and hashes use seed0 per curve; target/start
streams use the case seed. All integer/xor/shift/sampling work is metered.
Sample [0,n) by rejecting u >= 2^32-(2^32 mod n), then u mod n.
This removes reduction bias for uniform raw words, NOT an iid claim for the
fixed deterministic seeds. No resampling duplicate/awkward valid outputs.

Harness samples k=1+draw(q-1), constructs Q=kG; arms receive only E,G,Q.
Harness input construction is diagnostic work, separate from solver input cost.
Also test Q=O directly with paid equality/recovery verification. Four shared
raw starts use a=draw(q), b=1+draw(q-1), P=aG+bQ. Each arm pays its own start
construction/orientation; no reference coordinates feed the candidate.
Construct all four starts before processing any initial identity/DP events.
An initial success therefore still pays all four starts.

## Tables, state and successor

Sample32 public nonzero alpha_i=1+draw(q-1), J_i=alpha_i G. Control uses all;
candidate uses first8. Separate honest per-arm setup accounting; common work may
be physically shared only with full costs attributed to both single-target
sheets. Candidate bootstraps h(G),h(Q) by independent binary Miller. Table point
and h construction and scalar labels are paid, without subgroup enumeration.

Candidate stores all145 signed formal vectors ||v||_1<=2: index0 zero;
1..16 signed units (coordinate increasing, + then -); 17..32 doubled units
in same order; 33..144 coordinate pairs i<j lexicographic, signs (++,+-,-+,--).
Retain identity, duplicate points and exceptional sums as distinct formal
entries. Composite points/h arise through a declared parent plus signed jump.
Use paid explicit index ranking or pointer storage; do not hide dictionary
ranking or precomputed inverse-point advice. Table records contain point,h,
scalar label and vector metadata; charge each implemented field-record access.

Maintain S=epsilon*(P0+K), with origin coordinates,h,labels and formal K index.
From canonical h(S), select i=hbar mod8 and set K'=K+epsilon*J_i. Compute
H=h(P0)+h(K')-lambda; orient by H, falling back to y only for H=0.
Use hbar=min(rep(h),rep(-h)); for h=0 use ybar=min(rep(y),rep(-y)).
The control uses the same minimum-y convention. Unique representatives within
each arm justify plus-only label recovery on exact-x equality.
Labels become delta*(a0+alpha_K',b0) modq. Refresh every second transition;
exceptions may refresh early without altering F(S)=can_h(S+J_i).
Candidate DP predicate hbar mod4=0. Control chooses i=ybar mod32,
F_B(S)=can_y(S+J_i), DP predicate ybar mod4=0. Identity precedes selectors.
Exact x is the negation-class equality key in BOTH arms, never h alone.

Batch available regular denominators across current live walkers separately
per arm. Retired walkers reduce actual batch size. Exceptional identity,
K=O, tangent, vertical and H=0 dispatch uses complete formulas with paid work.
All arithmetic already done for a synchronous batch counts even if processing
outputs in ascending walker index finds a scalar before its last output.
Commit each output only when processed in that order. On success, unprocessed
outputs remain paid batch overshoot; their walkers retain pre-batch committed
states for terminal checks. Report the overshoot count explicitly.

## Detection and stopping

Each walker has an8-state ring, initially including its start. Candidate ring
contains hbar, labels and private sufficient deferred x descriptors (immutable
origin/table coordinates and slope, or paid cached x). h matches trigger exact
x reconstruction/comparison, including false matches. Cache only after paying.
Control ring stores exact x and labels. Include scans, updates, descriptor copies
and overwrites in cost/memory accounting. An exact repeat attempts recovery;
null repeat terminates this walker permanently. Do not replace cycle policy
with uncharged doubling, adaptive jumps, or a complete visited dictionary.

Each arm also owns a512-bucket chained DP table, initialized and paid. Per-curve
hash stream draws a=1+draw(p-1), b=draw(p); bucket=((a*x+b) modp) mod512.
Charge field/integer operations, head initialization, chain reads/comparisons,
and record writes (x,a_label,b_label,next). No bucket-uniformity claim.
Duplicate identical labels need not be inserted. DP x collision attempts scalar
recovery; zero denominator is null, not successful. Exact same representative
gives (a1-a2)/(b2-b1) modq; verify every proposed scalar by paid multiplication.
Identity with b!=0 gives -a/b; b=0 is null. No target secret read by recovery.
Ring-null retires; DP-null continues scanning the ENTIRE bucket and does not
retire the walker. Suppress identical-label duplicate insertion after the scan.
If exact equality with nonzero denominator yields a scalar whose verification
fails, treat this as fatal correctness mismatch, not an ordinary failed trial.
Process initial states in walker order through the same identity/DP rules.
For each subsequent output: identity, ring scan/recovery, then DP/recovery,
then ring insertion if still live. Stop arm at first verified scalar, all four
terminated, or32 rounds. Remaining work is neither inferred nor extrapolated.

## Independent validation and cost outputs

Maintain full-coordinate reference for the SAME h-canonical candidate F, using
full addition and propagated h, then compare every completed candidate output
and labels. Reference cannot supply any coordinate/cache/history to the solver.
Candidate materialization for validation is read-only with a separate ledger;
it must not cache or otherwise save future solver work. Independently binary-
Miller-check each start, first completed transition of EACH walker, and every
terminal state; verify terminal labels. At successful stop, all initialized
walker terminal states are checked. Include paid direct identity/tangent/
vertical dispatch checks, report actual nonidentity H=0 coverage (possibly none).
No coverage claim for an unobserved branch and no manufactured fixture.

Report separate vectors for setup, starts, regular steps, refresh, exceptions,
false-h screens, DP, labels, verification and failed-walk work. Expanded inverse
M/S work plus a SEPARATE abstract-I projection must not double count. Include
both Fp and scalar Fq recovery inversions, distinguished by domain or an explicit
common modular-RAM convention. Completed inversions alone may be replaced in
the abstract-I projection: a cap-interrupted inverse retains all raw paid work
and an unfinished marker, without subtracting it or inventing a completed I.
Attributing shared setup to per-target sheets is counter-only reporting, not
another m.tick or actual execution; actual-global work counts it exactly once.
Include
explicit field-record reads/writes: H018 fixed-attribute administration does not
measure this. State the register/record model and charge implemented accesses.
Report table/ring/DP widths, occupancy, peak modeled payload, not Python heap.
Shared curve setup is actually computed once where declared, but FULL setup is
attributed to each single-target sheet; show actual two-target amortization only
for completed cases and actually shared work. Preserve all failed/partial work.

Reference/certification/Miller diagnostics remain in the global cap and separate
from solver comparison. Wall time is diagnostic, not a256-bit benchmark.
For completed cases show actual first-verified-stop vectors and symbolic
weighted inequality. Kernel-normalized credit is separate from complete work.
Finite loss rejects only that configuration/prices; finite pass proves neither
iid stopping, asymptotics, hardware prices, nor improvement over optimal rho.

## Integration gate

Writer owns only c2_probe.py, no execution/import or edits elsewhere. Reuse
H028/key_probe.py and H018/bm_probe.py definitions by deferred import inside the
eventual execute entry, preserving their hashes and making cap override explicit.
Do not run either old experiment or H028/fixture_probe.py. Root records hashes,
static-source review and exact admission before sole command:

    timeout 60s python3 -B research/experiments/H030/c2_probe.py --execute > research/experiments/H030/c2_result.json

Source-only AST syntax parsing is permitted; numerical selftests are not a
source check. Cap/error output must be valid partial JSON when inner guard can
handle it; outer kill is retained as such, without inventing missing results.
No Lean claim or new audit entry until a focused theorem is actually proved.

## Independent cost-review clarifications (native Sol, before execution)

Use phases identifying fixture, case, owner and operation. Failed-walk work is
a terminal classification of already paid work, not another additive category.
Refresh/exception subtotals must not overlap when summed. Keep Fp kernel costs
separate from Fq label arithmetic where possible. Raw actual-global events,
attributed per-arm sheets and diagnostic verification are distinct layers.

Logical transfer model: fetching a record pointer is an array access; loading
its named fields into registers charges field-record reads. Reuse those local
registers administratively. A flat field-array read already charged as an
array_read is not charged twice for the same access. Charge solver-record
construction, copies and cache writes consistently for BOTH arms. This is not
a hardware/cache traffic measurement. Diagnostic trace export is separate.

Candidate pays eight required jump constructions, h propagation,145 table
records/metadata,h(G), and each h(Q). Control pays32 ordinary jump constructions
and y orientation, no h apparatus. Shared point-only setup must have its own
actual measured snapshot; do not infer it by undocumented subtraction from
combined h construction. Applicable jump/hash/start-label sampling is solver
setup. Harness kG and certificates are diagnostic. Answer verification needed
for acceptance is solver work; extra reference/Miller checks are diagnostic.

Peak logical payload includes live immutable origins retained by ring
descriptors, table metadata, cached x, labels, bucket heads, DP records and
batch scratch. Report reference storage separately and combined diagnostic
payload, with a word-width convention. Do not label either Python heap bytes.
