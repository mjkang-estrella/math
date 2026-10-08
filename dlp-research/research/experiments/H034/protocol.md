# H034 C4-free finite diagnostic: protocol v2 for source construction

2026-10-08. Source construction admitted after independent native Astra mathematics
and Factory Fable5.1 cost reviews, with root amendments below. Numerical execution
is NOT admitted; a separate source audit is required. Root corrected Astra's
addition-count recommendation and did not accept Fable's per-block alternation.
The original per-index interleaving remains fixed. Root integrates Sol design.
Question: does a concrete C4-free paired-sum solver implement its stated finite
correctness and complete operation ledger? This is not a speed experiment,
grumpy comparison, small-margin statistical test or asymptotic proof.
No C4-light variant is implemented in this diagnostic.

Scope qualification: small-fixture seed collisions will frequently end the solve
before leaf search. In the ideal IID-root model the exact probability of reaching
the leaf phase is product_(j=0)^(n-1) (q-1-2j)/q, n=2ell², after excluding the
Q=O shortcut; zero if n>(q-1)/2. These are model probabilities, not predictions
for the fixed PRNG seeds. The review's numerical rates are rough and unvalidated.
The run primarily tests setup/seed/dispatch correctness and paid batch arithmetic;
leaf archive/recovery is tested on sampled cases ONLY IF REACHED. Record that
boolean. Seed-only cost vectors are retained but cannot support a candidate
improvement headline. This limited, cheap falsifier is worth the bounded run;
it does not test the asymptotic constant or replace a later surviving full-size
cost argument. No claim that a larger fixture must exceed the cap is accepted
without its actual static ledger.

## Inputs, limits and immutable order

Use these public synthetic fixtures(p,A,B,q,Gx,Gy), in order:

    (59,28,27,73,34,35)
    (101,2,31,103,0,43)
    (251,1,4,271,0,2)
    (8191,1,5,8053,0,789)

For each fixture, pay exact primality checks of p,q, nonsingularity, membership
of nonidentity G, and fresh [q]G=O validation. Prime q then certifies G's order.
No fixture discovery, replacement curve or solver inverse table. Certification
is harness work separately attributed, but consumes the global resource cap.

One aggregate1,000,000-event cap,55-second internal work guard, outer60s. No cap
reset between checks, fixtures, targets, arms or fallback. No warmup, selftest,
module import with numerical side effects or trial execution before admission.
One future command only after independent static source/protocol review:

    timeout --signal=TERM --kill-after=2s 60s python3 -B research/experiments/H034/c4_probe.py --execute --output research/experiments/H034/initial_results.json

The source is standalone: no numerical support-module import. Refuse execution
if the output path already exists. Inner cap/guard exceptions must write valid
partial JSON through try/finally; record which guard fired. External SIGTERM
with absent/invalid output remains inconclusive, with no second run. Source,
protocol and interpreter metadata/hashes are retained. One event is one declared
metered modular-RAM primitive; the source must list primitives before review.

First perform the paid primitive checks below in fixture order. Then test
Q=O,G,-G on q73 through candidate and primary baseline, reported as explicit
diagnostic cases, never mixed into sampled averages. Then process each fixture
with seeds7,19. Harness draws k in[0,q), INCLUDING0, constructs Q=kG and passes
only E,G,Q to arms. Each case runs candidate first, then controls in the fixed
order below. The harness's k never enters either solver or its helper arrays.

Use H030's reproducible LCG: state=(1664525*state+1013904223) mod2^32,
word=state xor(state>>16), initial state=(tag xor p xor q xor seed) mod2^32.
Reject word>=2^32-(2^32 mod n) to sample[0,n), then reduce modulo n. Fixed tags:
target0x54415247, labels0x4C414245, hash0x48415348, fallback0x46414C4C.
Every arm restarts and pays its own hash stream with tag xor arm_id:
candidate0, the six ordered controls16..21, candidate fallback1. The initial
state uses the case seed. Sample eta=1+draw(p-1), zeta=draw(p). Label stream
uses the case seed; draw a then b for each vertex in increasing index order.
Candidate fallback draws R=draw(q) from its separate case-seeded fallback stream,
then constructs its baseline hash stream with tag xor1.
Record streams and seeds. This is deterministic reproducibility, NOT evidence
that the theoretical IID probability law is instantiated. No awkward outputs
are resampled except the explicitly declared unbiased integer rejection rule.

## Candidate state machine

Use H034-finite-contract.md: Emax=ceil(3sqrt(q)/2), least prime ell>=2 with
4ell^6>=9q, 2ell² roots, exact affine-plane graph indexing, lexicographic edge
order, plus output before minus, and edge batches of at most ell. Compute
integer roots, primality search and indices with expanded charged operations.
Emax is the least integer E with4E²>=9q; D is the least integer with D²>=2q.
No floating-point roots determine these ceilings.

Expected fixture parameters, checked at runtime without substituting for the
paid calculation: (q,ell,n,Emax,U,Hc,D,last_index) =
(73,3,18,13,26,16,13,7), (103,3,18,16,32,16,15,8),
(271,3,18,25,50,32,24,12), (8053,7,98,135,270,128,127,64).
Orient every edge from point vertex i=x*ell+y to line vertex j=ell²+s*ell+t.

At input dispatch, check ONLY Q=O; verify and return0 if so. G and -G are test
cases, not additional shortcuts. For every other input, sample all root labels
(a_i,b_i) and construct ALL roots before processing any seed event. No early
setup exit based on a zero/collision. This fixes the previous timing ambiguity.

Paid seed routine: construct powers G_j=2^jG and Q_j=2^jQ for every q-bit
position. For each root scan all positions in increasing order, adding selected
G_j then selected Q_j to an accumulator with ordinary complete affine addition.
Pay power construction, arrays, bit tests, reads, identity branches and additions.
Powers are solver preprocessing, not advice, independently rebuilt per target.
Release them after all roots have been constructed, paying declared release.

Scan roots in vertex order, infinity before exact-x seed lookup. A zero root
with nonzero b proposes -a/b, which must verify; a null zero root triggers
fallback. On first seed-x match try signed recovery; success stops, otherwise
fallback immediately. Do not continue after a null seed match. The seed index
stores exact x and root index, with explicit hash chains and paid initialization.
Use Hseed=pow2ceil(2ell²) heads; reuse the candidate's independently sampled
eta,zeta with modulus Hseed for this exact-x index. Allocate its declared capacity
before the scan. Sharing hash parameters does not select seed outcomes by hash:
only exact equality/infinity determines algorithmic stopping. Resource caps
are still separate censoring. Free it before leaf processing; retain full root coordinates/labels. Helpers
and seed keys are never queried against the leaf archive.

Reaching leaf phase therefore certifies finite roots with pairwise distinct x.
All simple-graph edge denominators are nonzero and both signed outputs finite.
Check this invariant defensively before batching. A violation in the actual
leaf phase is an implementation failure, not silently repaired evidence.
General tangent/vertical/identity branches are exercised separately below.

For an ordinary batch of b edges, exact coordinate boundary is

    (5b-3)M + 2bS + 6bA + I,

where the inverse is symbolic at that boundary but also fully expanded in the
raw ledger. For each edge form denominator xi-xj; numerators yi-yj and yi+yj;
shared sum s=xi+xj; and outputs slope_plus²-s, slope_minus²-s. That is exactly
six field additions/subtractions per edge. Two successive coordinate subtractions
per output would instead give seven and do NOT implement this exact subtotal.
Empty batches perform no inverse. Finish and pay all batch arithmetic before inspecting outputs.
Inspect in exact edge/sign order; no hash/query/insert of later outputs after
the first equality. Already generated outputs remain charged as overshoot.

Archive capacity U=2Emax, exact x/edge/sign/next records. Hc is the least power
of two >=ceil(sqrt(q)); hash ((eta*x+zeta mod p) mod Hc) with sampled eta!=0.
No hidden Python dictionary performs solver lookup. Explicit prepend-and-scan
chains charge every head/node access, comparison and insertion. Sample and pay
fresh hash parameters at startup. No truncation or unverified fingerprints.

For a leaf with sign e, recover labels(A,B)=(a_i+e*a_j,b_i+e*b_j) from its edge
descriptor. Given equal x keys with labels(A,B),(A',B'), try sigma=+1 then-1:
d=B-sigma*B'; skip d=0; otherwise propose (sigma*A'-A)/d and verify against
original Q. Wrong-sign verification failure is expected. First geometric match
with neither verified orientation goes to fallback, not a later match search.

On declared algorithmic failure or edge-cap exhaustion, release all candidate powers/index/roots/archive/scratch after
preserving administrative evidence; independently sample R, compute Q+RG, and
run primary H019 control with its own setup. Return d-R only after verifying
original Q. Failed candidate work and release count in that same solve. Fallback
shift0 is allowed. Resource-cap exhaustion is censorship, not algorithm fallback.

## Predeclared H019 controls

Use repaired contiguous-prefix generation from H019-xonly-baseline-screen.md,
D=ceil(sqrt(2q)), baby and giant indices0..ceil(D/2), inspected alternately.
Give each control the same Q=O input dispatch and verification. Full centers
with side abscissae only; complete paired inversion batches paid.
Center indices ellH+j*(2ellH+1), advance stride k*(2ellH+1). Generate blocks
on demand; no advance after final termination and no query of out-of-cap indices.
Charge all initialization, exceptions, final-batch waste and verification.
Buffer each generated block into INCREASING scalar-index order, including its
centers' own keys; inspect baby i then giant i, before i+1. Last requested blocks
generate all configured outputs and pay for discarded out-of-cap keys, which
are never queried or inserted. Advance centers only when the next block is
actually requested. Baby index0 is O: skip it as an archive entry, not a target
solution. Giant Q-jDG=O proposes jD and requires verification. These branches
remain role-specific.

Two fixed arithmetic configurations avoid restricting every control to ellH=1:

    q73,103:  (k,ellH)=(2,1), then(1,2)
    q271:     (4,1), then(2,2)
    q8053:    (8,1), then(4,3).

For each configuration test total split-role head counts Hc,2Hc,4Hc, in that
order. This small grid is not claimed optimal. Omit any control whose DECLARED
full lifecycle logical packed peak exceeds the candidate's declared peak;
report the capacity calculation, never use a target-dependent observed peak.
If primary configuration at Hc does not fit, invalidate the comparison instead
of inventing another fallback. Primary fallback is the first configuration/Hc.

Each control independently pays setup and owns its tables, hash, powers and
scratch. Half the heads serve each role; one hash value can index either role.
Query opposite role, then prepend own role, charging both head accesses. Exact
x matching recovers jD+i or jD-i and verifies against Q. Infinity gets explicit
direct recovery before hashing. Within-role repetitions do not act as cross hits.
Run all admitted controls separately; their observed lower envelope is descriptive,
not a secret-dependent executable choice. No baseline tuning after results.

The sole preregistered primary comparison is first arithmetic tuple at Hc;
the other five results are descriptive controls, not an online min-of-six policy.
For total Hb heads, slot=(eta*x+zeta mod p) mod(Hb/2), with a fixed role offset.
Check regular components for BOTH solvers: side batch of b pairs is
(5b-3)M+2bS+6bA+I; full affine advance batch of b regular additions is
(5b-3)M+bS+6bA+I. Check actually executed complete regular components, separately
from exceptional dispatch. H019 ellH side rounds plus one advance reproduce
the block subtotal only when that advance is actually executed. Do not charge
or assert an unperformed final advance. Empty components have zero inverse cost.
Subtotal mismatch is fatal for either solver.

## Paid correctness checks and information separation

For each fixture, construct one ordinary paired batch of size ell on public
pairs((i+2)G,G), i=0..ell-1. Check all source denominators before the subtotal;
if an expected regular case is not regular, record invalid diagnostic setup.
Cross-check every signed output against ordinary full affine addition. Also
exercise O support, the pair(G,G) tangent, the pair(G,-G) vertical, and signed recovery
whose first denominator is zero: Q=2G with labels(-1,1),(-3,1) gives G,-G;
the second orientation must recover2. Exercise null zero label and identical
labels as recovery-dispatch checks. These public diagnostics are not root
samples, solver advice, extra detectors or evidence of naturally reached branches.
On q73 also invoke the standalone fallback component once on public Q=2G with
seed7, recording it as a diagnostic forced invocation, not a natural candidate
failure. Pay shift, independent primary control setup, solve, unshift and verify.
This guarantees the wrapper is checked without modifying IID-labelled solver
root samples. No output or setup from this check is reused by later cases.

Also check an ordinary full-addition batch for each distinct control k on public
pairs((i+2)G,G), paying construction/reference verification. This exercises the
control's advance boundary even if actual blocks encounter exceptions.

Independently check generated leaf x values against ordinary full affine addition
in a reference-only phase. Never feed reference coordinates to solver state.
Place checks so all prepaid outputs are checked even when lookup stops early.
Reference work consumes the global cap but is separate from solver cost sheets.
The reference checker uses immutable copies of public/root coordinates and edge
descriptors, returns pass/fail only, and writes nothing to solver state. Complete
prepaid reference validation before inspecting that batch's lookup results.
No cache sharing: harness powers and reference points never supply solver
preprocessing; each arm rebuilds D*G, strides and power arrays. Defensive regular
denominator checks belong to each solver's ledger; the independent full check
belongs to the reference ledger. An invariant mismatch is fatal in either.
Verify each final scalar inside the solver against Q, then compare with private
harness k. Append state/pending markers before work so interruption is retained.

## Complete ledger and interpretation

Use the SAME expanded inverse routine in Fp and Fq for all arms: Fermat
exponent modulus-2, left-to-right binary exponentiation from accumulator1,
square at each bit and multiply on a1 bit. Zero inverse is invalid. Primality
was separately validated. No builtin pow, modular inverse or hidden table.
Expand field inverse/power loops and scalar operations; report raw Fp/Fq M,S,A,
integer operations/branches, RNG/rejection, indexing, field-record access,
allocations, initialization, head/node accesses, chain probes, exact matches,
descriptor decode, verification, clearing/release and fallback. Count only
COMPLETED symbolic inverse boundaries and their observed expansion, so an
interrupted inverse is never subtracted from a cost projection. No GPU rates.

Separate harness certification/input/reference sheets, each complete arm's
single-target work, candidate setup/seed/leaf/fallback, and administrative output.
All computational sheets consume the single global cap. A fixed-schema register
assignment and instrumentation bookkeeping may be administrative, but dynamic
array/container work is charged. Document the exact modular-RAM primitives;
they are not binary-tape steps, calibrated CPU cycles or uniform bit operations.

For logical memory, use actual rounded bit widths, including null-pointer codes,
and declared capacities for every power/root/label/scratch/index/head/archive
stage. Include full center and output buffers. Explicitly mark unused payload
as uninitialized if that is the implementation; otherwise count initialization.
Report this packed-payload MODEL separately from measured Python-object storage;
neither is a hardware-traffic benchmark or proof of an implemented bit layout.
The matched-peak filter refers only to the declared logical model.

Before the first solver arm, emit a per-fixture declared-capacity table and all
control omission decisions, calculated from public parameters only. Show root/
power/seed-index stages, leaf root/archive/head/scratch stage and fallback stage;
do not force non-overlapping arrays to coexist. Reserve node payload uninitialized
for both arms, but pay capacity reservation/allocator slot initialization actually
performed, plus every head zero. Release explicitly walks each allocated live
array/container slot and charges its release; no O(1) release on only one side.
Report actual lifecycle differences, including uninitialized payload. Python
storage observations may be approximate; claim neither exact allocator peak
nor hardware bytes from packed counts. The writer must supply static stage-event
estimates before execution review, without trial runs or post-result retuning.

Retain source/support/protocol hashes, cases, streams, pending operation, per-stage
counters, peak components, terminal reason and elapsed guard evidence. On cap,
keep completed arms, mark active arm incomplete, later ones untested. No retry,
resumption, replacement seed or cap reset. External timeout/invalid JSON is
inconclusive and preserved, not an implicit authorization for a second run.

Wrong scalar, reference mismatch, lost equality, wrong exception dispatch or
regular-subtotal mismatch falsifies the implementation/ledger. Finite vectors
quantify startup dominance; classify input/seed-only/leaf/fallback outcomes.
Seed-only successes do not validate the leaf Poisson law. At q8053,98 eager
roots may exhaust the cap; no promise all eight sampled cases finish. A finite
loss can reject that tested configuration's gain claim, not the asymptotic
hypothesis. A favourable vector does not prove physical speed or improvement
against all baselines. Verified improvement remains NONE until separate evidence.
