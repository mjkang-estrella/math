# W032 lift-sweep assay audit

**Accept the two completed finite negatives, with a minor terminal-record
attribution defect disclosed below. The three-group pilot is incomplete:
b=17 stopped in diagnostic setup and is not an exhausted or failed lift
family. Verified complete factoring improvement: NONE.** No arithmetic-meter
undercount or mathematical implementation defect was found in the inspected
source. This is static review plus file-integrity and stored-record inspection;
it is not numerical replay or an independent recalculation of the results.

The full assignment is frozen in [brief.txt](W032-sweep-assay-audit-evidence/brief.txt).
The [input manifest](W032-sweep-assay-audit-evidence/input-manifest.json) records
51 immutable audit snapshots, including the complete assay package, report,
protocol, governing documents, and the two accepted mathematical reviews.
All 562 lines of `assay.py`, 59 of `run_once.py`, and 152 of
`evidence_admin.py` were read. The full assay report, protocol, sweep target,
assay-frozen exact-quotient note, METER, configuration, manifests, runner
status, prior ledger audit, and both mathematical review reports were read.
[Read scope](W032-sweep-assay-audit-evidence/read-scope.json) distinguishes these
reads from excerpts and structural processing of the large datasets.

**One journal defect; no evidence was repaired.** In
[frozen assay.py](W032-sweep-assay-audit-evidence/inputs/research/findings/W032-lift-sweep-assay-evidence/assay.py)
lines 550–551, the final loop records each group without resetting
`meter.group` or `meter.phase`; lines 47–48 write those active values into
every envelope. Consequently records.jsonl lines 1177 and 1178 label the
b=9 and b=13 terminal payloads as outer `group=17`,
`phase=diagnostic_prime_generation`. Line 1179 has that same envelope for
the actual b=17 payload. All three are emitted at global event count 20,000.
Their nested `result.b` values are respectively 9, 13, 17, and their complete
nested objects equal the corresponding `status.json` groups byte-for-value
after JSON parsing. The earlier completed-group records also equal status.

Thus all terminal outcomes survive, but grouping terminal records solely by
the outer group tag misattributes two completed groups. Consume these final
records by `result.b`; keep the original bytes. This is a journal-attribution
bug, not three lost terminal results or an arithmetic-event accounting error.
The assay's phrase “no source error” is supportable as “no execution failure,”
not as certification that its source contains no defect. The report's retained
outcome and event-count claims otherwise survive this qualification.
[Terminal-attribution evidence](W032-sweep-assay-audit-evidence/terminal-attribution.json)
contains the exact record locations and equality checks.

The initial [structural inspection](W032-sweep-assay-audit-evidence/integrity-and-structure.json)
preserves all 129 checks, including the three failed expectations that each
outer group would have exactly one matching terminal record. Those are three
symptoms of this one attribution defect, not numerical invariant failures.
A separate inspection identified the nested results; neither the original
check result nor any assay payload was changed.

**Freeze and sole-run evidence.** All 35 delivery payloads and all 23 pre-run
payloads match their declared byte lengths and SHA-256 hashes. The complete
delivery file set, its two inventory exclusions, unique manifest paths, both
sidecars, and the frozen input/protocol copies agree. The external anchors
supplied in the assignment match exactly:

- Delivery: `0e0b4a6d60165794ccc1921d30ba3a7f753d5188c1e27bcf023618744eef272f`.
- Pre-run freeze: `8b7387c453d5824d3948d11d9f161c49c6eb64ce67673c5e6e033a3d604a305c`.

The freeze timestamp is 2026-10-09 05:55:04 UTC, before the 05:55:11 UTC
run marker. `run_once.py` creates that marker exclusively, verifies every
frozen payload, and launches one child with the original monotonic start.
The child also exclusively creates its records and terminal files. The runner
and stored transcript record one launch, child exit code 2, and a normal
supervisor completion; no retry path exists. Runner freeze checks equal the
independently hashed files. The preserved stdout and stderr are empty.
This supports the sole frozen run in the trusted-code evidence model. Hashes
and a local exclusive marker are not an independent attestation of every
possible past process or an adversarial execution sandbox.

The runner records 0.2378464009379968 seconds through child termination/output.
The preserved external transcript records 0.23844374401960522 seconds through
supervisor recording, correctly reported as **0.238444 seconds rounded up**.
This audit did not remeasure it. The process starts its timer before freeze
verification, and the child includes setup, controls and logging. A
59-second cooperative gate reserves one second of the 60-second limit for
terminal recording; the supervisor has the overall timeout. The event cap,
not time, ended this run. This timing is for the declared measured interval,
not a benchmark of interpreter startup or post-run audit/report/sealing work.

**Candidate boundary and legal depth.** The fixed configuration selects only
b=[9,13,17], in that order. Diagnostic trial division starts at 2^b and then
at p+2^floor(b/2)+1 for q; no chosen gap or replacement path appears. The
candidate is called with N, the meter and an output state containing only an
initial status. It derives R=ceil(bit_length(N)/4), m=2R+1, L=2R-2 and a0=1
from N and literal public constants. Complete source inspection found no
factor lookup, family-based parameter branch, filesystem/network lookup,
hidden p/q read, or import of older assay code in candidate arithmetic.

The same-process meter carries diagnostic labels and logging handles; this
is a reviewed-code separation, not process isolation. The candidate and its
helpers use none of those labels to choose arithmetic or thresholds. p,q
appear in diagnostic setup and subsequent factor verification/reference
probability only. The candidate's chosen stencil and event generator do not
depend on them.

Lines 180–208 charge depth and endpoint checks, every integer denominator
gcd from 2 through m inclusive, and all m+1 initial-point gcds. This includes
the omitted j=R denominator factors required by the imported truncation
theorem; success of only the shortened recurrence's inverses would have been
insufficient. Nonunit guards are retained with proper/full categories and an
inapplicable sweep/control status, with independent diagnostic factor checks
later. The observed groups use R=5 and R=7. There is no small-tail guard in
this unguarded quotient assay; imposing the separate small-tail depth theorem
would change its scope. R=1 remains a symbolic constant-polynomial boundary,
not an added numerical case.

**Arithmetic meter.** The complete source routes substantial numerical
formulas through the declared wrappers: depth/modulus setup, trial division,
coefficient and binomial recurrences, Horner products, signed quotient sums,
threshold ceiling divisions, range/crossing checks, interval coverage, gcd
classification, direct and scalar controls, and diagnostic probabilities.
Ordinary and modular positive powers use actual repeated multiplies,
reductions, exponent divmod operations and loop comparisons. Pair powers
likewise expand to the five products, two sums and two reductions of each
pair multiplication. No complete polynomial or positive power is a single
event. Stable sort's `__lt__` calls the meter, accounting for 391 and 779
threshold comparisons in the completed groups.

Native `math.gcd` and `pow(a,-1,M)` are declared macro primitives with actual
operand/result widths; their internal Euclidean work is not counted as
separate events. Static range/index arithmetic, containers and distinct-value
hashing, JSON, clocks, width instrumentation, integrity hashes and logging
administration are explicitly outside the arithmetic-event measure. Branches
on already computed booleans/residues do not create an extra comparison
primitive. This accounting follows the declared model and cannot certify
bit complexity. No additional uncharged substantial formula was identified.

All 20,000 event records were parsed, with contiguous IDs, nondecreasing
timestamps, matching operation/phase summaries, and consistent operand and
result width metadata. The maximum is 729 bits. Their vector is 3,864
multiplies, 3,796 additions, 1,716 subtractions, 1,968 remainders, 668 floor
divisions, 441 divmods, 284 gcds, 22 inverses, 2,426 equalities, 2,691 strict
comparisons, 1,472 non-strict comparisons, 434 absolute values and 218
bit-length operations. Setup and all prescribed references share the global
count. The cap check precedes the primitive call, so the next denied primitive
is not evaluated. The terminal-envelope defect does not change these events.

**Precision, recurrence and sign.** The coefficients are computed modulo
M=N^(2R), beginning with 1 and applying, for 1<=j<R,
`beta_j=beta_(j-1)*N^2*((2j-1)^2-N^2)/[4*(2j)*(2j+1)] mod M`.
The denominator is inverted only on the fully checked unit branch. Horner
evaluation is in a² and returns the canonical lower remainder r. Exact
division of r-1 by N² gives u at precision N^(2R-2), not the extra digit of
the full normalized scalar. The divmod extraction returns top digit b and
lower block v in the correct order. The signed binomial weights use
(-1)^(m-i), with first weight negative and last positive; their sum and
weighted affine sum are checked. c0 is obtained as an ordinary signed
integer by both Delta^m r/M and Delta^m u/N^L, with remainder-zero and
agreement checks. No inverse of N or M is used and no negative numerator
is rounded into a purported exact quotient.

The stored stream contains 79 divmod/remainder-equality pairs from exact
divisions, all recording remainder zero and a true check; five have negative
numerators. This inspects existing checks, not their quotient arithmetic.
The accepted mathematical quotient and sweep reviews supply the general
identities. Per the assignment, the parent resolves the sweep review's
historical provisional C_base dependency through the accepted quotient
review. This assay uses Horner and does not implement or benchmark that
theoretical shared multipoint soft O(R² log N) acquisition bound.

**Thresholds, atomic ties and maximal intervals.** Generation covers
k=1,...,a_i and uses the positive integer ceiling
`(k*N-b_i+a_i-1)//a_i`, retaining exactly 1<=w<N. The sorted list is a
permutation of the retained records. Source lines 319–341 collect all equal
thresholds, check each one-step crossing, sum every weight, then subtract
the total once before any next interval gcd. No intermediate tied carry is
tested. The prior interval ends at w-1, and the next starts at w; the final
interval ends at N-1. The no-threshold path also emits its one interval.

Source lines 311–316 merge adjacent equal-c intervals into maximal segments
while retaining original threshold/tie and interval records. Nonadjacent
repeated c values remain separate intervals. The stored threshold order,
tie partition, adjacent old/new values, update-event links, interval
adjacency/endpoints/lengths, total coverage, and maximal-segment records all
reconcile. The 216 recorded interval gcds are linked to their actual stored
gcd events. **Neither completed case has a multi-event tie or zero-net tied
update.** Atomic multi-event handling and zero-net merging are source-reviewed
paths, not numerically exercised paths. No extra case was introduced.

**Controls and finite outcomes.** Direct controls construct the actual
unwrapped inputs a_i+12*N^(2R-3)*w and reevaluate at lower precision. Their
coefficient list, Horner routine and signed weights are shared with the
candidate, as permitted. They check the sweep update independently of its
floor-event formula but do not independently prove those shared components.
The scalar control separately forms (Na+s)^N with s²=(Na)²-4 modulo
N^(2R+3), divides its real part by N² exactly, normalizes by the checked
unit a*(-4)^((N-1)/2) at precision N^(2R+1), and extracts the top digit.
Its ordinary difference table uses neither the polynomial coefficients nor
the candidate weights. The compared residue is **-c0**, with the correct
minus sign. Shared meter/pair primitives and the planned stencil remain
common infrastructure; this is finite control independence, not an
independent general proof.

- **b=9:** stored p=521, q=541, N=281861, R=5. All 78 thresholds,
  79 intervals/maximal segments and 75 distinct carries are retained;
  c0=133, maximum absolute carry width 10 bits. Their lengths cover all N
  parameters, every recorded gcd is 1, and proper probability is 0.
  Direct quotients at 0,1,N//2,N-1 are 133,133,116,133; all four passed on
  all 12 points. The one original scalar control passed on all 12 points,
  recording filtered integer 108798213 and residue 281728=-c0 mod N.
  Its phase has 3,835 events; the whole group has 9,330.
- **b=13:** stored p=8209, q=8287, N=68027983, R=7. All 136 thresholds,
  137 intervals/maximal segments and 130 distinct carries are retained;
  c0=-2252, maximum absolute carry width 14 bits. Coverage is all N,
  every recorded gcd is 1, and proper probability is 0. Direct quotients
  are -2252,-2252,1452,-2252; all four passed on all 16 points.
  Scalar control is correctly not scheduled. This group has 9,989 events.
- **b=17:** the remaining 681 events are all diagnostic prime generation.
  Event 20,000 records the divisor increment 111+2 to 113 while testing
  131093, whose primality was not certified. p,q,N,R are absent. Candidate,
  four direct controls and diagnostic verification are explicitly unstarted
  with the budget reason; scalar control is not scheduled. No family
  probability or candidate failure may be assigned to this group.

All 1,180 records and the complete status object were parsed. The original
three pre-arithmetic plans remain, and complete point/control/interval/tie
records agree with their retained status objects. The two baseline fractions,
1060/281861 and 16494/68027983, are stored analytic diagnostic references,
not random-gcd trials. No proper factor required independent hidden-factor
verification in this run. Source inspection covers proper/full/zero branches,
but those outcomes, guard exits, hard timeout and failed primitives were not
numerically exercised by the completed sweeps. The third stop is censored
setup work, not a zero-cost or negative candidate observation.

**Disposition and limits.** The accepted finite statement is that these
two fixed N,R,a0 families were exhaustively swept without a proper gcd,
subject to the reviewed code, accepted mathematical bridge and preserved
stored execution. The exact failed yield premise is “some attained c has
1<gcd(c,N)<N” for each of those two families. The incomplete third group
remains in the planned pilot without an invented factor-yield outcome.
The terminal metadata issue warrants this qualification, not a repair-run
or rejection of otherwise reconciled finite arithmetic results.

The accepted mathematical consumer can compress one supplied family at its
stated fast-arithmetic cost; this record-rich Horner diagnostic establishes
neither that implementation bound nor any success law. No factoring-time
improvement, general failure theorem, independent-trial model, fitted
exponent or novelty claim follows. A useful-supply or cover theorem for a
specified paid N-only schedule could change the general conclusion. The
separate live arrangement review and further construction are parent-owned
and were not duplicated or used to enlarge this audit.

No assay source was imported or executed; no candidate arithmetic, prime or
gcd result was recomputed. Only byte integrity, metadata widths, record
counts/links and stored interval coverage were calculated. There was no
retuning, repair, extra case, delegation, installation, commit, shared-code,
Lean, STATE or registry edit, or project-check invocation. The parent owns
`scripts/check.sh`. Only this report and its assigned evidence directory
were written. [Activity record](W032-sweep-assay-audit-evidence/activity-log.md)
and the preserved inspection scripts make the administrative work reviewable.

The [delivery manifest](W032-sweep-assay-audit-evidence/delivery-manifest.json)
seals this report and every audit payload, including all nested original
manifests, with paths, sizes and SHA-256. Only this audit's own manifest and
[terminal sidecar](W032-sweep-assay-audit-evidence/terminal-manifest.sha256)
are excluded to avoid circular hashing. An external terminal SHA-256 check
anchors the manifest in the handoff. No payload changes follow that seal.
