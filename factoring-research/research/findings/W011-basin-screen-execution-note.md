# Frozen execution details

The complete parent preregistration is preserved in the adjacent preregistration
file. This note resolves implementation details without changing its parameters.
Only the W011-basin-screen prefix is owned. The shared research loop and check.sh
would run additional experiments/builds and create files outside that prefix;
the user's narrower scope takes precedence. They are not run here. No packages,
shared solver changes, Lean changes, STATE edits, commits, or publication.

Freeze source, configuration, this note, preregistration and instruction snapshots
before any check. One fixed correctness check uses p=5,q=7,a=2,N=35 and exactly the
registered ten depths. Exhaust all 35 CRT seeds for direct gcd stopping and map
update counts; compare exact probabilities to formulas (3)-(5). Exhaust all local
seeds to compare direct orbit first-hit histograms to reverse BFS. This is one
instance, not a parameter search. No parameter tuning follows it.

The main supervisor starts a monotonic 60-second deadline before writing the
schedule or starting its worker. Prime search and the single N-only draw per
parameter are inside that deadline. The worker checks the same absolute deadline
throughout setup, graph construction, BFS and depth evaluation. The supervisor
uses subprocess.wait(timeout=remaining_time) and immediately kills its sole worker
on expiration. Output finalization after the worker exits does no new map/prime/
parameter work. OS scheduling and the bounded kill/reap cleanup may finish just
after the 60-second boundary; exact wall times and timeout statuses are retained.
No retry, continuation, replacement seed or additional main run is permitted.

Order: b ascending, then seeds 0..15, then one cubic C control per pair. Every
scheduled case/depth is recorded before worker setup. A full gcd in a chart does
not prevent checking later chart entries; only a proper factor stops those checks.
A clean chart computes the coefficient modulo N before diagnostic reduction at p,q.
The cubic control has coefficient zero and no parameter chart or sampling.

Each reverse graph includes every field element, including zero, targets and
all exceptional/colliding roots. Separate BFSs start from +1 and -1; their exact
first-hit histograms must agree. Full histograms, never-hit counts and positive-
time basin counts are retained, even if no non-target ever hits. Every specified
depth is reported, including zero success (null proxy with an explicit reason).
Probabilities and expected updates are rational with exact integer numerators.
The normalized proxy is a descriptive float; qualification uses the exact integer
comparison 16*proxy_numerator^2 <= p*proxy_denominator^2. Ties choose smallest k.
The endpoint probability and the stopping law both include full-gcd failures.
The additive 1 in the proxy is the registered optimistic setup placeholder,
not a measurement or a full cost account.

An append-only, fsync-per-event journal preserves setup, started cases, each chart
check, sampled a, coefficient, each local histogram, each completed depth, terminal
statuses, exceptions, and deadline events. The schedule preserves all 85 cases
and 850 case-depth slots. Final case/depth JSONL includes chart-not-applicable,
failed, timed-out and unstarted slots, including partial completed depths.
Unexpected per-case errors are recorded and not retried; the remaining fixed
schedule runs only while the original deadline remains. A fatal worker error
ends the diagnostic. Incomplete primary parameter analyses (deadline or error)
make the screen INCONCLUSIVE; a completed primary pair with fewer than eight
qualifiers is REJECTED if both primary pairs are completely accounted. Control
failure is reported separately and never supplies a qualifying parameter.

The report and delivery manifest are post-run summaries of retained records.
They do not execute new or extended diagnostics. Hash verification is read-only.
The freeze manifest hashes all source/configuration inputs; the final manifest
hashes every delivered prefix artifact except itself, to avoid a self-hash cycle.
