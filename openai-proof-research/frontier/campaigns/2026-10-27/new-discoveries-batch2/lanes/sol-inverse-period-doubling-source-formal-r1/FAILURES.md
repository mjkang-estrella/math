# Preserved failures and limits

All attempted Lean invocations retain numbered .log and .guard.json files.
Failed source snapshots where captured are retained as failures/*.lean.txt and
are excluded from compiled modules and the source-only archive.
Initial broad Mathlib.Tactic import exceeded RSS2800MiB and was removed.
Initial Audit import Lean also exceeded RSS2800MiB; removing that broad import
allowed the identical audit operations using already imported elaborator support.
Neither cap was raised. Intermediate proof failures include deprecated if_* names,
unused simp arguments, coefficient-shift normalization, definitional arithmetic
normalization for omega, a Fintype deriving-handler failure (replaced by an explicit
finite instance), and a successor rank rewrite. Failed attempts never supplied
certified declarations to the fresh replay.

Protocol defect: the first line-level valuation search exposed declaration names
and a deprecated wrapper before that additional file's local freeze. It was then
frozen, read in full and bound by original/copy hashes before implementation.
The tactic Ring wrapper was imported before its additional explicit local binding;
the selected 42 pre-reviewed library bindings and the primary bodies had already
been verified. These timing defects are recorded rather than claiming perfect
freeze-before-any-inspection compliance. No original scientific file was edited.

No new network retrieval. Reused actual JIS2018 proof bodies, Proposition10 pp9–10,
Table1/Proposition16 pp13–14, and Problem27 scope via independent review.
No denied GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge route
was retried; no historical HEAD loops, proxy, TLS disabling, or browser bypass.
Novelty remains HOLD: unread Merta2017 thesis and unavailable current proof-registry
head remain substantive gaps. No worldwide priority or current-registry clearance.

Item4 extrema/threshold/record induction is not closed by this component.
No full nonregularity claim, Lean source theorem for that endpoint, manuscript,
shared-file change, public action, git action, child agent, or acceptance/count change.

The first final verifier failed its overstrong assertion that every generated partial
implementation was axiom-free. Audit inventory already recorded the correct result:
suffixValues._unsafe_rec uses the three allowed axioms; the other three use none.
The documentation and verifier assertion were corrected; proof sources/archive unchanged.
The failed verifier source is retained in failures/verify-01.py.txt.
