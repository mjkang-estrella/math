# H001: user-directed algorithm refocus and first decision gates

Date2026-10-08 UTC. Verdict: operating correction implemented; algorithmic
hypotheses remain unverified. Verified improvement over the accepted baseline:
**NONE**. No new classical hardness bound or calibrated hardware claim.

## Why the work changed

The user explicitly corrected drift toward word-machine/query proof machinery.
Root stopped both writers, collected their actual last verification status,
parked exact snapshots with hashes and unresolved obligations, and rewrote
RESEARCH_LOOP.md, RESEARCH_TEAM.md and STATE.md around algorithmic hypotheses.
No infrastructure draft was discarded or adopted as a result. Existing goal,
coordinator and committed library remain; no duplicate scheduler/coordinator.
The archive README records the failed coordinator spec draft as failed.

The prior committed363 audits and finite query runs are support metadata. They
are not evidence of a changed ECDLP complexity or complete solver-work estimate.
The unchanged committed library check passed after parking; no extra machinery
was developed or tested to improve an infrastructure metric.

## Ranked hypotheses and threshold arithmetic

H001-algorithm-shortlist.md gives three concrete investigation slots and cheap
falsifiers. Native Sol explores an actual coordinate-aware relation generator;
native Astra explores complete-work quotient-rho scheduling; T3 Opus independently
challenges the shortlist. Exact task IDs are in STATE.md. Each is read-only with
bounded temporary tests; root alone integrates/commits.

For the first candidate, take the historical conditional Semaev model with
B≈q^(1/5+δ) and total work tB+B². If t≈q^a, the exponents are
`a+1/5+δ` and `2/5+2δ`. A fixed exponent gain requires **both** below1/2 by a
fixed positive margin. Thus δ<1/20 and a<3/10-δ are necessary in that model.
An unexplained fast root oracle cannot discharge the first inequality.

For example, an algorithm that actually spends B² **per retained relation**
has tB=B³≈q^(3/5+3δ), already losing to the square-root reference. This does
not reject every pair-table approach: reusable preprocessing must be charged
once and amortized honestly, while relation yields, rank, failed trials and
lookup work are counted. An alleged coordinate bucket filter must demonstrate
both pruning and retained relation probability; EC coordinates are not assumed
to be an additive representation for generalized-birthday algorithms.

The second candidate must pay for every micro-step between collision-observation
boundaries. A valid macro map alone does not imply that interior orbit collisions
merge walks or preserve the original collision rate. Its promised saving must
be evaluated against the best applicable known automorphism-aware baseline.
The third candidate, GLV-only exponent reduction, supplies no new information
about unknown joint coefficients; it is a quick obstruction check, not a new
experiment or discovery.

These are analytic gates, not experimental results or unconditional lower bounds.
Prior sources are identified in the shortlist; delegates must refresh primary
literature before any novelty claim. A historical missing algorithm is not proof
that no later algorithm exists.

## Current five-item wave report

- Best supported working estimate: generic square-root classical work with known
  automorphism constants, subject to their models and costs; no demonstrated
  coordinate-specific reduction and no validated GPU curve-work rate.
- Verified improvement: NONE.
- Hypotheses: explicit prime-field relation generation; complete-work quotient
  walk scheduling; GLV-only exponent objection.
- Evidence: independent Opus review completed and delayed-canonicalization
  arithmetic reproduced. Raw critic assertions are separately qualified, not
  automatically adopted. Coordinate relation-generator exploration remains active.
- Next decisive action: reject candidates whose actual steps already exceed
  the threshold; only an explicit surviving mechanism earns matched seeded
  synthetic scaling/correctness tests. If all lose, retain negatives and choose
  genuinely different mechanisms, without returning to generic infrastructure.

## Reproduction and preservation

Root used byte-for-byte renames into research/parked/20261008-query-infrastructure
only after author checkpoint reports. Hashes and last statuses are retained in
its README. `./scripts/check.sh > /tmp/ecdlp-refocus-check.log 2>&1` exited0 after
parking. This check validates preservation of the existing accepted library,
not a new algorithmic advance. Working tree paths are explicitly inspected before
local commit; unrelated research-monitor/ remains untouched.
