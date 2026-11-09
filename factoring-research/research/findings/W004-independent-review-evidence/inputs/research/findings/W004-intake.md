# W004 — coordinator intake of the completed construction

2026-10-08. **Submission received; new deductions UNACCEPTED pending a new
independent review.** Verified new complete factoring improvement: **NONE**.

The constructive task `factoring-w004-biquadratic-construction-r1` is completed,
with result available and no pending child runs. The coordinator read all
385 lines of the final [main report](W004-biquadratic-construction.md), all
127 lines of the [reciprocal supplement](W004-biquadratic-reciprocal-packets.md),
all 69 lines of the [test proposal](W004-biquadratic-test-proposal.md), the
source notes and source identity ledger. This supersedes provisional draft
reading, not the independent review still required.

All 13 original input snapshots, three appended input snapshots, 11 source
identities and 36 delivery entries verify against their recorded hashes and
byte counts where supplied. Only the mutable STATE original differs from its
initial frozen copy. Original reports, supporting evidence and manifests are
unchanged. Byte-identical main report, supplement and test-proposal copies
are preserved under [W004-submitted](W004-submitted/W004-biquadratic-construction.md).

| Artifact | SHA-256 |
|---|---|
| Main report, 21684 bytes | `9957b2368caa91ba3261bcef7d7b2f33b392c931d2744c2536906d55ad7132e9` |
| Reciprocal supplement, 6769 bytes | `a520c469b3e4c635500916bd952fd9fa6eaf1126a0bb827c8c0038fd25e56764` |
| Test proposal, 4238 bytes | `5456e113dc6f2318b3d97e105032a63e80d1630f5e7011781eca690d0a693eba` |
| Original delivery manifest | `a2d7b693d7d9b5f738b95cad25f3f377cee4f4e3dd2219e7af04744dcd37ca0d` |

## Claims and missing step to review

The report checks the auxiliary-prime/CRT construction of two distinct real
quadratic fields, then develops two common-row families. The accepted W003
rows give a twisted target in one field; rational rotations preserve it while
varying the second-field square test. The report claims explicit norm and
rational-square tests, followed by integral derivative clearing so actual
field roots can be reduced even when a displayed quotient denominator is not
a modular unit. Every required inversion still has a unit justification.

The rotation's norm quotient is genus one and has a stated rational point.
That point is not claimed to supply the two coordinate-square lifts or an
actual second-field square root. The asserted lifted genera are seven and
thirteen. The reciprocal family instead forces square absolute norms in both
fields, with its remaining mixed target expressed on eight genus-five curves
and genus-one quotients. Its weaker conic with prescribed unit witnesses
already yields a root of R. All these new geometry, equivalence and recovery
claims need independent checking at their exact scopes.

The finite program is fully specified on paper: deterministic paid Norm2,
field selection and early returns, two bounded rotation scans, then a bounded
reciprocal scan. For cap M its asserted inner cost is
C_norm+poly(n)+M^2 poly(n+log M). No useful target-probability lower bound is
given. With the full-list Norm2 reference and M=n^2, the claimed complete
expected O(N_0^(3/2) poly(log N_0)) bound comes from the earlier gcd fallback.
It is worse than the ordinary trial-division comparison. A polynomial cost
after Norm2 is not a complete factoring speedup.

The [prepared obligations](W004-review-preparation.md) cover field degree,
character counts, packet identities, exact root tests, localization, every
nonunit branch, ramification and connectedness of the covering curves,
finite execution order, raw-word probability and complete recursion cost.
They must be checked against the final report, including its explanation of
negative rotation parameters and the point on the elliptic norm quotient.
The field-norm and abstract-attainment corrections in W003 remain governing
accepted context; they do not accept W004's new deductions.

## Evidence and test boundaries

The source notes restrict each primary citation to stated pages/passages.
The reviewer must independently verify those actual uses. No claim is made
here that hash verification audits the underlying mathematics or primary
source theorems. AEM's previously recorded full-text retrieval limitation is
unchanged; no renewed search or faster Norm2 assumption is selected.

The proposed later screen would use at most 48 deterministically selected
small promised N,R cases, M=n^2, one second and 200000 recorded events per
worker, and a 60-second total wave. Its only proposed falsifier is a fully
exhausted failing case for that cap; timeouts and budget stops are unknown.
The report does not claim this coverage assertion. The independent reviewer
should assess whether the screen is precise and informative enough to
select, including how early factor/root branches may mask packet coverage.
The proposal is preserved, not approved for execution by this intake.

No numerical examples, mathematical execution, experiments, solver code or
Lean work have been performed in this intake. Launch a NEW review task with
the exact original assignment, frozen brief, in-flight update, final findings,
accepted W003 dispositions and unresolved obligations. The research goal
remains active; no final disposition or improved factoring bound follows yet.
