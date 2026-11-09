# W032 transition to exact carry quotients

Parent intake, 2026-10-08. Verified complete factoring improvement: **NONE**.
The period-bound (364 lines), unit-step (269), ratio-sharing (193), and
carry-quotient (515), lift-sweep (279), and arrangement-cover (491)
reports were read in full. The
[integrity record](W032-quotient-transition-intake.json) verifies all 23,
23, 28, 24, 25 and 31 respective payloads against their external terminal anchors.
Hash checks are delivery evidence, not proofs. No candidate was rerun.

- Accept [the period lower bound](W032-period-bound-review.md), including
  its precise prime band and uniform PNT consequence. The reviewed
  common-label filter cannot split the stated sufficiently large balanced
  inputs even with its minimum global label period. This is not a sharp
  period law or a restriction on every carry consumer.
- Accept [the unit-step algebra](W032-unit-step-review.md) with its stronger
  rejection: D divides the integer residual and is a unit modulo N, so
  it adds no gcd support. Any full exact small-tail stencil forces
  R=O(logN/loglogN). The parent independently derived the same two
  obstructions. Initial gcds, individual digits and unguarded filters are
  not disposed of by that theorem.
- Accept [the unguarded quotient](W032-carry-quotient-review.md), its exact
  coefficient recurrence, strict |c|<4^R, monic multipoint evaluation and
  signed integer convolution. The full denominator branch through 2R+1,
  actual unwrapped inputs, exact division and failed attempts remain part
  of the contract. Soft O(R^2 logN) is an acquisition upper bound, not a
  lower-bound speedup theorem or successful factoring runtime. The stronger
  small-tail estimate logN>=2R logR-O(R) is also accepted by this review.
- Accept [the ratio-sharing identities and exact law](W033-ratio-sharing-review.md).
  The KH and H^2+K volume gates remain for the specified random generator
  and representations; deleting rational repetitions gives no asymptotic
  gain. Raw/accepted sampling costs differ, although a separate stopping
  argument proves the same loose K(1/p+1/q) probability bound for accepted
  K. A bare product-tree descent is insufficient with globally full leaves
  outside the no-alias range; the stated paid decoders restore completeness.

The main thread changed computation after these negatives: exact carry
quotients eliminate the small-tail guard, and a
[breakpoint sweep](W032-lift-breakpoint-sweep.md) covers a full N-lift family
with O(R^2) events for a0=1. Accept its separate symbolic audit, including
atomic ties, coalescing zero-net ties for maximal constant intervals,
shared weight references in the event-space bound, and the distinction
between event counts and gcd counts. The accepted carry acquisition
resolves its provisional C_base dependency. Its soft O(R^2(logN+R)) bound
exhausts a possibly unsuccessful family; it is not a factoring bound.

The single [bounded diagnostic](W032-lift-sweep-assay.md) is terminal:
two full families had no proper gcd; the third stopped in prime generation
at the shared 20,000-event cap and has no candidate result. All 35 sealed
payload hashes match. The report was read fully; code/ledger correctness
is separately delegated to W032-sweep-assay-audit-r1, so these delivery
claims are not yet promoted to parent-accepted implementation evidence.
No rerun or tuning occurred. The parent required project checks passed:
12 Python tests, source screen, pinned Lean build and axiom audit; see
[the check log](W032-lift-sweep-project-checks.txt). These checks do not
exercise the new assay or prove its mathematics.

The later [two-dimensional cover](W032-lift-arrangement-cover.md) removes
the large-base event factor by enumerating a superset of gcd arguments.
Accept its audit with the explicit horizontal-line boundary convention:
skip edge division for i=0 and ignore top-edge overlap as a cut. Its
imported lift identity is now resolved by the accepted sweep review.
It is not part of the frozen diagnostic. Extra
arguments must never be labeled actual lift witnesses or assigned a
uniform-lift probability. Both constructions still lack an asymptotic
useful-factor supply theorem. That is the core bottleneck now.

The parent next derived [an affine two-parameter family](W032-affine-lift-family.md)
varying both start and step; its separate audit is LIVE. The additional
quadratic phase preserves the annihilation identity and has an explicit
polynomial geometric superset, but no useful-factor supply theorem.
The separate [W034 order construction](../hypotheses/W034.md) has a concrete
N-dependent exponent and proposed exact split law. Opus failed with API
errors; the unchanged mathematical brief is now in a new Codex review round.
The [integral-annihilator compiler](W032-annihilator-image.md) is a third,
unreviewed symbolic computation: translated differences generate the whole
kernel image, while unconstrained target programming supplies no gain alone.

No Lean or shared solver implementation was changed in this intake.
Preserve the frozen run even though its third group is unfinished.
