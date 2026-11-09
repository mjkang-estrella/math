# W032 transition to exact carry quotients

Parent intake, 2026-10-08. Verified complete factoring improvement: **NONE**.
The period-bound (364 lines), unit-step (269), ratio-sharing (193), and
carry-quotient (515) reports were read in full. The
[integrity record](W032-quotient-transition-intake.json) verifies all 23,
23, 28 and 24 respective payloads against their external terminal anchors.
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
with O(R^2) events for a0=1. Its separate symbolic audit is LIVE. A single
[bounded diagnostic](W032-lift-sweep-protocol.md) is frozen and delegated,
with three prescribed inputs and no tuning or repeated execution.

The later [two-dimensional cover](W032-lift-arrangement-cover.md) removes
the large-base event factor by enumerating a superset of gcd arguments.
Its own audit is LIVE; it is not part of the frozen diagnostic. Extra
arguments must never be labeled actual lift witnesses or assigned a
uniform-lift probability. Both constructions still lack an asymptotic
useful-factor supply theorem. That is the core bottleneck now.

No Lean or shared implementation was changed in this intake. Run the
required project checks after the new diagnostic source is delivered;
preserve the single-run rule even if it fails or hits its budget.
