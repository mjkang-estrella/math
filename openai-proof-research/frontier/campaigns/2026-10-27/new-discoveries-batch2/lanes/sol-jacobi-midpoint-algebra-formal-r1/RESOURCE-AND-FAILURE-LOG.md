# Actual formal-build resources and corrected failures

All Lean invocations used the supplied runner and sampled RSS guard, with
`-j1 -M4096 -DwarningAsError=true -DautoImplicit=false`. Builds were sequential.
The guard samples every 0.2 seconds, adds the runner and its Lean child RSS,
and has a 3,145,728 KiB threshold. It does not set a virtual-memory limit.
Every invocation has its full output and JSON receipt under
`verification/development/` or `verification/fresh/logs/`.

The fresh source-only replay passed all eight proof modules, both complete
audits, and the environment/safety inventory. All proof logs are empty.
The largest sampled fresh proof-module RSS was 2,284,052 KiB; the largest
sampled RSS including the Lean environment inventory was 2,737,980 KiB.
Proof modules disable only the nonmathematical `unnecessarySeqFocus` style
linter where used; the exhaustive audit additionally disables the
`auxLemma` reference-style linter. Neither changes proof checking or the
warnings-as-errors setting.

Every fresh exit code was zero and no RSS guard fired. These are sampled
measurements, not claims of continuously measured maxima.

Development receipts are aggregated without omitting failed invocations in
`verification/development-builds.json`. Of 34 formal-build attempts, 11
returned nonzero before the final successful replay. No guard killed any
build. The largest development sampled RSS was 2,738,088 KiB. Corrected failures:

| Attempts | Actual failure and correction |
|---|---|
| 001–003, 005 | Reserved identifier `partial`, projections simplifying too deeply or in the wrong order, missing imports/API names, unfinished coordinate goals, and style-linter errors. The concrete operator is named `delta`; coordinate proofs now apply the pair extensionality theorem and explicitly rewrite projections as needed. Some initial failed declarations triggered Lean's generated-placeholder error; no placeholder was authored or retained. |
| 008 | Downstream sequence build attempted while the algebra module had not yet produced an olean. Rebuilt only after the algebra passed. |
| 010 | Focused Lean proof probe reproduced the coordinate-simplification issue. Explicit projection rewrites resolved it; the final successful probe is preserved as `verification/development/Probe-final.lean`, outside the deliverable proof modules. |
| 014 | Renamed/deprecated coefficient and conditional APIs under warnings-as-errors. Updated to current additive-monoid-algebra and conditional APIs. |
| 016 | An overbroad rewrite changed the argument of the extraction operator; one style warning also failed the build. Replaced it with a directed calculation and corrected the warning. |
| 024 | The obsolete `#print prefix` reporting syntax is unavailable in pinned Lean. Replaced it with a read-only environment-inventory command. |
| 026 | During replacement of well-founded recursion by primitive finite history, a deprecated conditional lemma and an unsimplified `Fin.last` bound failed. Both corrected. |
| 031 | Audit-only unknown pretty-print option and warnings about deliberate references to compiler auxiliaries. Removed the unknown option and disabled only that style linter in the exhaustive frozen audit. |

A working well-founded recurrence was replaced after inventory showed its
compiler-generated runtime helper. The final primitive `Nat.rec` history
has no unsafe environment declaration. The earlier source is retained at
`verification/development/MidpointSequence-well-founded.lean` as development
provenance and is excluded from the source-only packet.

The environment inventory is a Lean reporting module; it supplies no proof
term or mathematical assumption. No numerical experiments were needed.
The Python metadata/provenance diagnostic reported 16,376 KiB maximum RSS,
well below 512 MiB. No package or toolchain upgrade was made.

Only final sources and successful replay/audit reports support the component
claim. Historical failed logs are not certificates.
