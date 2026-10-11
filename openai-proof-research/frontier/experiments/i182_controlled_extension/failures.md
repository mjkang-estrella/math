# I182 retained failures and empty captures

Before the freeze, three read-only scoping probes ran: two JSON key
inspections of retained ancestor payloads and one enumeration of
quadrilateral face adjacencies in the retained I177 child graph to
locate candidate two-square patches. They used unauthenticated reads,
made no claim, and are not evidence; every mathematical statement in
this package is re-derived post-freeze from frozen byte-authenticated
inputs by the sealed diagnostics. No pre-freeze probe wrote any file.

A pre-diagnostic debug run of the abstract patch subset enumerator
(plain `python3` heredoc, no repository data) printed the ten
degree-correct local subsets; it informed the forcing predicate below
and is likewise not evidence.

`mandatory-attempt-01` failed at the cross-retained consistency check
between the I181 and I180 mandatory payloads with
`AssertionError: cross-retained I176_k6`. Cause: the retained I180
payload serializes the `image_minor` entries as strings (Fraction
export), while I181's payload stores the same integers numerically.
The check now coerces through `Fraction` before comparing. No output
JSON was created; stdout is empty; stderr is retained.

`mandatory-attempt-02` reached the fresh I181 patch-forcing control and
failed with `AssertionError` on `len(solutions) == 2`. Cause: the fresh
predicate wrongly expected exactly two degree-two-at-cycle-vertex
subsets of the eleven abstract patch edges; the actual population is
ten, including the bare boundary six-cycle. The parent certificate's
uniqueness claim is per exact alternating half, not global. No output
JSON was created; stdout is empty; stderr is retained.

`mandatory-attempt-03` failed with
`AssertionError: exactly one degree-correct local set per half`. Cause:
the predicate tested subset-containment of a half, which several of the
ten degree-correct subsets satisfy; corrected to subsets whose
intersection with the boundary equals the half exactly. No output JSON
was created; stdout is empty; stderr is retained.

`mandatory-attempt-04` failed with `AssertionError: routing B`. Cause:
the retained quoted routings order component words by walk start, not by
component minimum; the fresh signature lists groups by least vertex.
The comparison now sorts words by their first vertex. No output JSON
was created; stdout is empty; stderr is retained.

`mandatory-attempt-05` then passed (all 22 mandated control stages in
the mandated order). `extension-attempt-01` passed on its first attempt.

A first verification replay after the initial seal failed inside
`verify182.py` itself before any recomputation: four verifier-side count
assertions compared payload lists (`cycles`, `equations`, `witnesses`,
`rejected`, `parent_identities`) against their lengths. The payloads are
correct; the verifier assertions were wrong. The stale seal was removed,
the verifier corrected, the failure recorded here, and the inventory,
prevalidation and exclusive seal were regenerated on the corrected
package.

The corrected verifier then passed twice, but review against the I182
brief showed it lacked the mandated eight blocked probes (write,
mutation, network, subprocess, unbound read, outside compile, outside
exec, forged owned source). The verifier was extended with the probe
harness; no diagnostic, payload or mathematical content changed. The
inventory, prevalidation and exclusive seal were regenerated a second
time on the probe-bearing verifier.

All inherited ancestor failures, rejected stages and empty captures in
the 1,014 strict bindings remain unchanged. No ancestor was repaired,
overwritten, rolled back or resealed.
