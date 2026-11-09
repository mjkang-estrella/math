# MathDB 365301: r6 locality repair, awaiting root review

The repaired endpoint is `ContactPilot.refutationLocal : ¬ ContactPilot.SourceConjectureLocal`.
The new predicate follows the root ruling exactly: one fixed positive lower
neighborhood and positive constants, and upper witnesses inside every smaller
positive neighborhood, with the same upper constant throughout. No adaptation
of the specification was necessary. The old SourceContact.lean and all 28 r5
modules are retained byte-identically as history.

`local_contact_unique` proves uniqueness of the natural-number contact order
for arbitrary functions q and arbitrary torus points. It uses neither rational
inner structure nor positivity/parity of the orders. Combining the lower bound
of one order with upper witnesses from the other, inside both neighborhoods,
contradicts the vanishing of a positive power of displacement if the orders
differ. A separate Cayley-chart lemma supplies arbitrarily small punctured
unit-circle displacements at any unit point.

`bidisk_local_contact_six` proves genuine local order 6 at (-1,1). It reuses
the inherited lower bound and strengthens the upper estimate using the
arbitrary-neighborhood half-plane localization and Cayley map, retaining
upper constant 16 for every neighborhood. `bidisk_not_local_contact_two`
follows from uniqueness. The existing unconditional reduced certificate,
actual graph resolvent and nearest-w distance 1 then give `refutationLocal`.
There are no residual bridge hypotheses.

REGRESSION.md proves ordinarily that the reviewer's diagnostic pair has local
order 2 at (-1,1), and cannot satisfy the repaired order-6 predicate. The
symbolic regression verifies its exact reduction, reflection, root formula
and height limit. That optional diagnostic is not a Lean theorem.

Final validation and exact declaration counts are recorded in results.json
and fresh-extraction/replay-logs. The packet contains only sources, scripts and
documentation. Its portable driver refuses existing compiled artifacts and
performs a strict serial rebuild, separate leanchecker calls, full declaration
type/body/flags/transitive-axiom audit, and 17 failing negative controls.
These include attempts to use the old non-local theorem or hypothesis to
close a local goal, wrong local order 2, and wrong refutation direction.

Read-only inputs are hash-bound before and after, with hash-identical copies.
All writes stay inside contact-formal-r6. No git, child agents, external
messages, browser tabs, publication, ledger edits or count changes were used.
No background jobs remain at handback. Counts remain 22/40 beyond the previous
39. This is a formal repair, not a new credited mathematical result. No new
prior-art, significance or source-body review is claimed; preserved independent
review and earlier research limitations remain for root to adjudicate.
Root acceptance is pending; no self-acceptance or acceptance credit is claimed.
