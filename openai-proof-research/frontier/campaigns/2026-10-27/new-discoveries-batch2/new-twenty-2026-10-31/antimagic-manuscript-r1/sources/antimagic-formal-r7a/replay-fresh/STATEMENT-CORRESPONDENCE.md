# Endpoint correspondence

The requested endpoints use the literal inherited definitions without edits.
`Labeling G` is an edge-set equivalence into Fin |E|; `weight` sums the
values plus one over incident edges. `IsLocal` requires unequal weights
on adjacent vertices, and `spectrum` is the set of attainable color counts.
`chiLA` is its infimum; the endpoint supplies IsLeast as well as equality.

`FullTree G t n` is the inherited rooted structural certificate with every
nonleaf having exactly t children and all leaves at depth n. The round-4B
ModelBridge transports this certificate to the model. The graph endpoint
quantifies over every finite SimpleGraph with that certificate, t >= 2 even,
and n >= 1; its leaf count uses degree-one vertices.

AntimagicFinal7A.even_case is to have exactly AntimagicFinal6A.even_case's
statement with BinaryHigherConstruction discharged. The arbitrary-tree
mathdb_354228 endpoint is to have exactly AntimagicFinal6A.mathdb_354228's
statement with BinaryHigherConstruction and ModelBridge discharged. No new
structural assumptions, numerical bounds on n, or nonliteral colorings may
be introduced. Consult results.json and the compiled final module for actual
completion status; this correspondence note is not a validation claim.
