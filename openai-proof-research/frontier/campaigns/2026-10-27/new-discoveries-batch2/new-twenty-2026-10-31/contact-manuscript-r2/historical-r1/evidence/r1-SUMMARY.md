# MathDB 365301 formalization pilot: partial, zero credit

**Stop at incomplete P3. No conjecture refutation and no acceptance.**

P1 supplies compiled source predicates, the actual colored adjacency matrix
inverse representation, a polynomial reduced rational-inner certificate, a
walk-based nearest-w distance, and a universal SourceConjecture. The source
comparison is in STATEMENT-CORRESPONDENCE.md. These definitions still need
independent fidelity approval; no candidate reduced certificate is constructed.

P2 succeeds for the reviewer's L = -i normalization in x = -1/z. The local
inverse of squaring at 1 yields an analytic square root, with an exact local
square identity. It gives two analytic roots of the normalized concrete
quadratic, with initial values -1 and -3, exact local factorization, and
exhaustiveness for every normalized root. There is no analyticity assumption
left over in the existence theorem.

P3 makes real progress beyond jets: an exact polynomial residual and a
nonvanishing divided difference give an actual analytic remainder for the
slope -1 branch. The checked theorem `ContactPilot.concrete_order_six`
constructs an analytic quadratic root u and proves

`analyticOrderAt (fun x : ℝ => ((x : ℂ) * u x).im) 0 = 6`.

This is an unconditional local analytic order theorem, not the graph/contact
endpoint. The corresponding order-two theorem and the common-neighborhood
imaginary-distance comparison over both roots were not completed. Thus the
required paired P3 result remains incomplete. The pilot stops without P4;
none of the graph representation, reduction, Cayley transfer or literal
`¬ SourceConjecture` bridges is claimed proved. No mathematical impossibility
or missing foundational mathlib theorem is asserted. GAPS.md identifies the
missing application proofs and gives remaining effort estimates.

Validation of the **partial source packet** passed on fresh extraction
`work/extracted-02`: strict sanitized sequential Lean 4.34.1 build with
`-j1 -DwarningAsError=true`, leanchecker for all four modules, complete
opaque-inclusive type/body/module/flag/transitive-axiom audit, and three
expected-failure controls. There are **73 declarations including generated
ones**: SourceContact 39, QuadraticBranches 19, ExactOrders 15. Audit.lean
adds no mathematical certificate declarations. Only propext, Classical.choice
and Quot.sound occur transitively; no unsafe or partial declaration was found.
The checker replays each module from its imported environment; this is not a
claim to have rechecked all upstream mathlib from a fresh empty kernel.

The final extracted validation made 11 sequential compiler/checker calls.
Maximum sampled private RSS was 4,719,206,400 bytes, below 6 GiB; maximum
wall time was 23.80 seconds. The watchdog limits process groups to two CPUs,
CPU 120 seconds, wall 140 seconds and sampled private RSS 6 GiB. Full logs
and sampled receipts are in logs/replay-*. Large audit bodies are losslessly
gzip archived rather than truncated. Developmental failed attempts and logs
are retained separately; they are excluded from the accepted module build
and the source-only packet. The successful order-six scalar-restriction
probe was promoted into ExactOrders.lean.

All 19 designated input files were SHA-256 bound before and after, copied
with identical hashes, and remain unchanged. The inputs include the root
adjudication's bounded prior-art qualification; this pilot does not claim a
new live novelty clearance. No network lookup, child agent, git operation,
shared ledger edit, publication, external message or browser tab was used.
All writes stayed inside contact-formal-r1. All started processes completed;
no background job is left at handback. Campaign counts are unchanged.

Deliverables: results.json, GAPS.md, formal/, STATEMENT-CORRESPONDENCE.md,
contact-pilot-source.zip, REPRODUCE.md, and logs/ with replay receipts,
declaration inventory, audit archive, negative controls and input hashes.
Only the root may accept; this report awards zero credit.
