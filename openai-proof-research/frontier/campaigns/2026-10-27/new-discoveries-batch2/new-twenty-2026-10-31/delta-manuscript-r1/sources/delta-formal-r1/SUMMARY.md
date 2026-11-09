# Partial formalization — MathDB 352253

**Not an unconditional refutation. Not acceptance. Credit remains zero.**

Closed, compiled and explicit-module leanchecker checked:

* Literal finite multigraphs, both moves, pure results, pure minimum, equivalence, minimality, doubled cubic inputs and the capacity-based edge-distinct chain definition.
* The original input is doubled cubic; the seven pure reductions reach the selected order-11 graph.
* The seven-move witness reaches order 10. `Concrete.nonminimal` is unconditional and uses the literal matrix move relation.
* Positive legal-move and one-triangle-chain controls, plus a two-triangle control with an internal triple connection.
* Generic closed-state soundness and indexed DAG-certificate soundness.
* `Endpoint.conditional_negation`, with precisely the premises `Endpoint.PureLowerBound` and `Endpoint.ChainAbsence`.
* Fresh replay through `Closure107`: 432 of the supplied 2328 certificate entries. Every legal reduction of each checked entry is kernel-checked against its indicated child matrix. Each checked entry has a proved pure lower bound. Entry/arc census proofs are also checked for that prefix.
* `AuditPartial` inspected 3017 declarations by defining module, including private helpers: no disallowed declaration metadata. The conditional endpoint reports only propext, Classical.choice, Quot.sound. The source scan is clean.

Still required:

1. Complete the remaining canonical DAG replay (Closure108 through Closure581), RawResult, Final and the full Audit. These are generated source, **not claimed checked**. The archive has 609 modules; 131 were checked by the serialized fresh-extraction driver, with AuditPartial additionally compiled and leanchecker checked separately.
2. Prove transport from canonical list-matrix pure reductions to the arbitrarily labelled `Literal.Pure` relation. Do not silently identify the two relations.
3. Prove `¬ Literal.HasChain Concrete.g7`. The review's local obstruction has not been formalized here.
4. Complete independent formal-fidelity review and a full fresh strict replay. The capacity presentation is documented explicitly; no separate equivalence theorem to an edge-ID embedding API is claimed.

`Final.conditional_literal_negation` is a proposed sharper endpoint conditional on transport and chain absence, using the proposed complete canonical bound. It has not compiled because its canonical certificate dependency is unfinished. The **checked** endpoint is `Endpoint.conditional_negation`.

Resume with `bash replay-r1/scripts/replay.sh --resume` from this lane. It remains serialized and uses the original caps. For an entirely new extraction use source.zip and scripts/replay.sh. No process remains running at handback.

The archive was updated after the initial extraction only to add AuditPartial, fix the pending full audit's counter annotation, and update the module/source manifests. The 131 successfully replayed modules retain exactly the source bytes from the fresh extraction. This is a partial replay receipt, not a claim that the final archive completed strict replay.

All writes stayed inside this lane. No discovery script, git operation, network request, browser tab, external message or child agent was used. Development failures and the early unestablished non-overlap incident are candidly recorded in logs/development-incidents.txt; the successful replay driver itself was serialized.
