# Proof status

`Literal.closed_certificate_sound` proves by induction on pure reachability that a closed state set, all of whose graphs have order at least b, bounds every pure result. `RawClosure.closed_set_sound` supplies the corresponding theorem for the canonical list-matrix reduction operation. Neither theorem assumes the conjecture.

`Concrete.original_doubled_cubic` checks the original 18-vertex matrix. `Concrete.pure_path` verifies the seven reductions [0,0,3,4,6,7,11] under the literal finite-matrix move relation. The selected graph has order 11. Every concrete graph is a symmetric, loopless natural matrix by its checked structure fields.

`Concrete.seven_move_witness` verifies expand (1,6,8), reduce 6, expand (4,7,10), expand (3,7,10), reduce 10, reduce 7, reduce 9. Its target has order 10. `Concrete.nonminimal` is unconditional and uses these literal moves and the strict order drop.

`Controls.chain_positive` exhibits a one-triangle chain with bases 0 and 1, apex 2, left attachments 3 and 4, right attachments 5 and 6. Both bases have degree 6 and satisfy the end condition. Its graph is intentionally a small subgraph control, not claimed globally 6-regular. `Controls.move_positive` supplies an actual legal move on the original input.

`Endpoint.conditional_negation` has exactly two remaining premises: `Endpoint.PureLowerBound` and `Endpoint.ChainAbsence`. It does not establish either. Applying the conjecture to the cubic input and chosen pure minimum would make that graph minimal because it is chain-free, contradicting `Concrete.nonminimal`.

The lower-bound certificate work is a bottom-up DAG certificate: each listed matrix has order at least 11 and every legal reduction is one of its listed children; already proved child bounds imply the parent bound via `RawClosure.extend`. Children precede parents. This avoids evaluating exponentially repeated pure reduction trees. Counts of 2328 states and 9846 arcs come from the supplied JSON and are not substitutes for closure checks. See SUMMARY.md and results.json for the final checked extent.

Outstanding for an unconditional endpoint: finish any incomplete DAG chunks, formally transport the canonical list-matrix lower bound across arbitrary survivor numbering into `Literal.Pure`, and prove chain absence under `Literal.Chain`. The review's local obstruction is ordinary guidance, not a theorem imported here. No claim that order 10 is a global minimum is needed.

`Final.conditional_literal_negation` intends to use the canonical DAG result (this final module and its full certificate dependency are not yet checked) and exposes the more precise residual pair: `Final.CanonicalTransport` and `Endpoint.ChainAbsence`. The transport proposition explicitly asks that each arbitrarily numbered literal pure result have a canonically numbered list-matrix result of the same order. This is a genuine remaining proof obligation, not a convention or an axiom.

The final DAG certificate selects children by reduction centre, short-circuiting comparisons with unrelated children. `RawClosure.indexed_extend` proves this optimization sound from full matrix equalities, and does not trust child indices. Generated, not yet compiled: `RawCert.certificate_entry_count` and `RawCert.certificate_legal_arc_count` are intended to compute 2328 entries and 9846 legal centres in the Lean kernel. Entry count is list length, not a separate formal pairwise-distinctness theorem; the generator additionally checks distinct matrices in Python.
