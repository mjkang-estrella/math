# Full semimonotone conjecture remains unresolved

Credit requested: **0**. No acceptance decision. Counts unchanged:3/30 additional,
33/60 total. Only this assigned lane was written; no children or git operations.

Concrete result: an exact singular6x6 matrix with positive diagonal, positive
left/right null vectors, common positive nonzero maximal cofactors and all
maximal-block inverses nonpositive. Its diagonal is1/3, within-group entries7/3,
cross-group entries-5/3, for two groups of3. It violates smaller-block E0,
so it is **not** a counterexample to Chauhan–Dubey Conjecture3.12.

Further ordinary reduction: any singular matrix satisfying the local inverse
conditions has strictly positive left and right null vectors. After positive
diagonal scaling it is balanced, and the entire local inverse condition has
an exact parametrization by directed semimetrics through a centered inverse.
The source nonsingularity step becomes exclusion of E0 on all(n-2)-blocks in
that parametrization. This exclusion is unproved. See discovery.md for the
ordinary derivation, independent root-reduction verification, exact example,
failed routes, strongest objections, source chronology and access limits.

`python check.py` passes fixed rational checks, including both root fixtures
and a nonsymmetric directed-semimetric example. `python metric_probe.py`
records6000 bounded numerical probes, no source counterexample. Both have
512MiB address-space, explicit CPU and single-thread BLAS limits.

No full ordinary proof, Lean, PROOF.md, paper, independent review or novelty
clearance is claimed. The journal and closest companion full-body gaps remain.
