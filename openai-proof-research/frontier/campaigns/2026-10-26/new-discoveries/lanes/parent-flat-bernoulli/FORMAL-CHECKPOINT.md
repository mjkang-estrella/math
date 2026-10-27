# Development checkpoint — no source-level formal claim

The finite spectral propagation criterion is now proved in Lean, including its
all-n>=11 sign conclusion under explicit finite spectral hypotheses. The
orthonormal eigenbasis power-moment expansion is also proved.

Four modules compile from source under Lean4.34.1 / pinned mathlibd13f23b7,
`-DwarningAsError=true`, with empty build logs:
WeightedPowers, EvenPropagation, SpectralPropagation, SpectralMoments.
The checkpoint has **14 declarations (11 theorems and3 definitions)**.
`formal-dev/CheckpointChecks.lean` prints every type and every axiom set;
root inspected all14 reports in checkpoint-types-axioms.log. All use only
propext/Classical.choice/Quot.sound. No sorry/admit/newaxiom/native_decide.

These are supporting generic results. The literal source endpoint remains
absent. Required work: construct the arrowhead matrices and prove their
spectral structure; actual center-moment recurrence and Riemann convergence;
source finite composition/count bridge and rank/factorial conversion.

The 36-file preliminary-review freeze is preserved unchanged. New formal
modules and this checkpoint are outside that freeze and are not offered as
a source-level formal PASS. The proof candidate remains credit0.

The relevant theorem bodies in Hansen's 1988 doctoral thesis were additionally
read (renewal-hansen-thesis.pdf, sections2.3 and3.4). Its straightforward DFR,
log-convex and Hamburger-moment hypotheses fail for this interarrival sequence.
See renewal-subsumption-checkpoint.json. This only rules out those direct
applications; broader independent prior-art review remains necessary.

The previous analysis discovery task is now authoritatively terminal:
T3 task_cancel returned interrupted, and the stopped thread has no active run.
Its partial numerical investigation did not produce a completed result.
The freed slot is reserved for a NEW independent preliminary Hetyei review.
Only Pi GLM5.3Flash, default speed, with at most three active children.
