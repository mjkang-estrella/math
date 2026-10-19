# R040 — Two-variable finite strict free-entropy gap

**Accepted as the eighteenth substantial result of the 2026-10-14 campaign: 18/20.** Internal acceptance uses stipulated pinned source theorems and bounded primary-literature comparison. It is not external peer review or worldwide-priority certification.

There exist exactly two bounded self-adjoint elements Z₁,Z₂ in a von Neumann algebra with faithful normal tracial state such that

\[
-\infty < \chi(Z_1,Z_2) < \chi^*(Z_1,Z_2) < \infty.
\]

Here χ is the original operator-norm-cutoff microstates entropy, with unnormalized Hilbert–Schmidt volume and the ordinary limsup over all output matrix sizes. The result uses no supplied matrix-unit conditioning, ultrafilter replacement, or restriction to multiples of a fixed size. The deduction assumes source298 and the other explicitly identified pinned OpenAI inputs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, together with classical results under their stated hypotheses.

Source298 supplies the noisy bounded tuple of size n=2⁶⁴+1 with finite Fisher information and a finite entropy gap at least 1/2. With k=2³², the normal-slice encoding satisfies the source-specialized bound liminf as ε→0 of gap(Eε(X)) ≥ gap(X)/k². This gives existence of a strictly positive finite two-variable gap. No effective ε, practical low-dimensional witness, or W*-generation theorem is claimed.

The substantial contribution comprises the unconditional cheap-orbit Fisher estimate, intrinsic matrix-unit recovery and matched upper volume estimate for every output size, and their coupling through exact free noise and analytic straightening. Orbit-volume constants, the corner/compression pattern, classical entropy comparisons, and the final two-scale strictness argument are credited antecedents. The literature screen has explicit reading limits and does not establish worldwide priority.

All required gates passed at the unchanged target:

- [Proof review](../campaigns/2026-10-14/t298p-proof-r2/review.md): PASS_FULL_T298P.
- [Contribution review](../campaigns/2026-10-14/t298p-contribution-r2/review.md): SUBSTANTIAL conditional on correctness. The separate proof and manuscript gates discharge that condition for internal acceptance; all four required attribution/comparison fixes are present in the paper.
- [Formal audit](../campaigns/2026-10-14/t298p-formal-review-r2/review.md): PASS for scoped support only.
- [Final manuscript review](../campaigns/2026-10-14/t298p-manuscript-review-r4/review.md): PASS_FULL_MANUSCRIPT_T298P, with no required findings. The historical round-3 NEEDS_REVISION and its two resolved objections remain preserved.

**The analytic theorem is not formalized.** Lean checks four finite-dimensional/scalar supporting declarations and four controls, with ten additional independent examples and five rejected broken variants. The full column-Gram, analytic-increment, and endpoint assumptions are exposed; scalar variables are finite real numbers. Standard axioms `propext`, `Classical.choice`, and `Quot.sound` are used. The installed compiler/runtime and pinned cached dependency oleans are trusted; no bootstrap or dependency-binary authentication is claimed.

The reviewed [18-page paper](../campaigns/2026-10-14/t298p-manuscript-r2/output/pdf/main.pdf) and [local release ZIP](../../output/release/r040-two-variable-finite-free-entropy-gap-v1.zip) are complete. Parent replay from a clean extraction rebuilt the identical PDF, matched both Lean builds' recorded types, axioms and logs, and rejected all five broken fixtures. Reassembly from the extracted files produced the identical ZIP. The release implementation also records 50 author-run integrity, semantic-gate and reproducibility controls. [Acceptance and hashes](../campaigns/2026-10-14/t298p-parent/acceptance.json) and [parent release validation](../campaigns/2026-10-14/t298p-parent/release-v1-validation.json) distinguish these checks from mathematical proof.

Frozen package metadata records the preacceptance stage as accepted=false/count_change=0; this separate parent decision grants one campaign acceptance. One optional prose splice is preserved in the frozen reviewed paper. Uploads and submissions remain stopped. Two further accepted results remain.
