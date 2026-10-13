# I213 — analytic/geometric discovery: relative approximation remains unpaid

**Exact verdict: UNRESOLVED TARGET; TECHNICAL PARTIALS ONLY. No PROVED NOMINATION.**

All OpenAI theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. None is audited for truth. The parent owns both independent acceptance gates and the count. This report supplies no ninth finding; I203 remains technical. I211/I212 reviews were not read, and I209's proposed bound is neither used nor discussed as a source. No parked graph/algebra line is reopened.

## Scope and the early target choice

The three requested families were screened against the current ledgers and specific matching reports, without historical replay. Contrary to a title-only freshness screen, positive overlap exists for **all three**:

- **354:** I43 §1.2 already treats fixed-volume quadratic stability, including both co-minimizing types at a transition. It expressly classifies that as technical and identifies the failure of uniform distance to only the winning phase. Arbitrary rectangular aspect ratios retain an anisotropic endpoint gap. A phase-aware reformulation here would not constitute a new difficult bridge.
- **368:** I07 §§2–3 treats constrained/inverse approximation and the Jacobian-correction cost; I122's Screen D identifies the prescribed-trace incompressible variant as overlap. That energy/incompressibility problem is not recycled.
- **377:** I130's Screen I spends homogeneous gradient interpolation and leaves inhomogeneous gradient stability unpaid; I140/I143 separately discuss actual p-harmonic gradients and the failure of the affine lift for that equation. No interpolation or limit-regularity transfer is nominated here.

The early selection was therefore the narrower **exact smooth boundary trace** question for family 368. No substitute family was added. The target is: for every finite p>3 and every W^{1,p} homeomorphism of the closed unit three-ball equal to identity on its boundary, construct strongly convergent diffeomorphisms smooth and nonsingular on the closed ball, fixing its boundary pointwise. This adds neither incompressibility nor inverse-energy convergence. The distinction between smoothness on the open ball and smoothness up to its boundary is essential.

The precise statements, complete technical proofs, two approaches and quantified missing estimate are in [analytic-attempt.md](../experiments/i213_new_analytic_geometric/analytic-attempt.md). The chronological reading scope and failure record is [reading-and-failures.md](../experiments/i213_new_analytic_geometric/reading-and-failures.md). Exact input paths, pinned raw URLs, scopes and SHA-256/Git-blob provenance are in [input-authentication.json](../experiments/i213_new_analytic_geometric/input-authentication.json). [literature.md](../sources/i213_new_analytic_geometric/literature.md) records primary comparisons and their limits.

## What the pinned source actually supplies

Both family-368 introductions state strong W^{1,p} approximation onto the *same open target*: the low-range companion covers 1≤p≤2, the high-range one p>2. Both expressly withhold boundary regularity. In both, `sm:smoothing` gives arbitrarily fine positive continuous value tolerance for a **locally bi-Lipschitz input**. `sm:relative-pl` is relative where the map is already PL and has no derivative estimate. High-range `hp:opening` has exact agreement on an eligible closed target set for its constructed carrier, but only qualitative/fine-value control. `hp:carrier` constructs protected exact cores; the final high-range assembly includes smoothing and finite corrections, without a stated prescribed-boundary conclusion.

These are actual read theorem/lemma contracts and proof passages, not inferences from titles. The torus main theorem, its two-volume reduction and standard-competitor equality argument were also read in place, as was the full family-377 introduction with its precise nonexplicit α_d∈(0,1/3] interior theorem and stated lack of endpoint/boundary conclusions. The inventory/catalogue companions were checked: one torus manuscript, both approximation range manuscripts, and one infinity-harmonic manuscript. No claim to a semantic search of every theorem in the corpus is made.

## Results of the two routes

**Route A: compression followed by relative approximation.** A full technical proof shows that any closed-ball boundary-fixing Sobolev homeomorphism is strongly approximated by homeomorphisms which are exactly identity in a boundary collar, using Sobolev Alexander compression. A second full proof flattens any *already smooth, boundary-nonsingular* diffeomorphism to identity in a collar with W^{1,p} error tending to zero. Consequently the target is equivalent to strong smooth approximation for inputs already identity near the boundary, with outputs identity in some collar. That latter relative density assertion remains unproved here. Qualitative PL approximation does not pay its derivative cost.

**Route B: ambient approximation followed by annular correction.** Extend the compressed map by identity to a larger ball and use the stipulated ordinary approximation. For p>3, Morrey gives uniform convergence as well as strong Sobolev convergence. The desired new estimate would straighten the approximants to identity outside an intermediate radius, keep them unchanged inside a smaller radius, and make the derivative error of the annular correction tend to zero. This is `(CS_p)` in the analytic note.

A fully proved diagnostic rules out one proposed shortcut: for a **fixed smooth scalar cutoff**, there are smooth boundary-identity diffeomorphisms converging to id strongly in every finite W^{1,p} and uniformly, whose cutoff interpolation with id is not injective. The explicit determinant at the folding point is `−exp(−1/s)/2`. The construction uses local compression, not a numerical experiment. It refutes that implication, **not** the existence of a better correction; id itself is a valid correction in the example.

Fine smoothing of a locally bi-Lipschitz closed-ball input does give interior diffeomorphisms extending continuously with the exact boundary trace, by choosing tolerance proportional to distance squared. This is another direct technical corollary and still does not give smooth boundary-nonsingular approximants.

## Prior art and final gate

The original [Iwaniec–Kovalev–Onninen paper](https://arxiv.org/abs/1009.0286v1), read in full, already supplies zero-trace errors and compactly supported modifications in its planar theorem. Its five-stage proof uses planar p-harmonic injectivity and energy control; topology alone is not a replacement for that operation. [Hencl's survey](https://arxiv.org/abs/2502.01336v1), read in the existing local copy, separates ordinary, energy, and incompressible approximation. The published piecewise-affine smoothing result was checked bibliographically, but its external proof is not imported as an unexamined relative-energy theorem. No worldwide novelty follows from the bounded search.

**Next unpaid estimate:** prove collar-supported strong smooth density `C_p`, or the sufficient derivative-controlled annular correction `(CS_p)`, with exact injectivity, fixed boundary trace and all error quantifiers. The technical compression, smooth-input flattening, positive-tolerance smoothing and cutoff failure do not establish it. Even a successful relative localization would require a separate contribution review against the complete source mechanism. Present verdict remains **UNRESOLVED / TECHNICAL ONLY**, with no count change proposed.

Only the assigned I213 report, two notes, authentication JSON, literature note and fully read primary PDF/text were written. No research code, scans, tests, snapshots, seals, commits, staging, publication, shared edits or subordinate agents were used. Detached hashes are returned separately.
