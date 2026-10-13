# I203 reading, failed routes and validation

2026-10-12. Final, unsealed research record. **The all-height optimum is attained for every k>0; a proved nomination is returned to the parent.**

## Inputs and actual reading

Read AGENTS.md and sources/upstream.json. Used the full I203/I201 briefs, I201 report, analytic record and parent response supplied in the task; the local briefs/report/response were also read and actual file hashes recorded. Read the I201 literature, failure and authentication records in place. Read only the family-100 catalogue entry, not the whole catalogue or upstream corpus. The accepted revision was not audited.

Read the full retained introductions of all four covering companions. Read the full ruled-set `linear-coverings.tex` and `finite-approximation.tex`, including the exact hypotheses of `b:lattice`, the inverse bound and the finite-retention proof. No I198 or I201 input was edited or copied into a snapshot.

Read all 11 pages of I201's retained Kolountzakis 1998 publisher PDF via text extraction. Read the stated introduction/theorem/reference passages of the two 2025 lattice papers, not their complete proofs again. Read the full text of the new 16-page Kolountzakis–Papageorgiou v1 PDF and the new 28-page Loukaki–Spyridakis v1 PDF. Their diagrams were not used as proof evidence. Reading scopes and hashes are in the authentication record.

## Discovery, failed claims and corrections

1. **Finite nets.** A bounded cover for a finite height mesh can be thickened to cover all heights, but the area error depends on mesh size times support radius and perimeter. There was no justification that these quantities vanish for tiles produced by abstract finite-family existence theorems. The analytic record gives the exact estimate. This route was not declared a solution before finding the explicit construction.
2. **Endpoint-only inference.** A common endpoint fundamental domain does not automatically cover intermediate heights; the supplied counterexample remains valid. The final construction chooses a specific endpoint tile and proves every intermediate height independently. It does not repair that false general implication.
3. **Fourier obstruction.** The surplus estimate is |hat(1_F)(xi_t)|<=epsilon+k²-t². Only endpoint frequencies must be zeros at optimal density. Treating all intermediate frequencies as zeros, and importing a Steinhaus nonexistence theorem, would be invalid. The fractional relaxation in the analytic record attains the density bound in the limit for every compact nonsingular lattice path, so a purely fractional linear obstruction cannot prove a higher value.
4. **Finite-group obstruction.** The three-index-two parity example gives a real 3-versus-2 cover gap for another lattice family. It does not embed directly into an elliptic path with its varying determinant. The 2026 theorem is also explicitly equal-index/equal-volume. No strict obstruction for the present problem was obtained; the final construction proves that none exists.
5. **Initial geometric restriction.** The first companion matrix [[a,-1],[1,0]] produced a candidate range k>=1/sqrt(3). This was an artifact of that endpoint basis. The shear-endpoint matrix [[a-1,a-2],[1,1]] gives a fixed unimodular change under which the whole path lies in the accepted positive-product square-covering regime. It proves every k>0. The final B_k,G_k are scaled and simplified versions of that construction.
6. **Boundedness and near-zero determinants.** The construction is bounded for each fixed k. It was not assumed to have uniformly conditioned area-one templates as k tends to zero. The finite nonlinear proof first fixes a determinant cutoff, uses the older bound below that cutoff and then sends the cutoff to zero. Thus degeneracy does not leave an unproved uniformity assumption.
7. **Convex-body scope.** The exact result is for periodic affine covers. Neither endpoint density nor this construction proves optimality among arbitrary finite cylinder covers. The nonconvex rotation sweep is not replaced by its convex hull. No new tetrahedral coefficient is claimed.

## Retrieval and display issues

- The initial broad filename search returned unrelated historical filenames and was truncated. They were not opened as research sources or authenticated recursively.
- A combined early search/text display was also truncated. Later targeted source reads established the actual reading scopes.
- One attempted catalogue line range landed in an unrelated entry. The correct family-100 entry was then read at its identified location.
- A three-row preprint-tree search was incidental and not relied on for a manuscript claim.
- A combined 1998/2026 extraction omitted a short part of page 6 of the 2026 paper. Page 6 was subsequently reread in full, as was page 4 after the initial `head` display had stopped partway through it. The full-read claims for the retained new PDFs refer to these completed bounded reads.
- No unsuccessful download, unread source copy, numerical script or generated snapshot remains in the I203 source directory.

## Symbolic validation completed

Checked B_k inverse and both columns of B_k^(-1)(I+tJ)G_k; checked det B_k=2k and det G_k=2k/(1+k²); checked off-diagonal product (k²-t²)/(1+k²), its nonnegativity and strict bound below one over the closed interval. The endpoint shears, all irrational heights, arbitrary elliptic conjugation and the full measurable-class lower bound are written explicitly.

The independent strip proof checks the ceiling increments at alpha=0,1 as well as in the interior, includes negative b, uses the positive determinant for both tails, and uses a first crossing to retain square boundaries. No almost-everywhere-to-everywhere assertion is needed in that proof.

For the finite consequence, checked area normalization, uniform template bounds above the determinant cutoff, use of the older small-determinant template, the continuous upper envelope, direct coverage of actual nonlinear targets, the inverse-controlled finite collar, counting by disjoint fundamental cells, and outer-neighborhood convergence for arbitrary compact label sets. These are symbolic checks, not automated tests.

## Scope and handoff

Only the four authorized I203 research/authentication files, the I203 literature note, and two fully read primary PDFs were written. There were no child agents, alternative models, research code, parameter scans, tests, snapshots, seals, historical replays, ancestor edits, shared-index edits, I31 modifications, staging, commits or publication. Shell/Python use was confined to retrieval, reading/search, permitted record writing, and metadata hashing/JSON assembly.

The runtime identifies GPT-6.1 Sol with high reasoning. The requested ultrafast service tier was not independently exposed. Both acceptance gates, the significance decision and integration remain with the parent. Theorem 1 is offered as the nomination; its known square-covering and finite-retention dependencies are stated openly.
