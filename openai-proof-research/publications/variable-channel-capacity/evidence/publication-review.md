# R009 publication review

Date: 2026-10-09. This is an authoring-agent review, not a new independent reviewer report, external peer review, or formal certificate. No agents were delegated. All preparation occurred in the isolated publication checkout.

## Source dependency

The manuscript assumes exactly the following subset of the pinned companion input: a symmetric posterior-law class containing revealing and uninformative laws, closure under all channel steps in `[0,1]` and finite products independent conditional on a uniform four-state input, and the binary moment saving with coefficient `1/1000`. Observed-mixture closure is available upstream but unused. No closure under limits is required.

The actual source statements were read:

- *A Capacity Criterion for Four-State Potts Reconstruction on Trees*, `build/main.tex`, labels `prop:companion` and `eq:moment-saving`.
- *The Reconstruction Threshold for the Ferromagnetic Four-State Potts Model*, `build/sections/03-cone.tex`, Proposition 3.2, labels `prop:cone-closure` and `eq:moment-saving`.
- The posterior product and channel formulas in `build/sections/02-experiments.tex` were compared with the manuscript definitions.

All five cached upstream files were fetched from immutable raw URLs and verified against their recorded SHA-256 and Git blob hashes at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The manifest records the exact paths. Upstream theorem truth was accepted under the research premise, without auditing its polynomial certificates. The paper states the dependency as Assumption 2.1 instead of presenting it as a theorem proved here.

## Mathematical review

The manuscript combines the complete proof in `frontier/iterations/i08-variable-channel-capacity.md` with the degree-independent strengthening in `i11-locally-finite-capacity.md`. It incorporates the conditioning and joint-independence clarifications in the existing proof reviews. No substantive gap was found in this preparation pass, conditional on the stated input.

The fresh reading checked the following points:

1. The product law uses the density `Z` relative to independent marginal posterior laws. Both moment integrands extend by zero at `Z=0` using `|N_i| <= Z`; a uniform positive denominator is unnecessary.
2. The exact quadratic cancellation gives coefficient seven; the polynomial coefficient bound plus the remainder gives 460 for the third moment. These estimates require symmetry only. Subadditivity is used separately through Assumption 2.1.
3. The cubic change of variable works even when the sum of two moments exceeds three. Finite product closure removes the degree dependence, and finite child sets justify passage to numerical limits without assuming limiting-law membership.
4. The necessity flow has finite mass, is conserved at dead ends, and its potential telescopes even on perfect edges.
5. The sufficiency proof uses only finite truncations. Positive-flow paths extend to rays, giving the profile bound. Degraded terminal experiments belong to the assumed class, and zero-flow branches are jointly uninformative.
6. The deficit estimate bounds `S-b_i` as the sum of the other branch moments. It never obtains this estimate by subtracting two upper bounds. Its triple term is at most `1610 X_v^2 beta_v` after normalization.
7. The replacement of the vertex splitting average by the realized split occurs only inside expectation with a multiplier measurable before the next branch choice. The terminal index is included in the column-kernel bound.
8. The loss bound with `epsilon=10^-4/sqrt(1+A_0^2)` is strictly below one half. The final supremum requires no maximizing flow and covers infinite capacity.
9. Zero-channel pruning uses joint independence of complete removed subtrees. The nonlocally finite counterexample forces every chain flow to zero while revealing the root at every depth.

`validate.py` adapts the existing R009 exact-rational checks and adds a symbolic reduction of the quadratic cancellation, rational constant bookkeeping, and 100 exact ray telescopes. Its tests pass, including zero-normalizer examples. These checks support selected finite steps and are not a proof of the infinite-tree theorem or the upstream assumption.

## Literature and novelty limits

The existing bounded primary-source audit is `frontier/reviews/i08-variable-capacity-novelty-r3.md`, with the locally finite review in `i11-locally-finite-capacity-r4.md`. Their AI acceptance labels were not treated as human verification. Nonlinear capacity, its series law, the necessity flow construction, and the near-perfect-ray obstruction have precedents. The claimed contribution is the uniform four-state sufficiency argument conditional on the posterior-class input. The locally finite formulation and degree-independent estimates remain in this one paper, rather than being counted as additional discoveries.

Primary bibliographic pages checked during manuscript preparation:

- [Pemantle–Peres](https://arxiv.org/abs/math/0503137): Annals of Probability 38 (2010), 184–206; DOI 10.1214/09-AOP482.
- [Sly](https://arxiv.org/abs/0811.1208v1): the cited 2008 preprint version.
- [Mossel–Sly–Sohn](https://arxiv.org/abs/2212.03362v2): the cited 2025 revision.

A bounded search on 2026-10-09 for variable-channel four-state reconstruction/capacity and inhomogeneous Potts reconstruction did not identify another exact matching theorem. This search does not prove novelty. The bibliography uses primary papers and the pinned upstream manuscripts; search summaries are not mathematical evidence.

## Editorial and disclosure decisions

The paper uses `amsart`, a short abstract, numbered statements and proofs, five substantive sections, references, and the author affiliation. There is no table of contents, project-status section, internal finding identifier, submission checklist, or internal review label in the manuscript.

The requested [unslop guidance](https://github.com/cursor/plugins/blob/main/pstack/skills/unslop/SKILL.md) was read and applied to the prose. The single AI acknowledgement follows the first paper's established wording. Its precedents were already recorded in that paper's editorial review: [Lacabanne–Tubbenhauer–Vaz](https://arxiv.org/html/2412.01283v3) and [Bizeul–Klartag–Lehec](https://arxiv.org/html/2610.05474v1). It names the actual roles of the tools without implying human or formal proof verification.

The PDF was compiled with Tectonic 0.17.0, extracted to text, and all nine final pages rendered and inspected. The orphaned affiliation page in the first build was removed by deleting redundant prose. The final log has no overfull/underfull boxes, unresolved references, or missing-character warnings. The source ZIP was also built after extraction into a clean directory. This review records the preparation stage, before external publication. The subsequent authorized Zenodo publication is recorded in `zenodo-publication.json`; no peer-review acceptance is claimed.
