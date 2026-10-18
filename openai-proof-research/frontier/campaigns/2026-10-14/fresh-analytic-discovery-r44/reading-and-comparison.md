# Reading, source operations, and limits

Author: Myeongjin Kang; original prose CC BY 4.0. This is an author ledger,
not an independent review. Downloaded bodies are private and excluded
from Git/releases. Acquiring or hashing a file is not reading its proof.

## Pinned source and changed interfaces

Pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The complete preprint tree
contains one manuscript in family 221, directory
`The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026`.
Its 15 mathematical/build text blobs and, after the parent's completeness
check, its nonmathematical .gitignore were fetched and Git-blob/SHA256
checked; receipts record the exact paths. The latter was not part of the
initial 15-blob acquisition. There is no second pinned companion hidden by
using a truncated repository tree.

Personally read in full in this round: build/sections/introduction.tex,
model.tex, overview.tex, cavity.tex, perturbations.tex, trees.tex,
decorrelation.tex, comparison.tex, reduction.tex, consequences.tex,
upper.tex, and build/references.bib. The wrapper, glyph mapping and README
were acquired but not read as mathematical proof. The stipulation, not
our checks, supplies upstream truth.

Exact locators for the localized transfer in proof.md §5:

| Operation | Pinned source location | Change and verification |
|---|---|---|
| Perturbation family | perturbations.tex 26–69, `pert:parameters`, `pert:factor` | Uniform site from cavity set I, same Poisson intensity and independent mark process. |
| Thermal differentiation | perturbations.tex 107–162, `pert:second-derivative`, `pert:thermal-bound` | No graph law used. Constant includes m_1^−1/2 and depends on fixed L. |
| Root variance and convex derivatives | perturbations.tex 164–247, `pert:root-variance`, `pert:convex-bound` | Replace iid physical-edge Efron–Stein part by matching-switch martingale; keep independent coupling/field/Poisson-label parts. |
| Parameter selection | perturbations.tex 250–312, `pert:selection` | Two-vertex increments, good-size subsequence and sparse bad increments are proved separately. |
| Palm insertion and extraction | perturbations.tex 314–547, `pert:palm-expression`, `pert:palm`, `pert:tree-identity`, `pert:mark-selector` | Insertion samples I. Its empirical product is |I|^−1 sum over I. The inserted object is a perturbation factor, not a physical edge. |
| Kernel insertion/logarithmic expansion | trees.tex 48–244, `tree:insertion`, `tree:log-expansion` | Arbitrary probability kernels; no physical graph assumption. |
| Charging and shape laws | trees.tex 245–525, especially `tree:regular-shapes` | Same grid j/L and same tree laws; no spatial coordinate count in constants. |
| Entire decorrelation induction | decorrelation.tex 1–620, `decor:contractions`, `decor:conditional-concentration`, `decor:overlap-concentration` | Replace finite normalized Hilbert space R^N by R^I; norm-one spin vectors, projections and kernel contractions persist. All required colored identities supplied by the preceding row. |
| Trial encoding and product patterns | comparison.tex 19–158, `comp:encoding`, `comp:patterns`, `comp:shape-error-bound` | Uniform observed coordinate is in I; full root is independently copied for each trial label. |
| Insertion comparison | comparison.tex 160–end, `comp:insertion-comparison` | Two stars and d bonds, each using 2d labels; bounded deterministic insertion sizes remove the Poisson-count cutoff. |

These are exact proof operations, not an invocation of the source's
Poisson-model theorem for a regular graph. The source already supplies
the difficult hierarchy/decorrelation mechanism. Any contribution
assessment must charge that work to the source.

## Primary antecedents actually inspected

1. [Lelarge–Oulamara, arXiv:1708.02457v2](https://arxiv.org/abs/1708.02457v2),
   *Replica Bounds by Combinatorial Interpolation for Diluted Spin Systems*.
   Extracted lines 1–235 (model/hypotheses), 476–1573 (Theorem 3 and all
   of §§4–6) read. This includes the free-port matching model and exact
   uniform insertion Lemma 4, Proposition 6's replica convexity inequality,
   stopped-walk interpolation, endpoint/error estimates, and the weighted
   finite-RSB extension/proof of Theorem 3. It pays the regular-degree
   upper bound at every finite depth. Its use of free-port averages and
   weighted power means also means those operations cannot be claimed
   new here. Pages between lines 236–475 were not read in full; they
   concern preceding formulas/examples, not additional proof credited here.

2. [Coja-Oghlan–Perkins, arXiv:1808.03440v1](https://arxiv.org/abs/1808.03440v1),
   *Spin systems on Bethe lattices*. Lines 170–284, 550–676 and
   2260–2547 read, including regular model/kernel formula statements,
   positivity, the §6.1 reservoir construction, and §6.2/Lemma 6.4's
   operative cavity-completion comparison. The v2/v3 download attempts
   returned 404; the saved and read body is v1. This work already owns
   opening cavities, coupling different regular sizes through a reservoir,
   and lower-bound insertion formulas. Its displayed reservoir parameter
   ω is fixed while n→∞, then made large. We do not assert that no
   refinement of that construction could replace ours. Its invariance
   space D* is not identified there with all finite independent-label
   hierarchy trials; that is the distinction relevant to T221R. The rest
   of its kernel compactness/invariance proof was not read in full here.

3. [Concetti, arXiv:2508.17049v1](https://arxiv.org/abs/2508.17049v1),
   *Properties of the full-RSB free energy functional of the Ising spin
   glass on random regular graphs*. Lines 25–285 and references
   2810–2845 read. This is the Rademacher, zero-field regular model.
   Its finite-RSB inequality and Theorem 1.3's larger Brownian-functional
   bound are upper bounds; equality (1.26) is stated as a conjecture.
   Its BSDE proof is not claimed read. This is a theorem-level distinction,
   not a claim that our packet independently resolves or identifies every
   part of its larger variational space.

4. [Franz–Leone–Toninelli, cond-mat/0307367v2](https://arxiv.org/abs/cond-mat/0307367v2),
   *Replica bounds for optimization problems and diluted spin systems*.
   Lines 45–180 read. It explicitly restricts its exposition to replica
   symmetry for simplicity; this packet uses LO's actual arbitrary-depth
   proof instead. No whole-body reading of FLT is claimed.

5. [Janson, math/0609802v1](https://arxiv.org/abs/math/0609802v1),
   *The probability that a random multigraph is simple*. Lines 1–150
   and 1172–1298 read, including Theorem 7.1, its complete displayed
   factorial-moment proof, and Remark 7.2. This pays the fixed-degree
   simplicity probability used in proof.md §8. The more general high-degree
   proof elsewhere in the paper is not needed or claimed read.

The 349 primary/source screen and its limits are separately recorded in
screen-349.md. Nifa's author PDF was read only in the stated introduction
and §7.2–§7.3 ranges; its §§2–6 were not read. The primary manifest gives
hashes, not broader reading claims.

## History and chronology

The structural-r39 history index was used as a pointer inventory. Its
keyword mode rejected current shared-ledger drift; that rejection was
not bypassed or called a successful current search. Its unchanged
family-only pointers for 221 list the r32 Levy-spin abstract lead.
The actual r32 checkpoint and reading-limit passages were read: no
regular-degree finite-hierarchy target was developed there. Fresh title,
path-component and standard-name searches covered canonical iterations
and authored campaign Markdown outside private/snapshot/input copies.
The broad matching/regular query generated unrelated switch-chain and
viscosity hits, not an exclusion or a novelty certificate. Acquisition
receipts/source paths were also checked against the family pointers.
No worldwide novelty is inferred from absent search matches.

349 was screened first and rejected as source-paid equality/compactness
operations, without a scope freeze. 119 and 239 were withdrawn on actual
developed-history passages before substantive source work. T221R's scope
was fixed at 2026-10-18T05:44:52Z, after operative reading and the pool
idea, before proof assembly. checkpoint.md deliberately preserves the
earlier incomplete state; proof.md is the later proposed full proof.

Parent assistance: root checked §§2–4 author-side, pointed out the
fixed-L thermal constant, and supplied the exact normalization (3.6).
These were checked and incorporated with attribution. Root assistance is
not an independent gate. No external proof/contribution/formal review
has been passed in this packet.

## Precise prospective contribution

The proposed added bridge is simultaneous use of a mesoscopic pool of
distinct degree-deficient vertices and localized hierarchy perturbations,
with sqrt(n)≪s_n≪q_n≪n. It includes the nonuniform completion density
estimate Var W=O((q_n+1)/n²), its covariance control against a root log
of variance O(n), exact star resampling, and sparse-index low-increment
selection. Generic graph opening, replica convexity, hierarchy calculus,
score concentration, overlap induction, and truncation are not new claims.

Separate contribution review may reasonably decide whether this bridge
is substantial or a technical extension of paid constructions. The author
does not decide that gate. The proposed full theorem has no narrowed
temperature, field, coupling, size, hierarchy, or graph-model scope.
