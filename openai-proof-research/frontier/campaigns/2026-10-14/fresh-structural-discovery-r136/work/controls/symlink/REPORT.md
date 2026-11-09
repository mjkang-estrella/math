# r136 handoff — PREFREEZE / no nominee

2026-10-20. Runner: Codex / GPT-6 Astra, high reasoning, default service tier. No full theorem was frozen or nominated. No correctness, contribution, acceptance, priority or campaign-count gate is assigned. The campaign remains at the supplied 18/20 baseline; this packet adds no count.

The sustained direction was exact-marginal distributions on cut-thin spanning trees: for every connected loopless undirected multigraph and every point x of its spanning-tree polytope, can a distribution with edge marginals exactly x be supported entirely on trees satisfying `|T ∩ δ(S)| ≤ A x(δ(S))` for an absolute A? This question remains unresolved here. The elementary and conditional derivations below are supporting progress, not substitute nominees.

## Mathematical work completed

The full arguments are in [derivations.md](packet/public/derivations.md).

1. Exact marginal preservation is equivalent, by separation and fixed tree size, to cost-factor-one selection from the same thin family for every nonnegative edge cost. The pinned source already gives a distribution with marginals at most Kx, where K is its thinness/cost constant. That routine consequence is explicitly credited.
2. A fully explicit K4 example has optimal single-tree thinness **15/13** and optimal exact-marginal-support threshold **5/3**. Its edge vector is `(1,1,4,4,1,4)/5` in order `01,02,03,12,13,23`; a three-tree mixture realizes the threshold. A degree/cut proof establishes the lower bound independently of enumeration.
3. On a triangle, `x=(1-p,1-p,2p)`, `0<p<1/3`, forces a unique tree distribution. The two optimum values are `1/(1-p)` and `2/(1+p)`, with ratio approaching two. Cycles and simple cactus graphs admit exact-marginal 2-thin distributions. These are elementary calculations, with no literature novelty claim.
4. One-vertex joining takes the maximum of the constituent thresholds. It cannot amplify those examples into an unbounded obstruction. Uniform maximum-entropy sampling and arbitrary extraction from an exact tree packing also fail as literal shortcuts; their failures do not exclude other constructions.
5. A complete conditional calculation shows how **exact** balanced bisection of every union of q trees, with summable relative cut discrepancy, would yield the desired distribution. The product bound is independent of q and graph size, and compactness extends dyadic convex combinations to real x. The required exact bisection was not established or nominated.

## Strongest integrated comparison and remaining obligation

The pinned existence and algorithmic companion proofs were studied at their operative normalization, extraction, two-sided split, iteration and fractional cost-rounding interfaces. Both halves of the source split are controlled; fair random selection of a half preserves the included edges in expectation. Those operations are already paid. The unresolved issue is that extraction first restricts to a smaller packing and later tree selection discards edges: a contained near-full packing is not an exact partition of all original edges into bases.

The actual primary proofs of Oveis Gharan–Saberi deletion/cheapest selection, CVZ swap rounding and tails, and Klein–Olver aligned laminar cost-preserving rounding were read. Combining cost preservation with separation already yields exact marginals for aligned laminar constraints. The general alignment reduction changes the fractional point. Late reads of Oveis Gharan–Saberi v4 and the 2026 Klein–Olver–Yeoh assembly/alignment proof are disclosed; neither is portrayed as a pre-draft read.

What remains is a uniform cost-factor-one selection theorem or equivalent exact-marginal construction. Exact tree-packing bisection with cut-controlled repair is one sufficient route, but no such repair estimate was obtained. A negative result would instead require an unbounded separating-cost family; the K4/triangle calculations and their one-vertex joins do not provide one. No impossibility, current-open-status or worldwide-priority conclusion is drawn.

## Evidence and preservation limits

[reading-limits.md](packet/public/reading-limits.md) gives exact source/primary/history extents, versions, late reads, search exclusions and rights. Forty pinned raw source text blobs are authenticated against the complete tree and by Git blob/size/SHA256. Five primary versions are preserved privately. Source geometry interiors, the 2026 polygon-cover proof and several older history bodies have explicit partial/unread limits. This is not an exhaustive project or literature clearance.

The abandoned family-180 route was stopped after source and actual Hamiltonian affine-span/count history reads. The r54 metric-routing and r107 directed-arborescence frozen targets were read and left unchanged. T165P135's adopted conditional TECHNICAL disposition was read in full and not reopened.

Twenty-nine stable captured originals matched their initial bindings at the final preseal comparison. Initial mandatory reads preceded those first bindings; the timing is disclosed. The mutable campaign ledger changed during the round and is recorded separately, not treated as an immutable proof input. No entire parent-directory snapshot is claimed. An initial filename-only inventory exposed one active-root path; no active file body was opened. All writes stayed in the exclusive root.

The exact finite check enumerated K4 independently by edge subsets and Prüfer words, checked all cuts and the explicit mixture, and checked 29 rational triangle parameters. General claims rely on the written arguments. Computation and artifact integrity are not mathematical gates. There is no independent adversarial review, formalization or manuscript/release stage in this handoff.

## Local seal and verification

`packet/MANIFEST.json` binds the exact packet tree. `FINAL.json` binds that manifest and this outside report. All three full detached SHA256 anchors are returned in the final handoff. The read-only command is:

```
python -B packet/public/verify.py --root /absolute/path/to/this/root \
  --project /home/mj-kang/Documents/Dev/math/openai-proof-research \
  --final-sha256 FULL_FINAL_SHA256 \
  --manifest-sha256 FULL_MANIFEST_SHA256 \
  --report-sha256 FULL_REPORT_SHA256
```

`packet/public/run_copied_controls.py` accepts the same arguments and creates fresh copies only under this root's `work/controls`. It checks an intact copy and seven mutations: payload, extra file, missing file, each of the three anchor files, and a symbolic-link substitution. Its postseal receipt is `work/control-receipt.json`, outside the sealed packet; it is not retroactively inserted into the manifest. The final handoff reports observed results. Scratch is unsealed; original mathematical preparation scripts/data are also copied into sealed private/preparation. Public original prose/code and private third-party/project bodies remain separate under their original rights.
