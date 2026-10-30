# Source-level implementation complete; not acceptance

Unconditional literal negative H-eigenpair for Cooper–Du arXiv2505.10501v1,
pp9–10, compiled and freshly replayed. Credit0. No ledger/count changes, paper,
external access/contact/posting, browser, git command, child, or other-lane edit.

Main endpoint `SteinerReflection.concrete_negative_H_pair` in
`formal/Endpoint.lean` proves:

```text
∃ s lam : ℝ, 5<s ∧ s<8 ∧ x s ≠ 0 ∧ lam<0 ∧
  ∀ i : Fin30, sourceH (x s) i = lam * (x s i)^3
```

`SteinerReflection.source_refutation` pairs the genuine star-tree theorem with
`¬StarHPositivity`. This positivity predicate is explicitly the source question's
specialization to K1,29 at order4. The concrete counterexample therefore refutes
the universal all-tree order4 question, and the proposed universal extension to
all even orders. The certificate does not define a general all-n Steiner library,
claim failure separately at every even order, or make a minimal-order claim.
It does not infer nonsymmetric H-eigenvalues from a quartic's sign.

## Definition chain, with every bridge proved

* `StarMinimum`: `V=Fin30`; mathlib `starGraph 0` and `isTree_starGraph`.
  Edge j is {0,j}. `required t` contains precisely the nonzero j with a terminal
  equal to j and another different from j. Walk connectivity forces those edges
  into every feasible edge subset. The required edges join every terminal pair.
* `SourceMinimum`: **actual `star.Subgraph` objects**, actual `.Connected`, and
  containment of every terminal. `sourceDistance` is the least edge count over
  these objects, with a proved nonempty domain. Edge labels are bijective with
  the actual undirected `S.edgeSet`; `SubgraphSize_eq_edge_ncard` proves the
  count equality. `source_minimum_attained` gives an actual connected minimizing
  subgraph and comparison with every connected competitor using edgeSet.ncard.
  `sourceDistance_eq` proves equality with the required-edge cardinal, including
  all-equal/repeated ordered terminals. No polynomial defines the distance.
* `CutTensor`: minimum-distance coefficient equals the sum of cut indicators;
  exact mixed finite-sum contraction for arbitrary vectors, including all
  repeated indices. No assumed source cut theorem or cubic contraction.
* `Contraction`: A(h,l)=1/15-delta(h,l); literal coefficient C=sum_h M*A and
  H=sum_jkl C*xj*xk*xl. `H_mixed` proves equality to M(e_i,x,x,Ax).
  Finite-sum cut distribution proves both complete orbit formulas.
* `Algebra`: continuity and strict IVT produce the root in(5,8); the factored
  inequality proves d<0; exact algebra gives the common negative scalar.
* `Endpoint`: `sourceM` uses `sourceDistance`, never a polynomial substitute.
  `A_literal` proves A=2/30 minus the identity. The fully unconditional
  negative H-pair uses the exact source tensor and all30 coordinate equations.

Witness x0=s+29 and xj=-1 for j≠0. The proof constructs
lam=29d(s)/(30(s+29)^3), d=2s^3-26s^2+32s+30;
L=86s^3-728s^2+894s+810; P=29d+(s+29)^3L.
P(5)=-85295770 and P(8)=273617240. On[5,8],
d=30-48s+2s(s-5)(s-8)≤-210. Both literal contractions and their common
negative H-scalar are proved; no graph/contraction/root premise remains.

## Validation and reproducibility

`steiner-source-component.zip` is a deterministic SOURCE-ONLY archive: six
mathematical modules, origin-audit source, runner/replay, nine pins, manifest,
and frozen upstream import hashes. No own precompiled files. Fresh extraction
in `verification-fresh` started with zero own oleans and rebuilt serially.
All six mathematical logs are empty; all stages passed strict flags.

The audit exhaustively crosschecks two actual environment inventories and
prints the fully elaborated actual type, origin, transitive axiom closure and
actual unsafe/partial/axiom flags for **118 declarations**, including generated
and private helpers. Axiom union is exactly propext, Classical.choice,
Quot.sound. Every unsafe/partial/axiom flag is false. No sorry/admit/new axiom,
native_decide or unsafe mathematical declaration. Lean4.34.1 binary SHA and
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 plus all8transitive pins checked.
The imported cache's source/olean hashes are frozen; upstream itself was not
rebuilt or independently attested from public source.

Fresh replay peak process-group RSS2703476KiB (2640.113MiB), below2800MiB;
45ms target sampling, CPU210/wall230 per Lean stage, -j1, warningAsError,
autoImplicit=false, -M2700. Python helpers AS512MiB and explicit CPU/file limits;
BLAS1 for build environment. Sampling cannot exclude unsampled transients.
Read `REPRODUCE.md` and `verification-fresh/replay-receipt.json`.

## Honest failures and remaining gates

Initial development imported Mathlib.Tactic wholesale. The guard killed it
at sampled2888552KiB against ceiling2867200KiB. The cap was not raised;
selective imports resolved it. The initial developmental logs were overwritten
by later module attempts; this exact observed failure is preserved here and
in FINAL-RESULT.json. Ordinary elaboration/linter failures were corrected;
the final replay has no warnings. No resource failure occurred in final replay.

Inherited strongest objection: elementary two-orbit star algebra and an
ancillary source question may still be judged modest/routine under the campaign
standard. Formal difficulty does not establish novelty or eligibility. Root's
INVEST adoption authorized this implementation, not acceptance.

Source provenance remains arXivv1 only: authenticated PDF SHA
2475bf1990f404e2bd6bd7e5badf618aaa6dca55199b5648d405aa792c06bab5,
https://arxiv.org/pdf/2505.10501v1. arXiv submission15May2025 versus internal
PDF date13June2025 retained. No target journal version was located by the
inherited preliminary review; that limitation is not cleared here. This lane
made no fresh novelty/registry search and claims no global priority. Frozen
proof/source/review/adoption and inherited HTTP receipts are in `frozen/`,
with pre-copy hash checks in provenance.json. Independent final formal review,
latest source/prior gates, and any manuscript remain root's work. Ancillary
hyperdeterminant sign conjecture untouched. No acceptance or counting claim.
