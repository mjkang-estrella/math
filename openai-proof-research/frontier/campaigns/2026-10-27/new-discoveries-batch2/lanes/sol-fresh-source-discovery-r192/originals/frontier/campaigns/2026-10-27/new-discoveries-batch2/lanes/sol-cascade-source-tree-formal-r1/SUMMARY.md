# Cascade source model and tree component

Assigned component **PASS**, formal investment only. Counts remain 3/30 additional,
33/60 total; candidate credit 0. This is not a full source refutation, acceptance,
novelty certification or finished paper.

`formal/SourceDefs.lean` and `formal/TreeConstruction.lean` are the integration
sources. Namespace `CascadeRate`; import `TreeConstruction` for the complete
component. `DepthDefs.lean` and `run_lean.py` are byte-identical frozen copies.
No other lane is needed to compile these modules.

## Source interfaces

`Word = List Bool`, with false=0 and true=1. `SourceContextTree` carries its actual
node set, prefix closure, internal root, saturation and countability of the actual
right-infinite branches. Internal means having a child; finite contexts are
nodes without children; infinite contexts have every finite prefix in the tree.
The internal-root presentation implements the source's exclusion of the
root-only tree: `root_internal_of_nontrivial` derives it from a nonempty word in
a prefix-closed node set, and `nontrivial` proves the converse witness `[false]`.
`contexts_countable` includes finite and infinite contexts.

`cont T w` has an actual unique finite context prefix for every noninternal finite
word (`cont_spec`, `context_prefix_unique`). Its arbitrary value on internal
inputs is never used by a cascade factor. `lisIndex` is the **least positive**
shift reaching an internal suffix. `lisIndex_spec`, `lis_maximal` and `lis_strict`
prove the actual longest internal strict suffix specification. `alphaLIS` is the
preceding letter followed by that suffix (`alphaLIS_preceding_letter`), with
`alphaLIS_noninternal` on the noninternal source inputs used in cascades/series.

`ProbabilityAssignment` assigns a strictly positive normalized two-letter law to
every finite **and** infinite context. `fairAssignment_law` is 1/2 on both sorts.
`cascade` is the genuine zero-based product of
`q_cont(w.drop(k+1))(w[k])` for `k < lisIndex T w - 1`.
`cascade_factor_valid` proves both in-range letter access and noninternality of
every context lookup. `cascade_nil` gives the empty-word convention.
`cascade_fair_halfpower` proves the exact weight
`(1/2)^(w.length - (alphaLIS T w).length)` for nonempty words.

`kappa T q s n` is the literal Eq.(5) finite sum over length `|s|+n-1` words,
filtered by finite-context membership and actual alpha-LIS `s`. It enumerates
all functions `Fin (|s|+n-1) → Bool` through `List.ofFn`, so each such word occurs
once. The source grading applies at n≥1; the total Lean function also has a value
at 0. No abstract surrogate sequence is substituted.
`GeometricDecay` requires C>0, 0<r<1 and an eventual `f n ≤ C*r^n` bound.
`SourceGeometricRateClaim` states the binary rate clause, not the separate
summability conclusion. Bool is a permitted finite alphabet of the source;
a counterexample here would instantiate its universal assertion. No negation
of this claim is proved in this component.

## Explicit tree and endpoints

`alternating`, `spine`, `anchor`, `constructionInternal` and `constructionNodes`
are literal definitions of the requested construction. `spine_even` and
`anchor_literal` identify the anchors with `(01)^k00`; bush indices satisfy k≥1
and internal bush lengths are strictly below the frozen `depth k`.

* `constructionNodes_prefix`: prefix closure.
* `construction_internal_exact`: internal nodes are exactly the prescribed I.
* `construction_root_internal`, `construction_saturated`: nontriviality and saturation.
* `one_leaf`, `zerozero_leaf`: 1 and 00 are finite contexts.
* `alternating_branch`, `unique_infinite_branch`: exactly one infinite context.
* `sourceTree`: fully admissible `SourceContextTree`, no existence premise.
* `one_contextAlphaLIS`: `[true]` is an actual context alpha-LIS.
* `short_shift_subsets`, `finite_shift_subsets`: the generic elementary statement.
* `construction_no_infinite_shift_subtree`: every prefix-closed, shift-closed
  node subset is finite, even without saturation.
* `sourceTree_no_infinite_stable_exists`: no infinite literal shift-stable
  `SourceContextTree` contained in this tree.

The stable-subset proof uses that every node of length≥3 starts 01 and neither
10 nor11 is a node. A 3-letter prefix 01a would shift to forbidden 1a. Thus every
word in such a subset has length≤2. No König lemma is used.

Branch uniqueness also needs no depth-growth estimates or other arithmetic
lane. A prefix differing from the alternating spine bounds all possible bush
indices for its extensions. Their finitely many natural heights have a finite
sum; a longer branch prefix contradicts every possible bush height. Thus the
proof works for arbitrary assigned finite bush heights and in particular the
frozen depth recurrence. No all-index depth-growth bridge is left open for tree
admissibility.

## Validation and limits

Run `python verify.py` from this lane for serial bounded compilation. The
completed isolated replay is in `replay/`, created from only `.lean` sources and
the frozen runner, with no inherited oleans for our modules. The runner's local
search path is this fresh directory plus the pinned package build libraries.
Four modules compiled with `autoImplicit=false`, `warningAsError=true` and
120-second per-module wall deadlines. Fresh maximum sampled Lean RSS was
1,860,915,200 bytes, below 3 GiB. Commands, timings and RSS are in
`replay/verification/receipt.json`; initial source-only contents are recorded.

All 89 explicitly authored declarations (including frozen definitions, excluding
an exhaustive inventory of generated recursors/projections) have displayed
types and `#print axioms` outputs in `replay/verification/Audit.log`. All exported
authored theorem types and every displayed axiom list were personally read.
Only `propext`, `Classical.choice` and `Quot.sound` occur. No unproved bridge,
`sorry`, `admit`, custom axiom, unsafe declaration or native decision is used.
Source/dependency hashes and supplied revision metadata are recorded separately.

The initial umbrella `import Mathlib` exceeded the resource ceiling and was
killed; targeted imports fixed it without raising limits. The observed failure
measurement and development-log retention limitation are in `provenance.json`.
No numerical/exact diagnostic was run or used as a proof.

The candidate proof, actual published definitions/rate clause, both independent
reviews and root adoption were read. All 27 frozen input file hashes match
before/after. There was one setup boundary mistake: an empty temporary file was
created at campaign root and immediately removed. No persistent shared edit,
git operation, child agent, browser, network publication or external contact
occurred.

The selected leaf suffix family, counting, nongeometric analytic assembly,
summability certificate and final source endpoint remain root integration work.
They are not premises of the theorems delivered here and are not claimed proved.
