# Selected cascade family and literal rate refutation

**Assigned formal component CLOSED; investment only, not acceptance.** Counts remain
3/30 additional, 33/60 total, candidate credit 0. Solo implementation, no children,
git operations, other-lane/shared edits, browser tabs, network acquisition,
external contact, posting or uploading.

Import `SelectedCounting` in namespace `CascadeRate`. All supplied dependencies
and the runner are byte-identical copies. The complete ordinary PROOF.md,
ADOPTION.md and both supplied review.md files were read. Adoption authorizes
investment despite the superseded preliminary HOLD; no new literature clearance
or source truth audit is claimed.

## Closed interfaces

`SelectedCode k = Fin (blockCount k) → Fin (k-2) → Bool` consists of B independent
binary words. `selectedWord` is literally anchor k followed by the flattening of
blocks `[true,true] ++ List.ofFn (u i)`, then `r+H` true letters. Each block has
length k, with **no extra trailing 1**. The frozen `anchor_literal` identifies
the anchor with `(01)^k00`.

For every k≥3 and every code:

- `selectedWord_length`: length = depth k.
- `selectedWord_injective`, `selectedCode_card`, `selectedFamily_card`: exactly
  2^freeCount k distinct words. Injectivity/cardinality also cover zero blocks.
- `anchor_prefix_index`: any two anchor prefixes of one word have equal indices.
- `bottom_context`, `selectedWord_context`: actual finite-context membership,
  including exclusion of all other bush anchors and the spine.
- `selectedWord_suffix_noninternal`: for every 0<i<word.length, the literal
  suffix `word.drop i` is noninternal in sourceTree.
- `selectedWord_lisIndex`, `selectedWord_lis`, `selectedWord_alphaLIS`: genuine
  least-shift LIS index = word.length, LIS = [], alpha-LIS = [true].

The all-order combinatorial bridge is `blocked_tail_no_spine`: induction on an
arbitrary list of length-k blocks starting 11, with an arbitrary terminal run
of length≥3, excludes a length-2k alternating prefix at **every** suffix position.
For a position inside a block the *next* block's forced pair (or the terminal
pair) lies within the required window; dropping a whole block invokes induction.
This includes zero blocks. `selectedWord_shift_no_spine` handles initial-anchor
positions separately: shift1 starts true, shifts2..2k meet 00, shift2k+1 meets
the tail's 11, and later shifts use the tail theorem. For a putative internal
suffix, earlier bushes j<k lie entirely in terminal ones; later j≥k require the
forbidden alternating prefix. Spine suffixes are excluded by terminal ones/equal
pairs, including lengths1 and2. No finite diagnostic is used for these claims.

`selectedFunction` injects the family into the actual `Fin (depth k) → Bool`
index type, and `selectedFunction_word` proves exact `List.ofFn` recovery.
`selectedWord_weight` uses the frozen genuine fair product cascade to obtain
(1/2)^(depth k-1). `selected_kappa_lower` proves, with no residual premise:

    ∀ k≥3, (1/2 : ℝ)^(deficit k) ≤
      kappa sourceTree (fairAssignment sourceTree) [true] (depth k).

Its proof compares the sum over the injective finite image to the actual full
sum, proves every remaining summand nonnegative, evaluates cardinality, and uses
`deficit_add_free` and exact real power arithmetic. `sum_fin_cast` is an elementary
proved change of finite function index under equality of lengths; it resolves
literal Eq.(5)'s `1+depth k-1` grading. No asserted counting identity, surrogate
sequence, altered source definition or residual suffix hypothesis is used.

The frozen depth analysis then yields the closed endpoints:

    fixed_kappa_not_geometric :
      ¬ GeometricDecay (kappa sourceTree (fairAssignment sourceTree) [true])
    source_geometric_rate_refuted : ¬ SourceGeometricRateClaim

The latter uses the frozen actual sourceTree, positive normalized assignment on
finite and infinite contexts, no-infinite-stable-subtree theorem, and actual
`one_contextAlphaLIS`. One tree, one assignment, one fixed alpha-LIS are used.

## Strict replay and audit

From this lane run:

    python generate_audit.py
    python replay_all.py
    python exact_check.py
    python dependencies.py

`replay_all.py` recreates an isolated directory from only .lean sources and the
byte-identical supplied runner, records its source-only inventory before any
compilation, and compiles serially. Its LEAN_PATH contains that fresh formal
folder plus the pinned cached package libraries, never local development oleans.
All eight modules passed `autoImplicit=false`, `warningAsError=true`, targeted
imports, default bounded Lean heartbeats, a 180-second wall deadline per call,
and a 3GiB sampled process-group RSS ceiling with 0.15-second sampling. Final
maximum sampled group RSS: **2,609,393,664 bytes**. Sampling is not a hard address
space cap for Lean. All call times were below3 seconds. Exact commands, cwd,
source hashes, times and measurements are in `replay/verification/receipt.json`.

`formal/Audit.lean` displays every one of 144 explicit declarations in the seven
non-audit modules, plus all eight explicitly named structure fields; generated
recursors/equation lemmas are not separately inventoried. All 152 actual types
and axiom outputs were inspected. `audit-results.json` independently parses every
output: only propext, Classical.choice and Quot.sound occur. The inventory includes
same-line simp attributes (an initial inventory omission was fixed before final
replay). No sorry, admit, custom axiom, unsafe, native_decide or hidden bridge.

The executable SHA256 matches the supplied e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550.
Mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612 is supplied pin metadata;
no git operation was used to independently identify its checkout. The recursive
source/dependency manifest contains3228 modules and hashes every source and
available olean (none missing). Exact integrity/audit bookkeeping enforces
hard512MiB AS,25CPU seconds, BLAS/OMP/MKL/NumExpr1. No mathematical numerical test
was run or substituted for proof. Ten frozen input hashes match before/after.
Development compile errors and retention limits are in DEVELOPMENT-ERRORS.md.

## Remaining scope and strongest gap

There is **no remaining proof premise in the assigned rate-refutation endpoint**.
The strongest remaining project gate is independent adversarial interface/source
and final packet review by root, followed by its paper/acceptance process. This
lane does not certify novelty, publication readiness or acceptance.

Optional formal Kraft summability, the limsup-root equality, and tail-series
nongeometricity are not delivered here. In particular the ordinary proof's
summability assertion remains ordinary-only until separately formalized. Those
optional statements are not needed for the fully proved negation of the explicit
rate clause. Bare convergence is neither refuted nor solved in general.
