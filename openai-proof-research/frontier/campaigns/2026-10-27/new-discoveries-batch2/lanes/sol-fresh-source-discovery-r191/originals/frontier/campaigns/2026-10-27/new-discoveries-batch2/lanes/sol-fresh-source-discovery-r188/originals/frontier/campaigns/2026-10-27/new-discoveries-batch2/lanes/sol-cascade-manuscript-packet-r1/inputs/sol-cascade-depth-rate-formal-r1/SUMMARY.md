# Cascade depth/rate arithmetic component

**Closed component PASS, formal investment only; no source-theorem acceptance.**
Counts remain 3/30 additional, 33/60 total, candidate credit 0. Solo implementation;
no children, git operations, shared edits, browser activity, network acquisition,
or publication. Full candidate PROOF.md, both supplied review.md bodies, root
ADOPTION.md and frozen definitions were read. Root's ADOPTION supersedes the
first review's earlier investment HOLD; its bounded novelty limits persist.

Import `DepthAnalysis` (namespace `CascadeRate`). `DepthDefs.lean` and
`run_lean.py` are byte-identical copies of the root's files. Actual definition
SHA256 is f0f934f04a96241742e68592ab3915c5d103dca446a863731b69085ea8500bd7;
the supplied `77ae829b08` label was treated as assignment metadata, not a file
SHA256. Actual freeze-manifest hash is in frozen-before.json. No git identity
was independently established.

The frozen definitions are depth(0)=0,
depth(k+1)=(k+1)^2*(depth(k)+(k+1)+10), anchorLength(k)=2k+2,
terminalLength(k)=depth(k-1)+3, remainderLength(k)=depth(k)-anchorLength(k)-
terminalLength(k), blockCount(k)=remainderLength(k)/k,
tailRemainder(k)=remainderLength(k)%k, freeCount(k)=(k-2)*blockCount(k),
deficit(k)=depth(k)-1-freeCount(k). Every subtraction here is Nat subtraction.

## Exact exported interfaces

`DepthArithmetic.lean` proves:

- `depth_zero`, `depth_eq k (1≤k)` give the exact recurrence.
- `depth_lower k`: k²(k+10)≤depth k, including k=0.
- `depth_strictMono`: StrictMono depth; `index_le_depth k`: k≤depth k.
- `room k (3≤k)`: anchorLength k+terminalLength k+1≤depth k.
- `decomposition k (3≤k)`: depth k=anchorLength k+blockCount k*k+
  tailRemainder k+terminalLength k.
- `tail_lt k (3≤k)`: tailRemainder k<k.
- `free_le k (3≤k)`: freeCount k≤depth k-1.
- `deficit_add_free k (3≤k)`: deficit k+freeCount k=depth k-1.
- `previous_bound k (1≤k)`: depth(k-1)*k²≤depth k.
- `deficit_bound k (3≤k)`: deficit k*k²≤(2k+1)*depth k+(3k+5)*k².
- `deficit_linear_bound k (3≤k)`: deficit k*k≤4*depth k.

`DepthAnalysis.lean` proves:

- `depth_atTop`: Tendsto depth atTop atTop (Nat).
- `depth_real_atTop`: Tendsto (fun k => (depth k : ℝ)) atTop atTop.
- `previous_ratio k (1≤k)`: (depth(k-1):ℝ)/depth k≤1/(k:ℝ)².
- `deficit_ratio_zero`: Tendsto (fun k => (deficit k:ℝ)/depth k) atTop (𝓝 0).
- `depth_beats_geometric (C r:ℝ) (0<C) (0<r) (r<1) (n0:ℕ)`:
  ∃k, 3≤k ∧ n0≤depth k ∧ C*r^(depth k)<(1/2:ℝ)^(deficit k).
- `abstract_no_eventual_geometric (f:ℕ→ℝ)` assumes only
  ∀k,3≤k→(1/2:ℝ)^(deficit k)≤f(depth k), and concludes
  ¬∃C r:ℝ,0<C ∧ 0<r ∧ r<1 ∧ ∀ᶠn in atTop,f n≤C*r^n.

The last theorem is explicitly an **abstract helper**, not SourceClaim. The
literal κ lower bound, words, tree, source cascade identification and probability
normalization belong to root/other components. No residual limit or eventual
bound premise occurs in `depth_beats_geometric`. Summability is neither proved
nor claimed here. No literature novelty or separate credit is claimed.

## Proof and strict audit

Integer proofs use recurrence, positive room, Euclidean division, exact Nat
subtraction conservation and bounded polynomial arithmetic. The stronger linear
bound supplies 0≤deficit/depth≤4/k eventually. Squeeze gives the real limit.
For the endpoint, log C/depth-(deficit/depth)*log(1/2) tends to zero, hence is
eventually less than -log r>0. Multiplying by positive depth and using log powers
proves the strict inequality. Filter intersection supplies k≥3 and depth≥n0.
The abstract transfer contradicts any eventual bound at this chosen depth.

All 19 theorem types and all eight definition types, and their `#print axioms`
output, were personally inspected in both development and fresh replay.
`Checks.lean` lists all exports; replay-Checks.log records the complete types.
Every axiom set is contained in {propext, Classical.choice, Quot.sound}; there
are no unproved bridges, custom axioms, sorry/admit, unsafe, or native_decide.
Both local modules explicitly set autoImplicit false and warningAsError true.
No unbounded proof search or raised heartbeat ceiling is used.

Pinned executable path and hash are checked by exact_check.py; mathlib revision
is the supplied d13f23b723b8a846827a245b89c10fc7d3f11612. External pinned cached
upstream oleans are used; our own modules are freshly compiled from source in
`replay/`, with no inherited local oleans or development-directory LEAN_PATH.
`replay_all.py` deletes replay/, copies only .lean files and byte-identical runner,
and serially compiles DepthDefs, DepthArithmetic, DepthAnalysis, Checks.
Each lean call has a 180-second wall limit and sampled RSS enforcement at 3GiB.
Final strict replay peak RSS was below 2.56 billion bytes. All four exit codes 0.

The initial broad Mathlib.Tactic import exceeded the RSS ceiling and was killed;
resource-failure.json records the observation. Replacing it with targeted imports
resolved this without increasing limits. The dependency manifest script initially
misparsed `import all` and documentation examples; header-only nested-comment
parsing fixed that bookkeeping error, without changing proof sources or limits.
Exact diagnostics use 512MiB AS, 25 CPU seconds, BLAS/OMP/MKL/NumExpr=1. They
check frozen bytes, binary SHA256, and 200 exact instances for bookkeeping only.
No finite instances enter any Lean proof.

## Reproduction and evidence

From this lane run `python replay_all.py`, `python exact_check.py`, and
`python dependencies.py`. Audit receipts contain exact argv/cwd, exit code,
wall time, sampled RSS, and root input hashes. dependency-hashes.json binds the
recursive explicit import closure (plus implicit Init), source and available
olean hashes; provenance.json binds component sources and receipts. The root
frozen definitions/runner/adoption/manifest match their initial hashes after all
work. supplied-inputs.json binds proof/review bodies (recorded after reading;
not misrepresented as a pre-read snapshot).
