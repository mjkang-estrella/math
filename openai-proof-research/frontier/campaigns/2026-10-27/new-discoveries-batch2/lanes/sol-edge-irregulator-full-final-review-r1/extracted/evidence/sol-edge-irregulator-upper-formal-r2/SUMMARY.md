# Upper witness complete — no source refutation claimed

Campaign accepted7 additional/37 total, candidate credit0; no counts or acceptance changes. Solo implementation restricted to this lane. No paper, git operations, children, network/browser/account actions, external posts, or other-lane writes. The independent lower worker's lane was neither read nor used.

## Exact unconditional interfaces

Import `Upper` (imports `UpperDegrees`, `UpperWitness`, then the inherited component). All new names are in `EdgeIrregulator.Upper`; `t : ℕ`, `i : Fin t`, `v : Fin 6`, `k : Fin 8`.

- `selected : Fin 3 → Fin 8` is the literal vector `[0,2,6]`; `selected_injective`.
- `index : Fin t × Fin 3 → Fin t × Fin 8`, with `index_injective t`.
- `deletion t : Finset (Sym2 (Vertex t))` is the image of all selected indices under the actual inherited edge index. It selects precisely ab,ad,xy in each block.
- `deletion_subset t : deletion t ⊆ (graph t).edgeFinset`.
- `deletion_card t : (deletion t).card = 3*t`.
- `edge_mem_deletion i k : edge (i,k) ∈ deletion t ↔ k=0 ∨ k=2 ∨ k=6`.
- `keptNeighbors i v` is the vector of finsets `[{c},{c,d},{a,b,x},{b},{c},{h}]` in that block.
- `private_neighbors i v : (Retained (graph t) (deletion t)).neighborFinset (node i v) = keptNeighbors i v`.
- `private_degree i v : (Retained (graph t) (deletion t)).degree (node i v) = ![1,2,3,1,1,1] v`.
- `hub_neighbors t : (Retained (graph t) (deletion t)).neighborFinset (hub t) = Finset.univ.image (fun i : Fin t => node i 5)`.
- `hub_degree t : (Retained (graph t) (deletion t)).degree (hub t) = t`.
- `retained_edge_classification u v h` for actual retained adjacency gives `∃ i k, (k=1 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=7) ∧ ((u=(ends i k).1 ∧ v=(ends i k).2) ∨ (u=(ends i k).2 ∧ v=(ends i k).1))`. Thus every retained edge is ac,bc,bd,cx,yh in either orientation.
- **`witness_valid (t : ℕ) (ht : 2 ≤ t) : Valid (graph t) (deletion t)`**.
- **`minimum_upper (t : ℕ) (ht : 2 ≤ t) : minimum (graph t) ≤ 3*t`**.

These use actual retained graph degrees. No lower-bound premise occurs. Private neighbor/degree formulas, hub formulas, deletion subset/cardinality hold for all t, including zero. Only validity and the minimum bound require t≥2. No t=1 optimum is asserted.

## Provenance and residuals

Starting component SHA256 `74e2c9ead42007930c623531d4ee290865cf41d245f520ca7bff8270a9fd2f74` was verified. Every inherited manifest entry was verified, and all five inherited mathematical sources (`Source`, `Boundary`, `Gadget`, `Edges`, `Degrees`) remain byte-identical; see `inherited-identity.json` and `inputs/frozen-component-manifest.json`. Read source-lane SUMMARY, actual five modules, pins, guard/replay and audit source; ordinary discovery PROOF and root ADOPTION, ancestor/campaign instructions and campaign context. Frozen inputs retain these source/adoption/context records. Publisher wording and source/novelty assessment are inputs; no fresh source or novelty assessment was attempted.

Residuals outside this assignment: arbitrary-deletion lower bound, exact minimum, transport to Fin n, source refutation, paper, independent final review, root replay and acceptance. None is claimed here. No conditional exact-minimum stand-in was added.

## Verification and replay

Eight mathematical modules compile serially with pinned Lean4.34.1, `-j1 -M2700 -DwarningAsError=true -DautoImplicit=false`. Pins preserve all9 packages including mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and the Lean binary hash. Replay checks package revisions through local metadata (no git command), binary hash, complete imported package olean hash inventory, entry hashes and forbidden proof constructs.

`OriginAudit` exhaustively enumerates117 actual module-origin declarations (89 inherited,28 new), including generated/private names, crosschecks `env.constants/getModuleIdxFor?` against `moduleData.constNames`, and records full actual types, transitive axioms and safety flags. `AuditPrint` separately executes literal `#check`/`#print axioms` for every actual kernel name. Axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`; unsafe/partial/axiom flags all false. `audit-inventory.json` and audit logs supply the exact complete declaration list. The audit-print linter exception is inherited `linter.auxLemma false` for deliberate generated-name references. No successful mathematical source has sorry/admit/axiom/unsafe/native_decide or an unproved premise.

`upper-witness-component.zip` is deterministic, source-only, with fixed timestamps/modes and no own oleans/ileans/IR/object files. `manifest.json` binds entries; `archive-sha256.txt` binds the archive. Fresh extraction into `verification-fresh/` rebuilds every module and both audits. `verification-fresh/replay-receipt.json` records the result, complete types and axioms, sampled resource receipts and zero initial own compiled artifacts. This is upper-witness PASS only, not source-refutation PASS.

Reproduce into a nonexistent destination within this lane:

`python3 replay_guard.py python3 replay.py upper-witness-component.zip /absolute/path/to/new-destination`

## Resources, failures and protocol deviations

Lean compiles use process-group RSS2800MiB, CPU210s/wall230s, nominal45ms sampling, memory option2700MiB and approved AS∞ only for Lean. Python helpers use AS512MiB, CPU210s/wall230s and BLAS1. The copied helper supervisor uses groupRSS512MiB and nominal40ms cadence with scan-time compensation. No cap was raised and no resource guard kill occurred. Receipts report sampled peaks; unsampled transients/scheduling delay cannot be excluded.

Protocol deviation: early development invoked the copied `guard.py` directly. It enforced its own Python AS/CPU limit and the full Lean group caps, but did not independently supervise the Python launcher's own group RSS/wall time. Later helper runs, final audit runs and the complete fresh replay use `replay_guard.py` for that separate supervision. This limitation is retained explicitly, not retrospectively advertised as full development-protocol compliance.

`probes/attempt0` through `attempt10` retain failed sources/logs/receipts: premature dependent builds with missing own modules; function-composition syntactic matching; finite-filter simplification and reversed Sym2 orientation; dependent Fintype transparency while reducing endpoints; and strict unused-simp/tactic linter failures. No failure was treated as a proof. Final proofs resolve dependent instance matching with `backward.isDefEq.respectTransparency false` and explicit definitionally equal endpoint changes; kernel checking and audits remain enabled.
