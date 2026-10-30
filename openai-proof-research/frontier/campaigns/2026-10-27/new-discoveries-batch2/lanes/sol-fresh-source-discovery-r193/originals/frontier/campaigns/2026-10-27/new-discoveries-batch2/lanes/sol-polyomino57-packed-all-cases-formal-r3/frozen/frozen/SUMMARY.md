# Partial formal closure: 37/70; unconditional endpoint NOT closed

Credit 0; additional count 5, total count 35. Root owns acceptance. No manuscript, novelty or new-family claim. SOLO; no children, enumeration-lane inspection, network, browser, git, or external action.

The immutable geometry archive SHA256 was verified exactly against dac195edc48dea0c812d265a50a71f42bfc6d5d2f8a844233935db41d020d130. Both frozen source archives, interfaces, adoption receipts, all 31 compressed tables and compression verifier/metadata are copied byte-identically under inputs. Consumed common mathematical sources are identical between frozen archives. Audit filename collision and the one immediately corrected misplaced initial log are documented in provenance.json.

The task is INCOMPLETE. All 35 empty-group cases, forced case (7,3,0), and COMPLETE potential case (10,10,1) are kernel proved. Exact formal residual has 33 cases, established by finite-set identities, not expected rowcounts. See INTERFACE.md for the complete semantic pipeline and exact remaining premise.

## Measured bottleneck and adaptation

Every Lean invocation uses pinned Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, -j1, warningAsError, autoImplicit false. Monitor samples group RSS every 45ms, kills at 2800MiB, wall 230s and inherited CPU cap 210s. Python generation has 512MiB address-space limits and CPU/wall limits. No caps were raised.

Small exceptional case: geometry/domain/group checks 4.16s; base 1.94s; merge 3.30s. A single all-vertices edge check was killed after 12.46s at 2941300736 RSS bytes. Splitting by distinguished root into 60 ordinary decide facts succeeded in 35.06s at 1854791680 bytes. All 960 entries participate in actual checks; the domain has no centers and still four boundary groups.

Largest (7,5,0) full-mask representative slices used balanced total table lookups on actual supplied bytes, not an arithmetic-only toy. 16 unordered partitions ×24 roots =384 comparisons passed in 1.68s at 1832361984 RSS bytes. Increasing to 256 partitions (6144 comparisons) hit RSS cap after 13.57s (2941628416 bytes); 1024 partitions (24576 comparisons) hit cap after 25.52s (2956697600 bytes). An adapted 256-partition module with one proof per partition still hit cap after 22.41s (2936713216 bytes): merely dividing theorem statements within the same data module did not solve this memory bottleneck. Full input sources, failure logs and process receipts are preserved, not discarded.

These observations block this direct balanced-lookup/powerset kernel-checking implementation at large table scale. They are NOT an impossibility result for more efficient reflection, bit packing, independent small-data shards, or alternative potentials. At the successful small-shard rate, naively repeating 384-comparison modules for all 184239622 merge comparisons would require about 479791 modules and about 224 hours (including module startup); this is a scale diagnostic, NOT a promised runtime or lower bound. Larger shared-data modules failed the fixed memory cap. No unjustified all70 runtime promise is made. The generic theorem avoids a mask-to-finite-set soundness gap by directly quantifying finite label subsets; a future efficient bitmask checker still needs its verified semantic bridge. No full largest certificate or optimistic runtime claim is hidden behind this partial result.

## Delivery and validation

Deterministic source-only ZIP includes all consumed sources, pins, generators, frozen inputs, measured failures and a fresh-extraction replay script. Replay builds every consumed candidate dependency from source in a new directory, audits every declaration from every consumed candidate origin (actual types, axioms, safety and partial flags), then runs #check and #print axioms for all audited declarations. Only propext, Classical.choice and Quot.sound are permitted. Exactly the documented inherited Polyomino57.attachCheck._unsafe_rec partial=true/unsafe=false helper is excepted; no new helper flag exception. No evaluation axiom or native_decide.

Replay initially failed because a hard Python AS cap was inherited by Lean before its distinct RSS-controlled launch. The corrected launcher starts a launch-only shell broker before capping Python at 512MiB; every Lean child still runs through the unchanged monitored run.py with its own specified caps. The original failed log is retained. A separate replay harness defect in printing private numeric name components was fixed using Lean mkIdent (as in the frozen geometry replay); its failed command logs are preserved too. No Lean cap was raised.

The final receipt beside the archive records fresh extracted replay status and actual declarations/resources. Frozen mathlib/package oleans are the pinned dependency environment; no candidate olean is packaged or reused by the fresh replay. Failed larger experiments remain experiments and are excluded from the consumed endpoint dependency list.
