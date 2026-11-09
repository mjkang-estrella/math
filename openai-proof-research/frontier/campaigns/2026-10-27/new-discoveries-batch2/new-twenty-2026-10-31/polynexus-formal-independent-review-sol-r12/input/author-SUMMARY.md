# Implementation handoff — MathDB 352496

The full literal integer endpoint is proved in src/PolynexusLiteral.lean (`polynexus_literal`), together with the exact signed-source operand-set equivalence `PNZ_source`, printed min/max legality equivalence, rational formula and n=1 theorem. The first production edit repaired the latest Partition compile failure and passed strict checking before any API lookup.

The implementation adds actual zero-pair gap bijections, disjoint length fibers, and a finite triangular-gap convolution. It evaluates that convolution by two induction/telescoping polynomial identities, replacing the optional formal-series/three-shift-binomial route. No answer-defined proxy, numerical experiment, external mathematics program or enumeration was used.

All 12 production modules compile fresh, all 12 kernel checker invocations pass. Setup was recorded with an empty build before compiling, and clean LEAN_PATH contains only own fresh build plus upstream libraries. No foreign project olean paths survive in clean receipts. Production sources equal the extracted sources exactly; final-source-freeze.json binds the review inputs.

Deep audit: 282 module-origin-selected production declarations (including generated/private names), 7,003 transitive declarations, actual types and opaque bodies. All safety/origin/axiom checks pass, only propext/Classical.choice/Quot.sound. Sixteen disjoint hash partitions provide unabridged types/bodies of the entire closure, checked for exhaustive coverage and zero abbreviation markers. The initially abbreviated audit and a CPU-limited raw-node serialization attempt are preserved as nonfinal evidence. Resource caps/runner were not modified. The raw-node attempt exited -9 at the 120 CPU cap; the final diagnostic-driven fix partitions body output, with every shard still checking the whole dependency closure.

Both meaningful negative controls failed as intended: changing the cubic endpoint sign gives a type mismatch; the old rectangle-style off-diagonal entry assertion reduces to False. Failure logs/receipts are preserved.

Manifest includes all own sources, extracted sources/oleans, frozen inputs, outputs, completed receipt JSONs and logs. Named terminal self-exclusions prevent circular hashing. Frozen-after verifies all 71 paths unchanged.

Independent source-aware formal review and manuscript review remain separate; novelty/significance and root acceptance are not claimed. Credit zero; accepted count 52/60 unchanged. No children, network, git, account, publication, foreign-lane bodies or dependency writes.

Startup reporting: the supplied directory has TASK.txt, not FULLTASK.txt. Bootstrap printed/read the complete TASK and AGENTS chain. Two initial guessed runner filenames did not exist; an own-directory inventory located runner.py. Those failed invocations executed no reader/writer. The runner implementation and runner-captured logs were read directly to establish/use the logging interface; substantive input/source/API/build/audit/bookkeeping operations used the provided runner and write_lane.py. No retrospective success receipt is invented for the initial failed commands.

See results/keyed-results.json, results/deep-audit.json, results/full-manifest.json, manuscript/polynexus-proof.md and cleanroom/setup.json for concrete evidence.
