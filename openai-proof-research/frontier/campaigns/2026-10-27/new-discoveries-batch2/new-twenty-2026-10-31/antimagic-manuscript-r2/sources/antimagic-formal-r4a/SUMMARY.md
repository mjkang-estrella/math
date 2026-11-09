# Round 4A construction handoff

PARTIAL, NOT ACCEPTED. No credit claimed; root decides.

DepthTwoConstruction is discharged, symbolically for every even t >= 4. Together with the immutable round-2 star and binary depth-two results, all depth-one and depth-two construction cases are now complete. The frozen round-3 packet has SHA256 9dc97086dd29e29d7d84932df93256c01c4531b9813e0be7f16af8410d589e6c. All 20 inherited modules are byte-identical, with before/after manifests.

Antimagic4AHigh proves the entire ordinary tuple partition into the high interval, direct agreement with the inherited formula, and unique occurrence of every high label. Antimagic4ABijection combines this with the low partition, transfers it onto actual Nonroot vertices, and constructs depthTwoLabeling as a literal edge equivalence. Antimagic4ADepthTwo proves properness, the exact colour count, formula fidelity on each child edge, and depthTwoConstruction : Round3.DepthTwoConstruction. There is no supplied edge-equivalence assumption in that endpoint.

Higher-depth progress: Antimagic4ALeafBlocks proves sigma injectivity and bounds, the leaf-block bijection for arbitrary tuple size and even block length, direct largeLabel agreement under explicit tuple-parameter and parity identities, and the exact displacement sum identity. Antimagic4AShell proves the centered interval partition with its center omitted, an explicit unique inverse, direct internalLabel agreement (including patchedIndex), and constant sums for even shell segments. These are ingredients, not proofs of either higher-depth construction Prop.

AntimagicFinal4A.even_case assumes exactly NonbinaryHigherConstruction and BinaryHigherConstruction. mathdb_354228 additionally assumes ModelBridge, reserved for the sibling lane. ModelBridge has not been worked on. All endpoint axiom sets are printed.

Validation: the source-only archive is freshly extracted in replay-fresh; scripts/replay4a.sh performs a strict serial rebuild and explicit leanchecker checks on all 27 modules, the full declaration audit, inherited hashes, and 42 Python regression cases plus negative controls. The audit covers 10,934 declarations: 749 local and 10,185 upstream. Local executable metadata flags are all absent. Upstream metadata is reported separately. Only propext, Classical.choice and Quot.sound occur as axioms. See results.json, REPRODUCE.md and replay-fresh/logs.

Still open: the complete internal shell assignment to row intervals, shell/leaf parameter bijections on actual vertices, global range bounds and properness for every even t >= 4 and n >= 3; then the t = 2 higher-depth patch. The generic shell and leaf results do not remove those obligations. This is not acceptance or a full resolution.
