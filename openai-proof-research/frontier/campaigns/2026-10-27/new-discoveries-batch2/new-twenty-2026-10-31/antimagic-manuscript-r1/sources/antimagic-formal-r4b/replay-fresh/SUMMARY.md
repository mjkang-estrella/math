# Round 4B handoff: MathDB 354228

BRIDGE PROVED, NOT ACCEPTED. Root decides acceptance. No mathematical credit claimed.

`Antimagic.Round4B.modelBridge : Antimagic.ModelBridge` is proved unconditionally in `AntimagicFinal4B.lean`, with the exact frozen definition. Every finite FullTree certificate with t >= 2 and n >= 1 yields a SimpleGraph isomorphism to the literal row-index model `tree t n`. No inherited declaration is edited or shadowed.

The stronger helper `Antimagic.Round4B.fullTreeIso` constructs an isomorphism between any two FullTree certificates with the same t and n. `Antimagic4BBridge.lean` proves the compatible layer equivalences, bijection on all vertices, and preservation and reflection of the child relation. `AntimagicFinal4B.lean` specializes to the verified model structure and proves `mathdb_354228` conditional ONLY on Round3.DepthTwoConstruction, Round3.NonbinaryHigherConstruction and Round3.BinaryHigherConstruction. Those three Props belong to sibling Round 4A and remain assumptions.

All 20 inherited modules are byte-identical to the frozen round-3 archive, verified against SHA256 9dc97086dd29e29d7d84932df93256c01c4531b9813e0be7f16af8410d589e6c. Before and after manifests cover exactly those 20 files. Three new modules make 23 total.

Strict serial compilation and explicit-module leanchecker checks pass. The complete import-closure audit contains 10,705 declarations: 531 local and 10,174 upstream. Local unsafe, partial, implemented_by, extern and _unsafe_rec counts are all zero. Only propext, Classical.choice and Quot.sound occur as axioms. Upstream executable metadata is reported separately in results.json. Endpoint #print axioms output shows exactly the permitted three axioms.

A fresh source-only extraction is rebuilt in replay-fresh, using the lane-local capped serial driver. The inherited six literal graph regressions and 42 Python parameter cases, including negative controls, are replayed. See REPRODUCE.md for fresh and resumable commands, logs and resource limits.

Remaining work for root: integrate the sibling construction results if and when independently verified; instantiate the three construction assumptions; independently review statement fidelity and the fresh replay. There is no remaining isomorphism-bridge obligation in this lane.
