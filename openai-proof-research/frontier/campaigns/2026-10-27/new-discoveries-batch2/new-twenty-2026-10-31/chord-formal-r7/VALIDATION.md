# Round 7 validation receipt

153 modules passed a fresh extracted strict serial build and an explicit-module leanchecker run. All 148 frozen Lean sources match their before and after hashes.

The complete endpoint import closure contains 282462 declarations, including 7024 LOCAL declarations. Audited and inventory sets are equal. Root and fresh audit streams are byte-identical. All forbidden LOCAL metadata and unapproved LOCAL transitive axiom totals are zero. See results.json for separate upstream runtime metadata totals.

Peak sampled RSS across validation and development logs: 3511772 KiB, below 6291456 KiB. All process caps remained enabled. Five negative controls failed as expected in both root and fresh runs. The independent regression checks 87296 assignment extensions, including the rank-table equations, with zero violations; these are numerical checks only.

The intended endpoint still assumes BandErasure, EndEdgeSurgery and TriangleRigiditySix. The n=4 and literal-small-size endpoints are unconditional. Their printed axiom lists contain only propext, Classical.choice and Quot.sound. Successful replay is not acceptance; root decides.
