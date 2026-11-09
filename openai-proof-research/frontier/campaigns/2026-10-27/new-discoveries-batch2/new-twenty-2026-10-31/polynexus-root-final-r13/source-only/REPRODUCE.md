# Polynexus source-only certificate

MathDB352496, explicitly source-bound: actual contiguous-one-block diagonal matrices; ordered NONZERO operand pairs with ordinary NONZERO product, not the entire rook monoid and not distinct product outputs. Positive n is the source domain; n1 and the canonical n0 extension are separately controlled.

Pins: Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52; mathlibd13f23b723b8a846827a245b89c10fc7d3f11612. env.sh records the exact host dependency installation paths. Pinned prebuilt upstream is trusted, not distributed/rebuilt here.

Extract to an EMPTY directory, verify SOURCE-HASHES.json, and run in dependency order:

    bash check.sh PolynexusDiag
    bash check.sh PolynexusSrc
    bash check.sh PolynexusProd
    bash check.sh PolynexusClose
    bash check.sh PolynexusSrcPrd
    bash check.sh PolynexusPairs
    bash check.sh PolynexusCount
    bash check.sh PolynexusPartition
    bash check.sh PolynexusGap
    bash check.sh PolynexusGapCount
    bash check.sh PolynexusEval
    bash check.sh PolynexusLiteral

Then run each module through bash checker.sh MODULE in the same order. The provided wrappers enforce -j1 -M3500 -DwarningAsError=true and the supplied capped runner. Receipts/logs are generated at true exits. No oleans or foreign project build directories are included. Audit sources included here are review tooling, not production imports; the complete independent audit evidence is hash-bound in the root acceptance/review record.

Independent fresh compilation and module checks have already passed; this source-only packaging operation did not execute Lean at root. See independent-FINAL-REVIEW and setup evidence for precise execution, original failure history, all282 production/all7003 dependency audit, and source-map qualifications. No worldwide priority or publication claim. The editable reviewed proof is under manuscript/; the PDF is delivered separately.
