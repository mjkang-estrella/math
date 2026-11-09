# Reproduction and trust boundaries

Run from this dossier directory. This manuscript lane has NOT run Lean, lake or leanchecker. The source-only packet is byte-identical to the assembly, SHA-256 bafc3b63f6baba271680f2eed29334603149cee7c17a714bb7b4b1a04c37d3a1.

Ordinary verification (Python 3 with SymPy; local observed version recorded in results):

    python3 -B scripts/capped.py reverify python3 -B scripts/verify.py

This checks the exact polynomial identities and symbolic residue witnesses, regenerates the table from the colour product and safely extracts the source ZIP into safe-extraction/. No proof tools are invoked. It regenerates artifacts; do so on a review copy if preserving delivery hashes.

PDF regeneration (local ReportLab/Pillow dependencies and fonts are bundled in vendor/ and fonts/):

    python3 -B scripts/capped.py rerender python3 -B scripts/render.py
    python3 -B scripts/capped.py reraster pdftoppm -scale-to 1400 -png paper.pdf qa/page

Inspect every regenerated page; the delivered QA receipt binds the delivered PDF and images only. ReportLab timestamps can change the PDF hash while retaining content. Poppler is a system dependency.

For formal replay instructions ONLY, read evidence/ulas-assembly-r1/REPRODUCE.md and the archived scripts/replay.py and module-order.json. The pinned Lean version is 4.34.1; mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. The source packet does not vendor upstream mathlib. Binary hashes are in toolchain-hashes.json; these programs were read for hashing, never executed here. Root's separate replay-result.json reports PASS for all 43 builds/checkers, declaration audit and 11 controls. The independent fidelity review reran all 43 builds and endpoint checker, but did not independently rerun the full declaration audit or controls. The assembly and root did those checks. No worldwide priority claim follows.

The dossier ZIP contains the files listed in DOSSIER-MANIFEST.json plus the manifest itself. Safe-extraction/ and vendor bytecode caches are omitted as redundant; ulas-source.zip and renderer runtime sources/binaries are included. The packaging process's own completion receipt and delivery hash receipt necessarily sit outside that ZIP snapshot. Archive CRC and every member hash are verified after creation. DELIVERY.json binds both delivered ZIPs. Before/after frozen-input maps and copy provenance are included. No manifest hashes itself.

Only propext, Classical.choice and Quot.sound are permitted proof axioms. Root must read the paper and decide. Zero accepted credit.
