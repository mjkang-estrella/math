# MathDB 334599: DRAFT manuscript and reproducible dossier

Six-page manuscript: output/pdf/supervenience-draft.pdf; source: paper.md and build_paper.py.
Ordinary proof: PROOF.md. Literal certificate: proof/Hierarchy.lean (byte-identical to the frozen author module).
Reproduction instructions: REPRODUCE.md. Portable drivers: tools/replay.py and tools/extract.py.

The proof defines the guard D(A; A and B), applies the known four Boolean cells, and proves recursive translation from L2 to L1 on arbitrary ternary frames. It refutes arXiv Conjecture 15 at n = 1, defines Section 7.3 relativized agreement, and identifies the unnecessary single-formula compression premise in Humberstone 2019, pp. 16-17. Known cell techniques are credited; journal text unread and bounded prior-art coverage are explicit. No priority claim.

Fresh safe extraction of source-only-proof.zip into fresh-replay-final passed strict -j1 -DwarningAsError=true compilation of all three modules and leanchecker on each. Module-origin audit checks all 101 original declarations, full types, bodies and safety; only propext, Classical.choice, Quot.sound appear. Receipts: fresh-replay-final/replay-receipts/replay.json and adjacent logs. Deliberately false proof and sorry are rejected; injected local axiom is detected by the audit.

Finite diagnostics were independently rerun: 263185 one-step cases, 98304 nested pointed comparisons, and five negative-control witnesses. These are diagnostics only. Every final PDF page was rendered and visually inspected; qa/receipt.json binds all six images and the PDF.

All 429 frozen input files hash identically before and after; only target-relevant r84 evidence is included. Source-only and full-dossier ZIPs have manifests and external archive hashes. Upstream pinned caches and the Lean distribution remain trusted and unmodified. Each substantive command used the retained limiter; systemd MemoryMax=6G was available. Early font and PATH failures are retained, with successful final replacements. No jobs from this lane remain.

DRAFT. Zero accepted credit. Count stays 12/20 beyond 39. Root alone accepts. No child agents, git, browser, external messages, upload, publication, shared-ledger edits or other-lane writes.
