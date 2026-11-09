# Partial implementation — MathDB 372205

**The full assignment is not completed. Zero qualifying credit; no self-acceptance.** The universal corrected existence theorem is absent. The exact remaining gaps are in GAPS.md.

The Lean sources prove the literal printed-statement negation for all natural powers, the positive-integer MathDB reading, and the n ≥ 4 reading. Each uses power 4, forbidden closed degree 12, a proved complement identity, and a general cubic zero-label obstruction. Literal graph definitions require simplicity, connectivity, regularity, a bijection into Fin n → ZMod 2, and zero neighborhood sums. Order 2^n is proved from the bijection.

The sources also prove the corrected theorem completely at powers 4 and 5: all 8 corrected graphs of order 16 and all 24 of order 32. Each base module has actual adjacency masks, kernel-decide symmetry / looplessness / degree / bit-label bijectivity / zero sums, and a parent certificate interpreted by a proved connectivity theorem. These are finite base cases only, not the all-power theorem.

Missing: formal F4 affine lifts, rank existence of translations, holonomy connectivity, matching decompositions / cycle persistence, degree interpolation, and the induction / top-degree complement bridges. No conditional theorem or axiom disguises these gaps.

Delivery includes formal/, results.json, a source-only xor-magic-partial-source.zip, its portable replay.py and REPRODUCE.md, input hash receipts, full logs, a statement-correspondence table and targeted negative controls. Final validation passed: 36 strict fresh builds, leanchecker on all 36 modules, an audit of all 576 declarations in 35 proof modules, and all three targeted negative controls. The driver also refuses an existing olean. Full receipts are in fresh-replay/logs/ and receipts/final-validation.json. All 196 input hashes are unchanged. No lane jobs remain. This validates the partial packet only.

No agents, git, shared ledger edits, publication, upload, external messages, browser tabs or network requests were used. Inputs are read-only; final before/after hash comparison is recorded separately. Proof builds and validation use the bounded runner. An exploratory leanchecker --help invocation was not bounded; it was terminated after discovering that the program has no help mode. This exception and the stopped first replay attempt are documented in receipts/tool-discovery-note.json.
