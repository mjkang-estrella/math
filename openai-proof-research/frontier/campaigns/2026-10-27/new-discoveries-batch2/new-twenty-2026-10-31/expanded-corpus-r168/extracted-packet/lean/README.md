# SplitMatching381751

Lean 4.34.1, using the read-only campaign mathlib cache pinned at d13f23b723b8a846827a245b89c10fc7d3f11612. Dependencies are inherited through the 2026-10-14/formal lake manifest. No full upstream rebuild is claimed.

Main file: SplitMatching.lean. Endpoint: SplitMatching381751.literal_counterexample. The graph is not bipartite; only the non-K4-component three-colour exception conjecture is refuted. All arbitrary matchings are represented by edge selections, with literal incidence degrees and count-cardinality bridge lemmas. Nothing is inferred from a bounded diagnostic.

Build using the lane resource wrapper and scripts/lean.sh, producing an explicit .olean in a fresh lane-local directory. Set PACKET_MODULE_DIR to that directory when compiling Audit.lean and calling scripts/checker.sh. The latter invokes leanchecker with explicit module SplitMatching. All calls use two CPUs, -j1 and -M3500. Logs replay2/audit3/leanchecker and extracted-* record the checks. The module-origin audit covers all generated declarations as well as named ones.

The final source contains no sorry, admit, new axioms, unsafe, native_decide or ofReduceBool. Kernel decide is used only for finite literal graph checks. The impossibility is proved arithmetically with omega and semantic bridges.

This is a research candidate with zero accepted discovery credit. See CANDIDATE.md for source, ordinary proof, prior-art limitations and substantial credit risk.
