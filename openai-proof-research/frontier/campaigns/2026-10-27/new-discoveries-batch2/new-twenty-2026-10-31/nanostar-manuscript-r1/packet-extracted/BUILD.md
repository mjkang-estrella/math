# Certificate replay

The source-only packet contains the twelve proof modules for R162.not_conjecture349177, all general definitions and the orbit/graph-isomorphism bridge. No external solver result is assumed.

Use a fresh directory containing the packet's contents, make scripts/run, scripts/lean-env, scripts/check-env and tools-bin/lean executable, then run:

    bash scripts/replay.sh

The script creates lean-input.zip from the sanitized source text, extracts it into a fresh empty replay/ directory, and rebuilds Definitions, Arithmetic, Certificate, EdgeRows0 through EdgeRows7, and Endpoint in that order. Every Lean and explicit-module leanchecker call uses scripts/run. Dependencies are read-only pinned prebuilt packages at the absolute path in scripts/lean-env, with Lean 4.34.1. The permitted three axioms and cache trust limitations are in lean-status.json.

The archive expects fresh replay/: it refuses to silently reuse a nonempty replay directory. For an existing lane the checked files and full logs are already retained. Inventory.lean enumerates local declarations, including generated ones; Audit.lean prints transitive axioms for all 335 declarations. The auxiliary-name stability linter is disabled only in the audit file so generated declarations can be named; warning-as-error remains enabled, and proof modules disable no such checks.

The first discovery build's one monolithic all-pairs decidable check exceeded Lean's internal memory limit. The final certificate splits exactly the same finite assertion into 88 row theorems in eight modules. Each tested row module remains comfortably below the RSS limit. Failures are preserved as historical logs, not included as proof dependencies.

Statement-fidelity qualification: nanostar means the contracted-hexagon tree structure depicted by the source's Figure 10 and the cited recursive Figure 12. See NANOSTAR.md for the source bridge and outstanding root review.
