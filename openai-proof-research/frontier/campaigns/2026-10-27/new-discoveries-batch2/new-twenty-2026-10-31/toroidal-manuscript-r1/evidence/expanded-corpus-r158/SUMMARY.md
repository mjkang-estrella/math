# Expanded corpus r158

One full Lean counterexample candidate is ready for root review: **369421**, the toroidal-grid representation-number conjecture. A 45-letter 3-uniform word represents **C3 square C5**, contradicting the conjectured lower bound 4 at m+n=8. Two different ordinary checkers and the literal Lean endpoint verify it.

Read **CANDIDATE-369421.md** first. The three-module packet is **lean-packet.tar.gz**; hashes are in **outputs/lean-sha256.txt**. The clean extracted replay is **extracted-replay/**. All three strict builds and explicit-module leanchecker runs passed. The audit covers all 23 local declarations, including generated declarations; only propext, Classical.choice and Quot.sound occur.

**No result is self-accepted; no campaign count was changed.** The main qualification is publication retention: the author and institutional accepted-paper records link to the current arXiv text retaining the exact conjecture, but the embargoed accepted-author manuscript was not read. Registry/prior-art searches are bounded screens, not global novelty guarantees.

Exactly 20 reserved ID-keyed dispositions are in **results.json**, with literal records, one-based chunk lines, chunk/raw-line/statement hashes, source receipts, actual depth, attempts and gaps. Raw bytes including newline are preserved in sources/ID.raw.jsonl. All 20 current arXiv abstract and HTML routes succeeded.

Other sustained routes:
* **369628:** exhaustive Hamiltonian-backbone cubic completions at orders 12,14,16: 9906,153839,2682919 completions. Biconnected maximum path counts 28,46,82 satisfy the conjecture. Order 18 was capped; no completed coverage claimed.
* **362965:** exhaustive (t,lambda)=(3,2) liking-digraph row searches at orders 5,6,7, using source necessary degree/intersection bounds. Only the complete order-5 example; none at 6 or 7.

Additional exact searches: all connected labeled graphs through order 5 for product-antimagic labelings and (2,2)-colorings; all loopless labeled digraphs through order 4 for majority 3-colouring; all H2 graphs through order 6 for 3-colourability; all six isomorphism types of simple 6-regular graphs through order 9 for a Hamiltonian factor; all Q3 edge subgraphs under coordinate colouring for the average-degree rainbow-path bound. The hypercube sweep tests one colouring and lies below the source unknown d>=5 regime. Full outputs are retained.

**361904** is refuted by its own source six-point example and blow-up. **368226** is refuted by its own current Proposition 2.22; MathDB also confuses d=3 and general d. **361551** is a classical matching-polytope averaging consequence, identified as a theorem in the 2026 journal counterpart. None is new.

**370342** has only a small-order omission: K4 has four cycle systems versus three for the four-vertex book. The source cone examples already give this, so it is not a candidate. Book counts at n=3,4,5,6 are 1,3,16,125, matching the printed formula. Other unresolved cases are parked, not declared resolved.

The requested several-hour broad pass was not completed: effort was redirected to finishing the discovered exact endpoint and its source/prior-art gates. Unsearched routes and limited-depth reviews are explicit in results.json. Uniformly deep review of all 20 papers is not claimed.

Everything written stayed in r158. No git, ledger edits, publishing, uploads, tabs, external messages, author contacts, installations or child agents. TLS verification remained enabled. No denied route was retried; a short-cycle-cover PDF route returned 404 and was recorded. All Python, Lean and solver calls used the lane-local RSS watchdog, two CPUs, CPU 120 s, wall 140 s, RSS 6 GiB and MALLOC_ARENA_MAX=2; Lean used -M3500. Caches/build/tmp directories were lane-local.

Initial failed diagnostics are retained: a cycle-script syntax error, missing g++, Lean instance/import fixes and a leanchecker PATH failure. The corrected extracted packet passes. No background work is left at handback.
