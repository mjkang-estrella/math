# Conditional formalization: MathDB 337062

Endpoint: `EBC337062.conjecture21_false`.

Statement: `DistanceAndCounts → PathSplitting32 → ¬ Conjecture21`.

Status: CONDITIONAL on exactly `EBC337062.DistanceAndCounts` and
`EBC337062.PathSplitting32`. These two Props are ordinary theorem arguments,
not postulates. The general BFS correctness and path-splitting proofs remain
unfinished. No acceptance or credit is claimed.

There are 15 Lean modules, listed in module-order.txt. The literal definitions,
shortest-path/walk bridge, all seven class formulas, exact finite rational
arithmetic, sum reindexing, conditional endpoint, local BFS certificate and
C_2 uniformity control are closed without placeholders.

The counterexample's arithmetic totals are 15169/615 and 15172/615. Their
interpretation as the literal graph's edge betweenness is conditional on the
two bridges. The endpoint is the negation of the source's complete conjunction
for all seven classes and n ≥ 1, instantiated at Class 4, n = 1.

Replay and audits: consult results.json and replay-final/logs for the final
fresh source-archive extraction. The driver strictly compiles each module
with warningAsError and separately invokes leanchecker with that explicit
module. The source scanner and local-declaration audit cover all local code,
including private generated declarations. The endpoint's only axioms are
propext, Classical.choice and Quot.sound. Development failures and earlier
extraction logs are preserved; they are not the final replay result.

Files: source-only.zip; src/*.lean; module-order.txt; PROOF.md;
STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; scripts/replay.sh; scripts/cap.pl;
logs/source-scan.json; results.json; replay-final/logs/*.

All writes and extraction/build/cache/temp directories stayed in this lane.
No other-lane script was executed. No git, network, browser, child agent,
upload, external message or shared-ledger edit was used. Resource limits were
unchanged after failures. No kernel walk enumeration was used.

Next implementation work: prove a general connected-graph path-splitting
bijection, prove the general BFS recursion correct for literal paths, and
apply them to discharge the two named Props. Reuse the checked arithmetic and
transport lemmas; no numerical recomputation premise is needed. The separate
2022 prior-art gap remains for root; this lane does not adjudicate it.
