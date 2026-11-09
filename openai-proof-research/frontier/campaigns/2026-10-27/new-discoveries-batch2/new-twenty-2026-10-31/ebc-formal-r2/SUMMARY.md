# MathDB 337062: round 2 implementation

Endpoint: `EBC337062.conjecture21_false_unconditional : ¬ EBC337062.Conjecture21`.
Status: unconditional. Neither DistanceAndCounts nor PathSplitting32 remains an argument.
No acceptance, novelty clearance, or campaign credit is claimed; root decides.

The 20 modules preserve every round-1 definition byte for byte. The round-1
sources are unchanged except Audit.lean, whose imports and printed endpoints
are extended. Five new modules prove the general BFS correctness and recursion,
certify all G32 table entries, prove general shortest-path edge splitting, and
apply these to close both original bridge propositions.

The endpoint uses the literal circulant C_32(1,7,9), literal shortest paths,
and literal edge betweenness. Its two edge values are 15169/615 and 15172/615.
The unconditional C_2 uniformity and edge-transitivity controls are retained.
The optional C_21(1,6) control was not added.

See results.json for authoritative extracted replay, metadata/source audit,
archive hash, and definition-preservation results. All 20 modules must have
both a strict compilation PASS and an explicit-module leanchecker PASS.
The final audit prints the endpoint axioms and rejects local postulates,
unsafe/partial/extern/implemented-by declarations and generated unsafe helpers.
The allowed endpoint axioms are propext, Classical.choice, and Quot.sound.

Files: source-only.zip; src/*.lean; module-order.txt; scripts/replay.sh;
PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; results.json;
logs/source-scan.json; replay-final/logs/*. Development logs are separate.
All writes, builds, caches, and temporary paths are lane-local. No git, network,
child agents, browser, upload, external message, or shared-ledger write was used.
The separate 2022 prior-art review remains outside this implementation lane.
