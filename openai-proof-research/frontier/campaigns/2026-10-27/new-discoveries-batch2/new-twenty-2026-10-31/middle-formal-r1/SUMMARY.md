MathDB 355217 — implementation handoff, not acceptance.

The connected 8-vertex graph G8 with edges 01, 06, 16, 23, 27, 37, 46, 47, 56, 57, 67 is formally proved connected and has outer-connected domination number exactly 4, as does its literal middle graph on Fin 8 ⊕ G8.edgeSet. Separate endpoints cover the empty-complement-allowed and nonempty-complement-required conventions.

MiddleFinal.lean contains:
- g8_value and g8_value': attained IsLeast minima, value 4.
- middle_g8_value and middle_g8_value': attained IsLeast minima, value 4.
- mathdb_355217_connected and mathdb_355217_connected': separate connected universal refutations.
- edgeless_two_literal_failure: explicitly uncredited domain control. Under convention B no minimum exists there; the totalized sInf is 0, as documented separately.

The G8 lower bound uses 93 explicit individual certificates plus a cheap exhaustive subset-coverage lemma. The middle lower bound is a generic counting proof. Both upper bounds use parent-map connectivity certificates. No native decision oracle, extra axiom, or unproved bridge is used.

Validation artifacts:
- middle-source.zip, containing source files and replay scripts only, with safe relative member paths.
- fresh-extraction/, created empty before extraction, with byte-identical sources.
- Strict serial rebuild and explicit-module leanchecker for MiddleBase, MiddleSmall, MiddleWitness, MiddleFinal, MiddleAudit.
- Full audit of 252,066 declarations in the import closure; inventory equals audited set. All 207 LOCAL declarations pass metadata and transitive-axiom restrictions. Upstream metadata is reported separately in results.json. Full per-declaration records are in fresh-extraction/audit.jsonl.
- Negative controls reject value 3, vertex–vertex middle adjacency, and a disconnected induced witness by actual false propositions.
- Independent python3 -I enumeration: both conventions give (G8, M(G8)) = (4,4), with 8 and 2 minimizing sets respectively. The middle graph has 19 vertices and 48 edges.

Resource discipline: each Lean, leanchecker and Python invocation used the lane-local capped runner, two CPUs, CPU 120 s, wall 140 s, -M3500 on Lean, MALLOC_ARENA_MAX=2, and a 6 GiB RSS watchdog. Initial import Mathlib exceeded the RSS cap and was killed; narrowed imports resolved this. A first replay identified a leanchecker PATH issue; the launcher was corrected. Failed attempts and all logs are retained. Final proof builds stayed below 2.3 GiB process-group RSS. Nothing was written outside the lane; no git, network, browser, child agents, ledger changes, or external messages were used.

Read PROOF.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md and results.json. This lane does not revise prior-art or significance rulings and does not self-accept. Credit remains zero; root decides.
