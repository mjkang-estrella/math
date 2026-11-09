# Final validation receipt

The source archive SHA-256 is 03971d4610581095feddea8040bd178f017d459794ac3e2374e73402d93ccbab. Its final source was extracted into the new, empty fresh-extraction directory, then all 33 modules in modules.txt were rebuilt serially and checked individually with leanchecker. All 33 source hashes match their successful replay markers.

The final endpoint import-closure audit reports inventory = audited = 213,179, with exact set equality. It audited 306 LOCAL declarations, including generated declarations and opaque proof values. LOCAL unsafe, partial, axiom, _unsafe_rec, implemented_by, extern and unapproved transitive axiom counts are all zero. The endpoint #print axioms reports contain only propext, Classical.choice and Quot.sound.

The other 212,873 declarations are upstream. Their implementation metadata is reported separately in results.json and fresh-extraction/audit.jsonl: 630 unsafe flags, 2,627 partial flags, 15 axiom declarations, 2,595 _unsafe_rec names, 300 implemented_by entries and 761 extern entries. There are 197 upstream declaration/axiom-name incidences outside the allowed proof-axiom list, primarily in imported Lean implementation code. No LOCAL declaration transitively uses an unapproved axiom. This is not a claim that every imported compiler/runtime implementation declaration is a pure mathematical theorem.

Final audit log: fresh-extraction/logs/1793738118096281862.log.
Audit module checker log: fresh-extraction/logs/1793738152894996117.log.
All prior failed attempts remain in logs/, diagnostic-replay/logs/ and packaging-attempt-1/logs/; they are not passed certificates. In particular the initial generated trace._unsafe_rec companion was detected and removed before the final archive and final fresh replay.

The independent regression checked 995,572 matching/assignment pairs through n = 5. All boundary-model comparisons, parity/nonnegativity checks and four numerical negative controls passed. Formal negative controls also reject a wrong Euler offset, omitted empty-circle contribution, and an isolated-pair replacement for the triangle.

No child agents, git operations, network requests, external messages, publication or upload were used. No heavy process or watchdog remains from this lane at handback. The intended conjecture and n = 4 completeness endpoint remain CONDITIONAL. Root decides acceptance; credit remains zero.
