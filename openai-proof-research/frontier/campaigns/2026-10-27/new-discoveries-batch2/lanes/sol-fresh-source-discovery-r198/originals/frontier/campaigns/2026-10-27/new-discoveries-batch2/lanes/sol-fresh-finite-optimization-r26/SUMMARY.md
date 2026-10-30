# Exact finite candidate; ordinary-proof gap retained

Target: Peter Exley's OEIS A395495 conjecture a(n)=(n²-n+6)/2 for all n>=4, where a(n) minimizes the size of a connected polyomino containing EVERY fixed n-omino by translation only.

Candidate literal refutation: n=11; C is the radius5 integer L1 diamond minus(±2,±2). C is connected and has57cells; the conjecture predicts58. Two separately implemented exact enumerators checked every135268 fixed11-ominoes. A third audit checked every saved literal translation witness and exact equality with the complete neighbor-growth family. All PASS under hard512MiB/CPU/wall caps. The57-cell container is also inclusion-minimal: for each deleted cell, a saved connected11-cell obstruction fails to embed in the remaining56cells. This does NOT prove global optimum57.

This is a COMPUTER-ASSISTED exhaustive certificate, not numerical sampling. No complete ordinary geometric proof or Lean theorem was obtained. An ordinary argument covers all bounding boxes with minimum side<=3;110106 cases in the other box types remain covered only by exact computation. PROOF.md intentionally absent.

Novelty/substantive status HOLD. Actual primary registry entry read; linked author solver repository404. Current registry roots checked; current Omega diff screen plus complete inherited trees saved, with fresh-tree completeness gap explicit. Closest2022 MathOverflow lower-bound proof bodies do not imply this exact finite construction. No matching public57-cell construction located; no worldwide priority claim. Main eligibility objection: a finite optimized witness to an extrapolated formula may be deemed routine, and the hard ordinary-proof gate remains open.

Independent source/math/substantive review IS warranted before any formal investment or acceptance. No children, git, shared/ledger edits, external mutation, acceptance or count change. Counts remain5/30 additional,35/60 total.

Read discovery.md, novelty-screen.md and provenance.json. Run bash run-checks.sh. The complete embedding-certificate.jsonl and independent-checks.json/certificate-audit.json contain exact witnesses/results.
