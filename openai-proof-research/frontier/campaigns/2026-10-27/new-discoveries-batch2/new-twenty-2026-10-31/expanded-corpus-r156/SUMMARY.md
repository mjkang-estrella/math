# r156 research handback — 20 reserved IDs

No result is self-accepted. No Lean endpoint was produced. This is a bounded investigative pass, not the requested multi-hour completed qualification of a discovery. The strongest lead remains held on source/prior-art qualification; the remaining entries are known, ineligible, or parked with explicit gaps. Root must decide any further investment or credit. Campaign counts were not changed.

The exact 20 ID-keyed dispositions are in [results.json](results.json). Each includes the literal MathDB statement, its SHA-256, exact raw line/chunk provenance and hashes, current primary-source receipt, review depth, actual computation and remaining gap. All 20 raw lines retain their original newline in raw/. The corpus extraction and chunk hashing completed under the lane resource wrapper. Required AGENTS files, both inherited batch context/ledger files, and the current campaign ledger were read; compact family/ID checks are in outputs/ledger-read.json. A bounded exact-ID search of historical batch Markdown found no prior hits; this does not establish global novelty.

## Strongest lead: 373598, held

An explicit graph on 18 vertices appears to refute Tian–Dong Conjecture 6.1 at r = 5 in its current preprint scope. Split its vertices into a nine-vertex clique and nine-vertex independent set. Cross-adjacency is defined by the cyclic offset set {0,1,2,3,5} modulo 9. It is 5-connected, has no induced K_(1,6) or K_(1,6)+e, and has no Hamiltonian path between two clique vertices.

[CASE-373598.md](CASE-373598.md) gives the complete ordinary proof, exact definition, finite checks and qualification objections. outputs/split-search.json gives the edge list. All 4,048 deletion sets of size <= 4 and all 15,444 centre/six-neighbour-subset pairs were checked. This remains ordinary mathematics and finite diagnostics, not a Lean certificate.

The full current source has the conjecture and its literal definitions. Its live abstract page lists only v1 and no journal reference. Positive evidence of retention in a published version was not obtained. The source cites a previous infinite family of non-Hamilton-connected split graphs; only search-visible primary text of that companion's final construction was accessible, while its full PDF timed out. A full augmentation/classical-example comparison remains undone. In accordance with the brief's material-source-gap stopping rule, this lane has not proceeded to a potentially zero-credit formal endpoint. Root should first resolve those gates and the significance objection that this may be a short modification of a classical balanced split obstruction.

## Other sustained routes

**348406: exclude the printed refutation from discovery credit.** The support-minimality polynomial was independently generated and tested against direct enumeration of all codewords in four small cases. A first diagnostic had incorrect bit indexing; logs are retained and superseded by logs/codes-corrected.log and outputs/codes-bridge.json. With correct indexing, the source's Proposition3.11 construction already gives 3,689 minimal codewords at k = 28, exceeding 3,347 from the printed Conjecture4.8 optimiser. This is inside its reported verification range k<=150. The arXiv PDF and Bayreuth repository version both contain that optimiser. This is exactly the prohibited source-ingredient/printed-inconsistency route, not a new significant solution. The intended corrected optimisation is not resolved.

**350364: no witness in substantial bounded searches.** The source's own proofs give the equal-cycle-incidence case and reduce the conjecture to its weighted max-cut conjecture; these ingredients were read before searching. An exact edge-transversal backtracker tested 7,059 seeded random triangle-free cubic/edge-deleted subcubic samples at orders8,10,12,14,16,18,20,24,30,40,50,60. Duplicates are possible; this is not a census. An independent normalized labelled cubic generator exhausted all 21,780 triangle-free cubic graphs of order 10 with N(0)={1,2,3}, which loses no isomorphism type. The order 12 run tested 967,020 such labelled graphs and stopped at its 110-second internal deadline; it is explicitly incomplete. Every tested graph admitted an exact-one-edge transversal of its5-cycles. Neither search proves the universal claim. The order 10/12 searches cover cubic graphs, not all subcubic graphs. The random run includes edge-deleted subcubic examples.

The attempted C++ implementation was not executed because g++/clang++ were unavailable. scripts/cubic-exact.py is the executed replacement; scripts/cubic.cpp is an unbuilt experiment. Logs retain the compiler failure and failed launch. No claims rely on the C++ file.

## Breadth checks and source fidelity

- 371967 is covered by the source's own arc-deletion characterization, rather than the unrelated Fraisse–Thomassen quotation in the database.
- 338977 has a direct later public resolution: Brettell–Semple–Toft arXiv:2409.13834 Theorem1.2 explicitly resolves the source Conjecture7.5, with missing exceptional families.
- 326282's Pawlik quotation refutes the general Scott conjecture, not the ISK4 four-colour question. All labelled graphs through order 6 were tested without a witness.
- 355759 passed all connected labelled graphs of orders 4 and 5 under the source's actual one-colour-per-edge, multiplicity1-or2 interpretation.
- 345350 passed the k=1 cases for every labelled loopless digraph of orders3 and4 meeting the semidegree threshold.
- 327034 passed every orientation of K4, the octahedron and the six-vertex wheel. Source conventions exclude digon-based paraphrase counterexamples.
- 351455 is about perfect truncated-metric codes. All6,859 cyclic quotient maps for singleton-centred n3,t2 balls failed to tile. The2025 published primary paper retains Conjecture1.9. General component-centred lattice tilings remain untouched.
- 354344's source proves the large-group regime; an all-orders solved assertion was not inferred from it. Exact small-group zero-sum partition runs cover11 explicit abelian groups through order 24, with no failure.
- 364299 has no failure among 46 sampled4-regular bipartite graphs at side sizes 4–10. Samples may repeat. Every sample had a disconnected spanning2-factor.
- 362979 has sphere-packing divisibility diagnostics only, not code existence certificates.
- 347519 is already source-covered through order 15 by its n/3 corollary for k5. No redundant small-range discovery search was claimed.
- 364090,365170,342671,361120 remain structural or semantic gaps. Penrose abstract-tree enumeration would not certify tile realizability or global leaf optimality.
- 402142 and399000 leaked through the finite metadata filter: the former has an asymptotic Omega constant, and the latter has joint spectral radius and unbounded word lengths. A finite numerical witness would not resolve either. Their EMS report bodies were not retrieved; landing pages and related primary materials are distinguished in results.json.

## Registry and access limits

Live /commits/HEAD receipts: OpenAI/math4eaee87548250b2682affda7d05d947c05554bae, unchanged from the brief; Omega8e15c484cf5786fe69fef0627fd84a63cfeb5942. Complete fresh Omega D5 and Problems trees had 13,912 and 1,717 entries, neither truncated. The targeted path-name screen had no hits. This is not a proof-body novelty audit. OpenAI's prior cached scope was not relabelled as a fresh full proof audit. receipts are in outputs/extra-receipts.json and outputs/registry-receipts.json.

All source HTTP requests retained TLS verification. No403/429/challenge route was retried or bypassed. The companion PDF timed out; access failure was not treated as clearance. Web-search leads are described as such and were not substituted for unread complete bodies. No external messages, publication, upload, git, browser tabs, shared edits or child agents were used.

## Reproduction and resource record

Run commands from this lane through scripts/run. For example:

```
./scripts/run python3 -I scripts/split.py
./scripts/run python3 -I scripts/cubic-exact.py 10
./scripts/run python3 -I scripts/cubic-exact.py 12
./scripts/run python3 -I scripts/bridge.py
./scripts/run python3 -I scripts/graph-small.py
./scripts/run python3 -I scripts/small.py
./scripts/run python3 -I scripts/groups.py
```

scripts/run sets lane-local TMPDIR/TMP/TEMP/cache paths, MALLOC_ARENA_MAX=2, two-CPU affinity, CPU 120 seconds and external wall 140 seconds. scripts/watch.py samples process-group RSS every 50 ms and kills the group over 6 GiB or its 137-second internal deadline. Full logs and sampled peaks are in logs/. At most one substantial search was active; small metadata/report operations could overlap. No Lean, leanchecker or solver executable was run. There are no upstream build or cache-trust claims. Source dependencies were not modified.

Important limits: sampling cannot exclude a transient RSS overshoot between polls. The wrapper has per-process CPU limits, not an aggregate child-CPU accounting proof. Diagnostic search implementations have not received independent review. No process remains running at handback. All remaining formal, source-fidelity, novelty and significance review is explicitly outstanding.
