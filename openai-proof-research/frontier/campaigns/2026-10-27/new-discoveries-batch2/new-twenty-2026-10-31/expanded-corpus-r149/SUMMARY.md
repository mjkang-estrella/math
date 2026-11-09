# Expanded-corpus discovery lane r149

No new qualifying endpoint was found. Four IDs are already covered by primary public results; sixteen are parked with explicit gaps. Nothing is self-accepted, and no campaign count changes. results.json has exactly the 20 reserved IDs, literal statements, raw provenance, review depth, mathematical attempts and remaining gaps.

This is a bounded investigator report, not exhaustive literature clearance. It records a shorter investigation than the several-hour depth pass envisaged in TASK.txt. Not every cited construction, institutional thesis, historical arXiv body or companion-paper proof has been read. No unresolved lead is promoted as novelty-cleared.

## Primary-source exclusions

- **363699:** Cossaboom, arXiv:2406.18480, Theorem 1.2 explicitly proves both hook-bias assertions. Theorem 1.3 and its asymptotic and strict-constant proof sections were inspected. The MathDB status conflicts with its own text.
- **363950:** Current Song–Wang Remark 5.9 identifies Eriksson's proof. Eriksson, arXiv:2602.18612, Theorem 4.1 and proof give the correspondence, level-one specialization and restriction compatibility.
- **359867:** Pálvölgyi, arXiv:2309.04603, Theorem 3 explicitly refutes the conjecture: m₂ = 3, m₃ = 6, against bound 5. The full 8-vertex construction and restriction argument were read. The 2026 companion arXiv:2604.24412 extends these counterexamples; it does not settle 359866.
- **382196:** Source Remark 5.4 reduces filtered invariance to full invariance. The actual full-invariance theorem was read in pinned OpenAI/math build/01-introduction.tex. Directed Bruhat graph isomorphism preserves interval order by reachability, so it applies without the extra colors. Upstream truth is accepted under campaign instructions, not independently audited here.

## Sustained finite routes

**Subcube weights, 382034.** Current v4 retains the weight conjecture; its refutations concern other extrema. Theorem 2.28 already reduces the weight lower bound to minimum size. That proof and constructions 2.29–2.30 were read. Source minimum-size verification reaches n = 7; a new counterexample should start at n ≥ 8.

All 154 and 89,512 labelled partitions in dimensions 3 and 4 were enumerated, yielding 8 and 824 tight irreducibles and exactly the predicted minimal weights. An optimized dimension-5 search through nine cells completes modulo coordinate permutation of the zero-containing cell: 2,773,317 nodes and 7,896 tight irreducibles, no counterexample. This is not all dimension-5 partitions. An earlier slower partial run is superseded, not added. The first dimension-8 attempt through 15 cells stopped after 9,043,968 nodes without a completed partition; it proves no lower bound. Its initial facet-containing branch is unproductive: a facet forces the complement to be a subcube, violating irreducibility of a tight partition in dimension > 1. A second run skips that branch; its final log supplies exact limited coverage. Neither dimension-8 run is exhaustive.

**Group subsquares, 354345.** Exact transversal backtracking tests every ordered equal-sized subset pair containing the identity in cyclic groups of orders 2–12; C₂ × C₂, C₂³, C₄ × C₂, C₆ × C₂; and dihedral groups of orders 6, 8, 10, 12. Translation normalizes arbitrary A and B independently. Every failed transversal matches a printed exception. Logs record exact pair counts, including 705,432 per order-12 group; repeated groups are not extra coverage. This tests the actual subsquare claim, rather than rediscovering full-table Hall–Paige.

**Bernstein colorings, 362930.** Definition 5.1, Proposition 5.3 proof and Conjecture 5.4 were inspected. Beyond the reported 5 × 5 check, 50 independent 6 × 6 graphs were generated at each of 18, 21, 24, 27 edges. Nonzero minors modulo 1,000,003 of integer rigidity specializations provide diagnostic independence witnesses. Up to 2,000 random integer zero-sum labelings per graph yield forest colorings in 129/200 cases. Five saved difficult examples receive simulated annealing: four yield explicit valid labels; one remains at cycle/tie cost 1 after 200,000 moves. This search failure establishes no absence of a real coloring.

**Q-polynomial closure, 355361.** Exact character enumeration covers all 7, 127 and 32,767 nonempty connection sets in F₂², F₂³ and F₂⁴. Connected counts: 4, 92, 31,232. Q-polynomial counts: 4, 71, 2,882. No Hadamard-closure failure. Integer eigenvalue classes determine character power filtrations, and class convolutions test idempotent closure. This covers labelled cubelike graphs, not every graph on 16 vertices. A NumPy graph-atlas attempt failed for missing dependency and gives no atlas coverage.

**Rounded penny bound, 372361.** The exact k = 7 recurrence in source Proposition 4.1 agrees with the rounded quadratic bound for every n ≤ 10,000,000, beyond the source's reported 366,536. Integer-square comparisons avoid floating point. A uniform recurrence inequality proof, general k, and literal geometry bridges remain absent.

**Hamilton edge lengths, 368808.** All admissible length histograms are realized through order 11. Source already reports verification through order 37, so this is only an implementation check. Extension beyond known coverage requires count-vector DP/SAT rather than factorial path enumeration; no improvement claimed.

The other targets involve unknown asymptotic constants, thresholds, infinite colorings, or substantial residue/topology semantics. A finite sample cannot negate their quantifiers. Each results.json entry records a source section and specific missing argument. The sunflower constants' dependence on r needs clarification; varying m₂ in the 2026 polychromatic construction does not refute finiteness at fixed m₂.

## Evidence and operational limits

Exact newline-preserving corpus records are in raw/. outputs/extracted.json binds one-based lines and chunk/raw hashes. results.json also hashes literal statements. All 20 current arXiv abstract pages and PDFs have dated URL/status/SHA-256 receipts. Named primary-body sections were read. Every old arXiv body was not downloaded.

Campaign/batch ledgers and inherited accepted/excluded families were read into snapshots. Bounded historical ID searches found only hash-substring false positives, not substantive earlier ID dispositions; this is not global nonreview evidence.

Live OpenAI HEAD: 4eaee87548250b2682affda7d05d947c05554bae. Live Omega HEAD: 07722effd921f36c97cc732326e6131aa04920ad. Complete nontruncated OpenAI preprints and Omega D5/Problems path screens are retained. Only the relevant OpenAI KL theorem was read for an exclusion; no all-proof semantic registry clearance.

Broad recursive registry downloads timed out, leaving invalid partial JSON; narrow subtree retrievals succeeded. The first KL source path returned 404; the actual build/01-introduction.tex path succeeded. Failures are not novelty clearance. No inherited denied or challenged route was retried.

Every Python process used scripts/cap.sh: CPUs 0,1; CPU 120 s; wall 140 s; 6 GiB sampled aggregate RSS watchdog; 64 GiB address cap; MALLOC_ARENA_MAX=2; isolated Python; lane-local TMP/cache. One numerical process at a time. RSS sampling is not an instantaneous cgroup guarantee. Some scripts stop internally at 100 seconds.

No Lean or leanchecker endpoint was run because no qualifying ordinary proof emerged. No dummy bounded theorem or numerical diagnostic is presented as a solution. No git, shared ledger modification, child agent, publication, upload, author contact, external message or browser tab was used. Root alone decides acceptance.

Reproduce numerical runs via scripts/cap.sh python3 -I scripts/SCRIPT.py ARGUMENTS from this lane. Full logs, including failed attempts, are under outputs/; source bytes and headers under sources/. outputs/manifest.json hashes the retained artifacts.

## Historical alias correction

A later title-based historical search found that 368808 is the same Buratti–Horak–Rosa problem as protected, parked ID 354609 in r142. That older report already records McKay–Peters verification through order 37. The route is stopped and the old disposition retained. The order-11 run here is redundant diagnostic coverage, not new investigation credit. Exact-ID searches alone missed this alias; the results entry records the correction.

Final second dimension-8 log: 9,682,944 nodes, no completed partition, 100.097 seconds, not exhaustive. Neither capped dimension-8 run is counted as completed object coverage.
