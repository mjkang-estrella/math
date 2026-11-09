# Parked deep search r1

Zero discovery or acceptance credit. No counterexample was found. This is a bounded computational follow-up on two shortlisted targets, not a resolution of either full conjecture. No Lean theorem or kernel replay is claimed.

## 345754: divine colouring

The corrected SAT encoding finds a colouring of {1,...,1024}; an independent checker verifies all 6,238 finite cascades and every CNF clause against its complete model. A separate N=4096 SAT run hit its 85-second wall limit with UNKNOWN. The subsequent model-check attempt correctly failed because there was no model; it establishes no negative result.

The source itself describes the Liouville construction and the known very large first positive summatory value. Thus extending this finite range is not a discovery. We independently constructed a Liouville witness on {1,...,1,000,000} and directly checked all 12,970,034 cascades. Maximum root-sign times tail sum is -1, so every condition holds. See outputs/divine-liouville-1000000.txt, its witness JSON, and logs/verify-liouville-1000000.log. This extends the locally checked frontier to one million, with explicit zero novelty credit. The infinite existence conjecture remains open in this work.

An initial incorrect counter prototype and its solver outputs remain marked `.invalid`. It omitted the first term of each running tail count. These files are excluded from all conclusions; the source definition was checked directly for every retained positive witness.

## 340618: centered Schur triples in the cyclic group of order 32

New encodings target n=5, asking for a strict improvement over the minimum centered value at each tested cardinality. Ordered triples, repeated generators and zero are included. Direct membership and complement encodings are described in ENCODING.md. No symmetry breaking is used.

The final machine-readable results list each independently checked UNSAT case and its exact trimmed LRAT size, number of additions, CNF hash and proof hashes. The original-membership cases M=29,30,31 have passed the independent RUP checker. The complement case M=27 also passed the independent RUP checker. Centered ST values are respectively 756,840,930 and 600.

At M=28, the solver returned UNSAT, but its raw proof is roughly 537 MiB and has NOT been trimmed or checked. This is provisional solver output, not an independently certified settlement. M=18 through 26 were not searched. M<=16 is trivial and M=17 is already the source's Theorem 1.8. Therefore the WHOLE n=5 case is not settled. No CANDIDATE file is proposed: these are finite parameter cases with zero credit under the campaign rules, and large certificates make the current encoding unattractive for Lean replay.

## Literature, provenance and resources

LITERATURE.md records the exact primary statements, source sections, live queries, citing-work leads and remaining access gaps. Fresh arXiv receipts bind the current abstract bytes. The 2026 majorization paper is about an elementary abelian group, not this cyclic group. No global novelty clearance is claimed.

Lean Pool HEAD was fetched live: 01db1d7049cf9668bda1e9e106875ee1278b43e6. Its complete tree, projects.yml and all 10 candidates files were fetched at that immutable revision. Literal topic/identifier screening found no hits. Two spaced unauthenticated GitHub repository queries, one per source identifier, were made; receipts preserve the statuses and bodies. This is bounded screening, not semantic theorem-body clearance.

The four inherited lanes were read as text only. inputs-before.sha256 binds their files; inputs-after-check.log records the after-check from the original workspace root. No inherited script was imported or run. All artifacts, caches, TMPDIR and downloads are local to this lane; every download used a fresh empty directory. TLS verification remained enabled. No denied access was retried or bypassed.

Python and solver runs use scripts/run.sh and scripts/cap.pl: two CPU affinity, CPU 120 seconds, wall 140 seconds, RSS watchdog 6 GiB and MALLOC_ARENA_MAX=2. Solver runs have additional smaller wall limits. Heavy runs were serial and no limit was raised after a failure. No software installation, git, shared-ledger edit, child agent, browser tab, upload, external message or author contact. No background job remains at handback. Root alone decides any subsequent review or acceptance.

## Deliverables

- results.json: exact coverage, solver statuses, checked certificate sizes and hashes.
- ENCODING.md: formulas, source bridges, checker interpretation and reproduction.
- LITERATURE.md and downloads/: bounded prior-art and registry evidence with receipts.
- scripts/: new encoders, resource wrapper, checkers and fetch/report utilities.
- outputs/: CNFs, finite witnesses, raw and trimmed LRAT proofs and check reports.
- logs/: full solver and checker output, including failures and UNKNOWN.

No CANDIDATE files, Lean packet, new-to-literature claim or acceptance claim.

Final certificate sizes: M=27: 94,573 additions, 70,952,634 bytes; M=29: 40,210 additions, 96,374,523 bytes; M=30: 94,874 additions, 17,047,265 bytes; M=31: 7,302 additions, 1,200,171 bytes. Total: 236,959 additions and 185,574,593 bytes. All four cases were also independently checked by exhaustive enumeration of complements (201,376; 4,960; 496; 32 subsets respectively), agreeing with minima 600, 756, 840 and 930.
