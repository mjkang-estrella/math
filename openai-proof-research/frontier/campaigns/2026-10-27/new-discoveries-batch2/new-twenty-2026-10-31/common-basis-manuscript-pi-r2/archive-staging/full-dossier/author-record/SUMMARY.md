# expanded-corpus-r250

One exact counterexample candidate: **MathDB 332371**, Lasoń's common-basis conjecture. No acceptance or campaign-count change is made. Independent fidelity, novelty and significance review remains necessary.

The candidate is a rank-four matroid on nine labeled elements, with 76 explicitly specified bases. Deleting element 1 or element 6 permits a partition into two bases, but no two such partitions can share a base. The ordinary binary representation has columns 9,6,4,11,6,14,5,1,12. See CANDIDATE.md for the precise statement, partitions, source fidelity, literature limits and reproduction instructions.

The strict Lean theorem `CommonBasis332371.counterexample` in lean/Final.lean has compiled with Lean 4.34.1, `-M3500 -DwarningAsError=true`. It uses an actual Mathlib `Matroid (Fin 9)`, proves ground cardinality 9 and rank 4, exhibits both partitions, and excludes every shared-base pair. The endpoint's transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. The metadata/axiom audit checks 106 local declarations, including generated declarations. **Fresh extracted strict rebuild and leanchecker PASS for all 12 modules (24 successful stages), recorded in replay-result.json. The verified source packet is lean-packet-final.zip; extracted build is replay-final/build.** No failed compilation's `sorryAx` report is a successful proof: the early failed logs are retained separately, and the successful endpoint has none.

Exactly 20 reserved entries, with literal corpus statements, one-based raw provenance, chunk/raw/statement SHA-256 hashes, review depth, sources, attempts, outcomes and remaining gaps, are in results.json. Raw JSONL lines retain their original newlines. Source versions and download receipts are in sources/. Nothing outside this lane was edited; no git, child agent, ledger edit, publication or external message was used.

## Other outcomes

- Previously resolved or source-proved: 332895 (Hogben–Shaked-Monderer 2019 refutation), 333073 (source Theorems 8 and 10), 333351 (Xie et al. 2026 Corollary 1.7), 333686 (Gregor–Micka–Mutze central levels theorem), 333882 (Wigal–Yoo–Yu exact TSP bound).
- Zero-credit generic support failure: 333511. At time one a 3-cycle on six letters has probability zero, while a fixed-point-free involution has positive probability, contradicting the claimed cycle-lex order. This is a generic step-support issue, not a significant new discovery.
- The remaining 13 targets are parked. Partial results are not upgraded to full resolutions: in particular, Balogh–Li's sufficiently-large-n theorem for 333208 and the inner-faithfulness ranges for 332491 do not silently settle all literal parameters.

## Exact computations and limits

Every numerical/Lean run used scripts/limited.py, two-core affinity, CPU 120 s, wall 140 s, sampled RSS 6 GiB and MALLOC_ARENA_MAX=2. RSS monitoring samples the child process; it is not a transient-peak or cgroup guarantee. Heavy processes were sequenced. Early Lean attempts failed by allocation, thread creation, or process termination; the smaller explicit List-based checks succeeded at about 2.2 GiB sampled RSS. All attempts and failures have full logs and receipts. There are no residual background jobs at handback.

- 332371: random binary-matroid exploration; the successful rank-four instance independently checked using all XOR combinations and every basis-exchange condition. The exploratory script stops when it finds the candidate, so its later planned rank/k ranges were **not** run.
- 333397: all 22,369,620 ordered composition pairs for n=2 through 13; no violating Frobenius block. The n=13 layer contains 7,678 Frobenius cases. A second search sampled 12,000 pairs through n=200, including 144 Frobenius cases; no violation. Blocks use exactly source equations (1),(2). These are diagnostics, not a full Lie-algebra formalization.
- 332512: avoidance-class generation through size 9, with complete component distributions agreeing. The literal conjecture's source locator remains a fidelity gap; the source and journal print relevant generating functions.
- 333794: all eligible multipliers at eight listed small (t,n) pairs; no failure. The source already reports all t^n<3e9. Additional adjacency-witness sampling at five larger moduli is incomplete and gives no counterexample or exhaustive clearance.
- 333208: all labeled graphs through order 5, counted exactly through partial three-colour edge assignments; the complete graph is uniquely extremal in this checked range. This does not bridge the unknown explicit threshold of the published asymptotic result.
- No exhaustive algorithmic, analytic, consistency-strength, knot-invariant, or asymptotic-class-speed conclusion is claimed from finite samples. Individual unsearched targets are explicitly marked in results.json.

## Literature and registry scope

Literature and citing-work searches preceded numerical discovery and Lean investment. All advertised arXiv source versions were fetched, hashes and HTTP status retained, and selected primary conjecture/theorem bodies reviewed. Candidate-specific searches were deepened after discovery, and the journal's actual Conjecture 2.5 was inspected. No matching prior resolution was located, but absence from these searches is bounded evidence.

Current OpenAI/math, Omega trureturing and Vilin97/lean-pool heads and trees were fetched. Lean Pool's untruncated tree and every raw candidates/ index file were screened, including discovered.yml, decisions.jsonl, both queues, manual/provenance and shortlist. OpenAI and Omega recursive root trees are truncated; their path screens are explicitly incomplete. The current OpenAI overview was also fetched. GitHub repository searches for candidate-related Lean work returned no matches; this is not all-code semantic clearance. Inherited denied hosts were not retried. The AIM SPN follow-up PDF URL returned 404 HTML; it was not treated as a PDF proof. No TLS bypass, challenge bypass, forbidden API, or retry of a 403/429 was used.

The proof trusts prebuilt pinned upstream package oleans (mathlib d13f23b723b8a846827a245b89c10fc7d3f11612), not a full upstream rebuild or independent source-to-olean attestation. `leanchecker` shares the Lean installation. Independent review, paper preparation and root acceptance are separate downstream steps.
