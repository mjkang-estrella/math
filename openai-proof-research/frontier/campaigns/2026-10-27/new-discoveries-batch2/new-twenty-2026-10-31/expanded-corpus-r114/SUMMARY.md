# expanded-corpus-r114 research handback

No qualifying new solution and no Lean packet. All 20 reserved IDs (368078 to 370017) have ID-keyed dispositions in `results.json`, with literal statements, exact raw provenance (chunk, one-based line, chunk/raw/statement SHA-256), source receipts, review depth, attempts, outputs and remaining gaps. Credit is zero. Campaign counts and shared files were not changed. No git, no child agents, no background jobs left.

## The one exact counterexample found, and why it gets zero credit

**369616 (line-graph inertia, Akbari, Elphick, Kumar, Pragada and Tang).** The conjecture says that for every connected G, n+(L(G)) <= n-(L(G)) + 1. Exhaustive sweeps beyond the authors' 9-vertex check found no violation (cyclomatic number 1 for n <= 15, 2 for n <= 13, 3 for n <= 13, 4 for n <= 9). Edge-swap annealing at 14 to 40 vertices then found violations. The smallest is the connected 14-vertex, 16-edge cactus C5, bridge, C4 (entered and left at adjacent vertices), bridge, C5. Its line graph has inertia (9, 0, 7), certified exactly by the integer characteristic polynomial and Descartes' rule of signs, which is exact because all roots are real. More generally, C_{4a+1} - C_{4b} - C_{4c+1} chains give signature 2.

The live prior-art check showed that the identical cactus with inertia (9, 0, 7), a 48-vertex example, and unbounded signature were already public: arXiv:2607.22874, v1 24 Jul 2026 ("The signature of connected line graphs is unbounded"), also posted as SSRN preprints by A. Paone. This is therefore an independent rediscovery of a public refutation and is excluded.

A side observation: the source's remark "for any tree T, s(L(T)) <= -1" is false. L(P5) = P4 has signature 0. Guo's theorem gives s <= 1, which still suffices for trees.

## Exclusions found before investment

| ID | Reason |
| --- | --- |
| 369280 | Already formalized as `shuffle-quadratic` in the 2026-10-25 campaign; a known Tripathi result. |
| 369281 | Already handled as `shuffle-spectrum` (2026-10-25): the endpoint is false at n = 4. This is an index-range correction. |
| 369568 | Live Omega registry proof: `Problems/caldwell-2024-super-catalan-action-graph-ntable.md`, Lean `SuperCatalanActionGraphRecurrence.result`. |
| 368317 | Published resolution: arXiv:2512.12251 proves mutual-visibility colouring NP-complete. |
| 368397 | Refuted by its own source: arXiv:2505.08131 gives a non-regular 11-vertex counterexample and infinite non-regular families. |

## Sustained finite searches with no counterexample (parked)

**368743 (unicyclic square energy).** For unicyclic graphs s+ + s- = 2n, so the claim is a sign condition on the sum of lambda|lambda|. The lane enumerated every odd-cycle unicyclic graph up to isomorphism for n <= 15; counts match OEIS. It also ran local search at n = 20 to 40 for k = 5, 7, 9, 11, 13. Margins shrink to about 1e-5 but never change sign. For uniform leaf coronas, an asymptotic expansion shows that the leading term has exactly the conjectured sign by k mod 4. The conjecture looks true.

**368742 (strong positive square energy).** Exhaustive search covered cyclomatic number 2 for n <= 13 and 3 for n <= 10, plus annealing up to n = 40. The minimum of s+ - n plateaus near 0.54 for c = 2 and grows with c.

**368745 (maximal planar and outerplanar).** For the outerplanar part, the lane checked all polygon triangulations up to n = 14. For the planar part it ran an exact flip-graph enumeration of triangulations for n <= 12 (counts match OEIS A000109). Both thresholds are exact: the bounds fail at n = 7 and n = 9 respectively and hold beyond, with margins increasing. The planar extremal is the source's own bipyramid.

**369839 (vincular Stieltjes).** An exact O(n^3) rank DP computes P_n(x), and quotient-difference S-fraction coefficients were checked against exact inversion. For both classes, 90 coefficients are positive at x = 1/100, 1/2, 3 and 100. The authors checked 30 and 37 coefficients.

**368352 (chromatic symmetric functions of unicyclic graphs).** The exact CSF code was cross-checked against brute force for all 143 unicyclic graphs with n <= 8. It reproduces the source's even-n triangle collisions. It was run on every 5-cycle unicyclic graph on 16 and 17 vertices, beyond the source's c = 5 range of n <= 15. At n = 16 there are 50,871 graphs and exactly one CSF collision pair, confirmed by brute force. The pair shares degree sequence, rooted-tree count and internal-edge count, so the conjecture holds, though CSF no longer separates 5-cycle graphs at n = 16. At n = 17 all 145,146 CSFs are distinct. The 3-cycle case at n = 17 (about 300,000 graphs) was not run.

**368305 (vertex-capturing game).** The source already reaches n <= 9. The case n = 10 is a 45-edge positional game, infeasible within the caps.

## Hard or beyond-source items given source-backed dispositions

- 368078: normality of an infinite word.
- 368244: magnetic shape optimisation.
- 368967, 368970, 368973: Speyer g-polynomials. The source data covers 3.29 million graphs and K_{3,n} for n <= 60. There is no Mathlib theory.
- 369640: plabic intersection number, from computations for m <= 8.
- 369642: reduced Dressian, verified by the source for 7 <= n <= 26.
- 370017: average-case hardness.

## Registries and access

- openai/math HEAD is 4eaee87548250b2682affda7d05d947c05554bae (unchanged).
- Omega HEAD is **ddeafbc85f06ddade64bc7aab47c37698ecd7fe6**, which is newer than the root-known 9a49565d. The lane fetched the complete Problems (1,668 entries) and D5 (13,565 entries) listings and ran a path screen; see `outputs/registry-screen.json`.
- arXiv HTML and abstract pages returned 200. A web search was used for prior art. No denied routes were retried.

## Resources

Every numerical process ran under `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB, address space 12 GiB, with logs and receipts in `logs/`. Two runs hit the cap and are recorded:
- the first broad grep (replaced by a single-pass grep);
- an exact-rational S-fraction run (replaced by Decimal quotient-difference).

No Lean, SAT, Java or pip installs were used.
