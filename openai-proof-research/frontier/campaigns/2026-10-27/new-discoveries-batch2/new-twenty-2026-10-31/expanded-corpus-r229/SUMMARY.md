# expanded-corpus-r229

No qualifying new solution was obtained. Eight reserved records are excluded by prior resolutions or a proof already in their own source. Twelve are parked; four of those were pursued through three explicit computational mechanisms. There is no proposed Lean endpoint, proof packet, acceptance, or campaign-count change.

The deliverable `results.json` contains exactly the 20 reserved ID keys, their literal statements, one-based corpus locations, chunk/raw/statement SHA-256 hashes, source receipts, review depth, attempts and remaining gaps. Original JSONL lines retain their final newline. `ATTEMPTS.md` explains the algorithms, their limitations and the failed proof routes. `artifact-manifest.json` binds retained files by SHA-256.

## Prior results found before search

- **357590:** Shahverdi, Journal of Algebra 642 (2024), Theorem 1.3 gives the exact nilpotency/direct-product conclusion under the center-size hypothesis. Indexed primary theorem text was found; the publisher proof body was not downloaded under the inherited ScienceDirect denial. [DOI](https://doi.org/10.1016/j.jalgebra.2023.12.007).
- **357600:** Hollom's counterexample already refutes k = 1. The proof is also public in Lean Pool and mathlib; the pinned public source and current mathlib documentation are retained. [Primary paper](https://arxiv.org/abs/2411.16844).
- **357636:** Wilde and Fischer's published Theorem 5 proves the exact n >= 2k+3 uniqueness threshold. The follow-up statement and induction proof were read in the retained PDF. [Published paper](https://link.springer.com/article/10.1007/s00026-026-00848-4).
- **357745:** The SODA 2025 lower bound 14n/9 - O(1) already refutes the proposed 3n/2 bound; the 2026 citing paper states this explicitly and obtains a further improvement. [Citing primary paper](https://arxiv.org/abs/2603.22262).
- **357805 and 357806:** The source authors' companion Theorem 3.5 settles the entire cylindrical-grid family, including the intended positive odd-height range. [Companion paper](https://arxiv.org/abs/2303.12222).
- **358220:** Deb's source itself proves the full Sokal-Zeng conjecture, including the indexed fixed-point weights. [Source](https://arxiv.org/abs/2304.14487).
- **358355:** Kong and Zeng's Corollary 2 proves both parity cases of the covering bound. [Primary paper](https://arxiv.org/abs/2509.13877).

These are exclusions from this discovery campaign, not new results of this lane.

## Sustained finite routes

**357880:** Recovered the reduced bipartization and actual moment-curve rigidity matrix. Exhausted every relevant-diagonal subset yielding a triangulation for (k,n) = (3,9), (3,10), (3,11), (4,11): respectively 30, 330, 4719 and 55 triangulations, all with full specialized row rank modulo 1000003. Extended random-subset searches at (3,12) and (4,12) also found no deficient matrix. The source's printed nongeneric K9 obstruction does not refute generic independence. Missing: an identically dependent triangulation or a uniform specialized-minor proof with the full basis bridge.

**358018:** Implemented invariant mod-two cycle generation, minimal-circuit checking, deletion-based 4-connectivity, a sufficient nonplanarity filter, and the full ordinary rigidity matrix with half-turn symmetric coordinates. Exhausted invariant cycles on six and eight paired vertices. Extended ten-vertex sample: 100000 cycle trials, 1675 full-vertex minimal circuits, 1655 eligible trials; no rank failure. Missing: a generic half-turn obstruction or uniform rank theorem. Sampling, labeling multiplicities and the incomplete nonplanarity filter are explicit limits.

**358524/358525:** Implemented minimal forward/inverse support graphs, directed reachability and augmenting-path matchings. Exhausted binary matrices through size four and ternary matrices through size three; extended sparse samples cover dimensions through sixteen over F_3, F_5 and F_101. Every tested feasible problem admits weakening at most three. This does not prove the required dimension-independent constant, and even a counterexample for c = 3 alone would not refute the existential conjecture. The attempted Hall-inequality route remains open.

Other records were given source-backed dispositions without indiscriminate sweeps: coarse geometry (357610), higher-dimensional boundary actions (357678), counting circuit double covers (357791), oriented matroids (357850), Painleve coefficient irreducibility (358043), transmission eigenvalues (358112), ISK4-free colouring (358308), and odd strong immersions (358391). The October 2026 diamond-free colouring paper was checked; it explicitly retains the general ISK4-free conjecture.

## Provenance and access limits

All listed arXiv versions exposed by the source abstract pages were downloaded into this lane, with immutable request receipts. Current GitHub heads were retrieved for OpenAI/math, Vilin97/lean-pool and the Omega repository. Lean Pool's recursive tree is complete. The OpenAI and Omega root recursive trees are truncated; OpenAI's preprints subtree was therefore retrieved separately. A title/path search and topical GitHub web search are bounded screens, not content-complete proof-registry clearance. No novel candidate survives to require a stronger priority audit.

The inherited denied services were not directly requested. Search-engine results occasionally included indexed pages on denied domains; those were not opened or fetched. No TLS verification was disabled, no challenge or 403/429 was retried, and receipts were not overwritten. No downloaded code was executed. PDFs were processed as untrusted data with Poppler; no archives or dependencies were installed.

The three instructed AGENTS.md files, current and prior ledgers, prior-campaign context, protected/excluded families and task instructions were consulted read-only. Historical search found no substantive exact-ID/title disposition for this reservation beyond assignment metadata; incidental digit/hash matches are not prior reviews. No global novelty inference is drawn from this.

## Execution audit

Numerical scripts used the lane-local resource wrapper: CPU affinity to two CPUs, CPU 120 seconds, wall 140 seconds, sampled RSS limit 6 GiB, address-space limit 12 GiB, MALLOC_ARENA_MAX=2. Logs retain the wrapper's actual resource limitations: sampled parent-process RSS is not a cgroup guarantee. All recorded searches completed normally; no Lean was invoked.

Two execution deviations are recorded rather than concealed. The initial body-downloading invocation used `python3 -B` instead of isolated mode; it ran only the locally authored downloader and was immediately replayed as `python3 -I -B` after making its local import explicit. No bytecode was written. Also, the first 100000-trial symmetric extension briefly overlapped the still-running CI-fields search because a partial log was mistaken for completion. Both used about 14 MiB RSS, but this did not follow the requested serialization. After CI-fields finished, the symmetric extension was replayed sequentially under a distinct retained log. No background numerical process remains.

This pass contains actual source review and reproducible finite searches, but does not claim several hours of work, exhaustive enumeration for every finite object class, a full literature search, or successful completion of the discovery objective. Root should use the precise parked gaps, not treat negative diagnostics as solved records.
