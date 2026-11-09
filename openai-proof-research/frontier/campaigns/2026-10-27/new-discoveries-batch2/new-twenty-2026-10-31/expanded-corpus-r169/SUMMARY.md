# r169 research disposition

No qualifying new solution or strong lead was found. All 20 reserved IDs have individual entries in results.json. Discovery credit is zero; no campaign count was changed. No literal Lean theorem, proof packet, independent review or acceptance is claimed.

This is a bounded investigation, not a proof of openness or an exhaustive literature review. All 20 literal corpus records were extracted with exact raw lines including newline, one-based chunk positions, chunk SHA-256, raw SHA-256 and statement SHA-256. All 20 current primary PDFs and arXiv abstract pages were fetched; the relevant conjecture paragraphs and selected neighbouring definitions/results were reviewed. This does not mean every page or historical version was read. Fetch URLs, dates, statuses and actual byte hashes are preserved.

## Dispositions

- **331606: excluded, known.** Its source's Theorem 4 explicitly proves the plateaux claim, using subdivision spectra and interlacing.
- **333167: excluded, known.** Nian Li (arXiv:1610.04441) settles two fractional-polynomial parts; Bartoli–Giulietti (arXiv:1708.04841, Theorem 2.3) settles the remaining one. The primary papers explicitly state the equivalence to the parameterized polynomial conjectures. Proof passages and the matching functions were inspected.
- **328049: zero-credit source correction.** Printed page 41 really describes forbidden-pattern words as factors of the Rote-Fibonacci word, although Theorem 37 says that word avoids the pattern. The proposed lengths also include lengths not divisible by three. The source page was rendered and inspected. This is not a substantive discovery.
- **370229: intended connected problem remains parked.** The literal disconnected formulation admits the elementary obstruction C5 disjoint K1,3: maximum degree 3 but the C5 component needs five proper conflict-free colours. The source itself discusses the C5 exception; this is a zero-credit domain correction. No formalization investment was made in it.
- **363000 and 375392: duplicate target, parked.** Both assert inversion diameter at most maximum degree. The later source cites a proof for maximum degree 3. No two-family credit is possible.
- All other targets are parked. Their exact mathematical gaps and actual review depths are stated individually in results.json. In particular, the reservation's finite metadata does not make the infinite tiling problem 324356, rational partition problem 335469, CSP dichotomy 366848 or asymptotic threshold equality 367106 into finite certificate problems.

## Reproducible searches

Every numerical search used scripts/limited.py, with logs and machine-readable resource receipts. Outcomes below are diagnostics, not formal proofs.

| Target | Completed search | Outcome and limit |
| --- | --- | --- |
| 337250 | Exact rational inertia on 2,132 base graphs: all nonempty graph-atlas graphs through order 7, plus 80 seeded random graphs per order 8–18; isolated padding 0–4, giving 10,660 cases | No failure. Exact inertia of nL−2mI includes zero eigenvalues. |
| 360376 | 2,514 base graphs, 94,445 precolorings of prism graphs | No completed failure; 15 cases hit the 10,000-node instance cap. Pair/triple colour partitions; at most 100 sampled cases per graph when more were available. Edge distance is minimum endpoint distance. |
| 334946 | All 7,770 three-part partitions with maximum part at most 35; 560 normalized four-part partitions with maximum part at most 14 | No surviving mismatch. Five accidental dependencies at t=2 failed later root choices. Four-root checks are not universal-root proofs. The intended parking criterion uses at least two actual permutations; empty-set wording is not exploited. |
| 372751 | Initial labelled/random sweep, all 1,252 nonempty atlas graphs through order 7, then 16 random regular graphs, degrees 3–6, orders 10, 14, 20, 30 | All completed tests colourable. The regular tests used Z3 with an 8-second instance timeout and all returned sat. Isolated edges are exempt. |
| 370229 | Initial labelled/random sweep and all 1,179 atlas graphs through order 7 with maximum degree at least 3 | No failure in those samples; trivial disconnected correction excluded. |
| 356282 | Labelled graphs through order 5, seeded random graphs through order 14, followed by the complete nonempty graph atlas through order 7 | No completed failure. See output JSON for exact unknown instances; initial random sweep has 391 node-cap unknowns. A failure with exactly Δ+2 colours alone would not exclude smaller equitable palettes. |
| 327891 | Exact game attractor on 55 atlas cop-win graphs with domination number greater than 1 and feasible state count | All contained by Δ cops. 232 eligible graphs skipped by the state-size guard. Not an all-graph test. |
| 363000 / 375392 | Exact inversion Cayley BFS on 208 nonempty atlas graphs through order 6 and 200 seeded random graphs of orders 7–10, with at most 15 edges | No failure. All edge-colourings of each selected graph were covered. |
| 367132 | All 1,252 nonempty atlas graphs through order 7; 420 instances with chromatic number at least 4 used explicit odd-path edge-packing searches | No failure. For chromatic number at most 3, the bipartite or odd-cycle argument supplies the required immersion. |
| 369727 | Exact minimal forts, disjoint-fort packing and zero forcing on all 1,252 nonempty atlas graphs through order 7 | This checks only known ft≤Z, below the source's order-8 range. It does **not** test Z*≤M: fractional optimization and certified maximum-nullity upper bounds remain missing. |
| 328049 | All binary x of length at most 10, testing minimality of xxx^R through total length 30 | Printed-formulation diagnostic only, zero credit. |

No finite Coxeter enumeration was completed for 328427: the actual object is Bruhat order on sortable elements, and its oriented forbidden diagrams need faithful implementation. No triangulation search was completed for 332071 because the full dual-complex arrow/corner encoding was not completed. These are explicit coverage gaps, not negative search results. No novel periodic tiling search was performed for 324356.

## Public registries and prior-art limits

outputs/registry-screen.json records terms, dates, queries, HEADs, hits and scope limitations. Lean Pool HEAD was obtained via /commits/HEAD and is 01db1d7049cf9668bda1e9e106875ee1278b43e6. Its complete 25,038-path tree, LeanPool/projects.yml and all candidate files were screened. The first guessed root projects.yml URL returned 404; the actual file path was recovered from the tree. There were no 403/429 denials or bot challenges in the saved HTTP receipts.

Eight repository-search queries, spaced by at least eight seconds, returned zero repositories. They cover inversion diameter, conflict-free colouring, Cameron/forts, the star source arXiv ID, precoloring, Cambrian lattices, the trinomial arXiv ID, and containment/robber. These are narrow repository searches, not GitHub code searches or proof of absence.

Omega HEAD was 46927cc328c58a872092e1d1c3bf102e48fa0426; OpenAI/math HEAD was 4eaee87548250b2682affda7d05d947c05554bae. The initial recursive root trees were truncated, so complete pinned D5 (13,991 paths), Problems (1,738 paths) and OpenAI preprints (13,578 paths) subtrees were separately fetched and screened. Name matches were unrelated topics; numeric substrings inside object hashes are not problem-ID hits. This is a path/text screen, not comprehensive proof-body review or worldwide priority clearance.

Prior campaign histories were searched by literal IDs and titles; digit-boundary filtering removed accidental numerical substring matches. The retained hit was this lane's launch note. Inherited accepted/excluded families remain binding. Ledger snapshots are read-only evidence; no shared file was changed.

## Files and replay

- results.json: exactly 20 ID-keyed entries, literal statements, provenance, source hashes, review depths, attempts and remaining gaps.
- CANDIDATE.md: no surviving candidate and no Lean packet warranted.
- extracted.json and raw/: immutable literal corpus extracts.
- sources/: downloaded PDFs, text, arXiv version pages and pinned registry responses.
- outputs/: all search data, registry screen, fetch receipts and hash manifest.
- scripts/ and logs/: reproducible programs, full stdout/stderr and resource receipts.

Run a numerical script using a real script path, for example:

```bash
python3 -I -B /absolute/lane/scripts/limited.py spectral-replay python3 -I -B /absolute/lane/scripts/spectral.py
```

NetworkX and Z3 are reused read-only from sibling r58/deps; bytecode writing was disabled for those imports. No package was installed. Record that local dependency trust limit when replaying. No Lean compiler or leanchecker was invoked, so no kernel-verification or upstream-cache rebuild claim applies.

The wrapper restricts affinity to two CPUs, sets CPU time to 120 seconds per process and a 140-second wall limit, and samples process-group RSS against 6 GiB. MALLOC_ARENA_MAX=2 was supplied. These are sampled user-space guards, not a cgroup guarantee. No process was killed by the wrapper or restarted after a maximum timeout. One initial extension run had a palette-index bug; it was corrected and the failed log retained. The first four-root criterion diagnostic admitted empty permutation collections; its corrected rerun is the reported result. No background process remains.

All writes were confined to this lane. No git, shared-ledger edits, child agents, browser tabs, external messages, accounts, uploads or author contacts were used. The pass did not establish a new mathematical solution and is not represented as the several-hour exhaustive investigation envisaged by the brief; the explicit uncompleted searches and source/novelty gaps above remain parked.
