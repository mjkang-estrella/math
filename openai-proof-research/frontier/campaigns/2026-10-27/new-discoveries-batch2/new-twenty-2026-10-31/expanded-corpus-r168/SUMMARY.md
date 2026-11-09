# Expanded corpus r168

One proved refutation candidate: **MathDB 381751**, the three-colour exception conjecture for split matchings. Two explicit 8-vertex components refute the conjecture at n=8 with colour counts (1,3,3). The ordinary proof, source fidelity, independent finite verification, literal Lean incidence endpoint and strict fresh replay are in `CANDIDATE.md` and the Lean packet. **Credit remains zero pending root review.** The main risks are proximity to the source's K4 parity obstruction and an unread bot-challenged author thesis.

`results.json` has exactly the 20 reserved ID keys, with literal statements, one-based raw provenance, chunk/raw/statement hashes, source hashes, review depths, attempts and gaps. Exact raw JSONL lines including their newline are in `raw/`. Fetch receipts, metadata/version screens, registry screens and logs are preserved. This is a bounded investigation, not a complete literature audit or a several-hour exhaustive examination of every target.

Prior outcomes disposed of without rediscovery credit include Aaronson's Hamming-sphere theorem (339247), the proved Nandi identities (344287), Takaoka's explicit refutation of the proposed line-grid obstruction list (344375), Wang–Zhao's Spiro equidistribution theorem (345225), and Haythorpe–Newcombe's secure domination formulas (347457). The global exceptional local-antimagic statement (345185) is not the precise source conjecture, and has adjacent credited-family risk. A preexisting Liu lexicographic counterexample claim and exact witness data preclude treating 357134 as new; its full verifier and proof were not independently replayed here.

The strongest computational routes were:

- Split matchings: complete alternating-cycle-reduced coverage through 14 vertices; partial search at 16 produced the witness. Separately, 500 random proper triples were checked for each n=7,8,9,10,12. The two exact witness verification methods agree.
- Regular hypergraphs (345607): exhaustive labelled simple 3-uniform regular hypergraphs on 4,5,6 vertices, and switched regular random constructions with r=3,4,6 at the parameter combinations in `outputs/hyperdeep.json`. Comparisons use exact powers of integers; no violation found. The row for n=7 in the initial output has an empty test dictionary and is **not** coverage of order 7. The current 2026 paper explicitly keeps the main conjecture open and blocks the occupancy shortcut.
- Triangular networks (355425): exact Fraction reductions at every step for initial orders 2 through 18 reproduce part (d). This remains within the source's numerical range through 250 and is not progress beyond it. Parts (a),(b) are already source results.
- Binary trees (350728): all patterns with 2 through 7 leaves on all 2,056 host trees with 1 through 9 leaves. No finite-signature separation; equality of finite signatures is not exact Wilf equivalence.
- Fuss paths (334972): exact independent path/connected sparse-partition counts agree at five listed (k,n) pairs, with source definitions rather than the paraphrase. No general bijection proved.

The other structural, continuous or algorithm-existence statements were parked with explicit gaps. In particular the unknown matroid threshold and polynomial-time-algorithm quantifier cannot be refuted by isolated small examples. No generic finite graph sweep is claimed for them. No scope was widened.

## Resource and process record

Searches and Lean builds used the retained wrapper: two-CPU affinity, CPU 120 seconds per process, wall 140 seconds, sampled process-group RSS approximately 6 GiB, MALLOC_ARENA_MAX=2 and lane-local TMPDIR. Every Lean build used -M3500 and later -j1. The wrapper is a sampled watchdog, not a cgroup guarantee. Fresh source downloads were inert data, read with isolated Python or pdftotext. TLS verification stayed enabled. GitHub searches were capped at eight, spaced eight seconds. The institutional thesis bot challenge was not bypassed or retried.

Two operational deviations are retained candidly: a `leanchecker --help` attempt was mistakenly made without a module argument and failed before it could launch Lean (PATH lacked lean); the actual verification supplies module `SplitMatching`. Also the small arithmetic Lean probe overlapped the abandoned large powerset Lean attempt briefly before that attempt was explicitly terminated. Their logs/receipts remain; subsequent expensive work was serialized. Initial exhaustive Lean attempts were too expensive and were replaced by the short arithmetic proof, rather than increasing limits or restarting killed background jobs. No background work is left at handback.

No shared ledger, git state, historical files, accounts or external messages were modified. New files are confined to this lane. Independent review, significance adjudication and acceptance belong to root.
