# Expanded corpus r73 handback (MathDB 377968–379120)

The lane proposes one candidate: **MathDB 378395 is refuted with a literal Lean endpoint**. All 40 entries carry zero credit. The accepted count is unchanged at 9/20 beyond the 39 prior results. No shared ledger, index or historical report was edited. There were no child agents, git operations, browser tabs, publications, uploads or external messages, and no background jobs remain.

## Candidate: 378395, the collapsing conjecture (Eriksson–Fienberg–Rinaldo–Sullivant)

**Conjecture.** For p ≤ q ≤ r, every facet of the no-three-factor marginal cone P_Δ^{p,q,r} is obtained by collapsing from a facet of P_Δ^{p,q,q}. The source checked this only through 4 × 4 × 4.

**Counterexample.** Take p = q = 4 and r = 5. An explicit integer inequality defines a facet F of P_Δ^{4,4,5}:
- it is nonnegative on all 80 columns;
- its 45 tight columns have rank 43, one less than the cone's dimension 44;
- its five slices have pairwise distinct zero patterns.

Any collapsing to 4 × 4 × 4 must merge two states of the 5-state variable. A pulled-back face has identical patterns on merged slices, so F is not obtained by collapsing. The argument does not use the facet property of F′ or the special form of the collapsing.

**How it was found.** Facets correspond to coarsest regular subdivisions of Δ_{p−1} × Δ_{q−1}, and the maximum number of distinct slices is the number of maximal cells. An exhaustive height scan for 4 × 4 found 54 coarsest subdivisions with 5 cells and 6 with 7 cells. All 60 were certified exactly, as facets of P^{4,4,5} and P^{4,4,7}. The p < q and 3 × 3 scans reproduce the source's Table 1.

**Lean.** The endpoint is `MathDB378395.Main.collapsing_conjecture_false : ¬ MathDB378395.CollapsingConjecture` in `lean-packet/proof/MathDB378395.lean`, together with the explicit witness `exists_noncollapsible_facet`. The module carries all definitions: the margins of real tables, the cone, faces and facets via supporting functionals and span dimension, the fiber-sum collapsing maps, elementary merges and collapsing sequences.

**Fresh replay.** A fresh extraction of `lean-packet/source-only-packet.zip` replays with status PASS:
- strict `-j1 -DwarningAsError=true` build with an empty log, and leanchecker PASS;
- audit of all 134 local declarations, including generated ones: only propext, Classical.choice and Quot.sound, no sorry, axiom, unsafe or partial declarations;
- the sanity supplement, 1 positive harness control, 5 rejected negative controls, and the exact Python diagnostic;
- maximum sampled private RSS 2.16 GB, maximum wall time 12.6 s, inside a systemd scope with MemoryMax=6G.

Receipts are in `lean-packet/fresh-replay-receipts/`. The packet uses the same lean, leanchecker and lake-manifest hashes as the accepted 366371 packet. The certificate checks use `decide +kernel` (kernel reduction, not native code). The cached mathlib oleans are trusted; there was no upstream rebuild.

**Prior art.** Searched only to a bounded depth (see `outputs/web-searches.json`): no refutation and no 4 × 4 × r (r > 4) facet computation found. The registry screen at Omega HEAD f9b5efa07de8 and OpenAI HEAD 4eaee87548250 is path-level only. Novelty is not globally claimed. Remaining: independent fidelity and significance review and root acceptance. The ordinary proof is `lean-packet/PROOF.md`.

## Other dispositions (full detail in `results.json`)

**Known or refuted in the literature (13 IDs).**

| ID | Disposition | Basis |
| --- | --- | --- |
| 377968 | Refuted | Kotschick: infinite-order products of two involutions have stable torsion length 0; independently rederived here |
| 378033 | Refuted | Miller's unexpected local extrema; abstract-level only |
| 378069 | Refuted in source | Hoffmann: the conjecture holds exactly up to rank 8 |
| 378285 | Proved | Andrews et al. 1994 |
| 378465 | Proved in source | Czygrinow–Hurlbert–Kierstead–Trotter, connectivity 2^{2d+3} |
| 378584 | Proved | Cooper–Hyatt 2025, body read; my search agrees for primes up to 19 |
| 378587 | Likely known | p-adic Langlands literature; not re-read in this pass |
| 378637 | Proved | Ellenberg–Gijswijt |
| 378663 | Refuted in source | Kellner's exceptions |
| 378665 | Solved | Stated in the source |
| 378697 | Proved | Eisenbud–Schreyer / Boij–Söderberg |
| 378902 | Proved | DeVos–Goddyn–Mohar Corollary 1.8 (body read); Cao 2006 for two primes; my search agrees |
| 379043 | Proved | Adiprasito et al.; abstract-level only |

**Formulation defect (379012).** The literal statement fails trivially for N = (R/(x₁))² because the β₀ factor is missing; this is direct-sum padding, so it is not credited. The corrected statement is Boij–Söderberg's theorem. The source's own codimension-1 theorem fails on the same example.

**Non-exact (379120).** The claim is an approximate bound, "≈ d²/3".

**Searched, no counterexample.**
- 378740: proved in the literature for s ≤ 9 and s = 11. Screens of 1.42 million configurations (grid subsets plus line-arrangement pools) in the open cases t = 5, r = 2–4 and t = 6 found no violation, using one-sided-sound modular ranks.
- 378162: the n = 2 case is proved outright; 80,000 numerical tests for n = 3–6 found no failure.

**Parked as hard, vague, numerical or heuristic, with no finite mechanism (24 IDs).** 377973, 378034, 378115, 378324, 378371, 378409, 378478, 378479, 378528, 378541, 378542, 378574, 378771, 378797, 378803, 378912, 378923, 378981, 379064, 379065, 379106, 379108, plus 378740 and 378162 from the previous item.

## Provenance and resources

- **Corpus records.** `extracted.json` and `raw/*.jsonl` hold the exact raw lines with newline, chunk and line numbers, and chunk/raw/statement SHA-256s.
- **Sources.** arXiv e-prints for all 35 distinct sources were fetched with HTTP 200, plus prior-art sources, each with a dated receipt in `sources/`. One SFU host returned 403 and was not retried.
- **Omega HEAD.** It advanced to f9b5efa07de8 (2026-11-01T20:06Z, an unrelated Koljančić–Oblak commit). Complete D5 and Problems trees were fetched there; see `outputs/registry-screen.json`.
- **Search coverage.** Per-ID search spaces are in `outputs/search-coverage.json`. Routes and remaining lemmas are in `mathematical-attempts.md`.
- **Resource caps.** Every computation ran under `scripts/limited.py` (2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB). Lean runs used `scripts/limited64.py`, which raises only the address-space limit to 64 GiB (Lean needs a large virtual reservation); RSS, CPU and wall caps are unchanged.
- **Failed runs.** Two single-shot lex-search runs (n = 19 and n = 23) hit the CPU cap; n = 19 was then completed in prefix chunks, and n = 23 is not covered. Two zero-sum runs (n = 15, k = 13 and n = 14, k = 12) hit the cap and are not counted as coverage. One Lean certificate run hit the 12 GiB address-space limit (bad_alloc) before the 64 GiB variant was used. All logs are retained.
- **Lean development modules.** `formal/R73/` holds the development copies; the authoritative packet is `lean-packet/`.
