# expanded-corpus-r88: summary (Claude Opus 5.5 investigator)

## Outcome

No candidate. No Lean packet. Zero claimed credit.

* All 20 reserved IDs are dispositioned in `results.json`: 7 are known in the literature and excluded, and 13 are parked as open with no candidate.
* No full-scope proof or counterexample survived, so no Lean endpoint was attempted and no `lean/` packet exists.

The campaign count stays as stated in TASK.txt; this lane changes nothing.

## Provenance

* `scripts/extract.py` is adapted from r59, with `rg` replaced by `grep`.
* `extracted.json` and `raw/*.jsonl` preserve the exact raw corpus lines (with newline), the one-based line number, and the chunk, raw-line and statement SHA-256 hashes for every ID.
* `history-matches.txt` holds the ID/title search over the frontier tree's prose and review/result/ledger/disposition/integration JSON. It matched only the ledger's reservation lines and unrelated hash-substring collisions.
* A family-keyword screen (sum-dominant, generalized Petersen, thrackle, Goldberg–Seymour, difference index, cyclic matroid, spectral containment, access structure, binomial edge ideal) found no prior lane work on these IDs.
* Source receipts (URL, UTC, status, SHA-256, bytes) are in `sources/*.receipt.json`. Abstracts and PDFs came from export.arxiv.org and arxiv.org, the Kumar–Mohan–Pandey paper from math.colgate.edu, and the graph catalogues from users.cecs.anu.edu.au.
  * graph10c.g6.gz was fetched with resumed curl; SHA-256 is ddabd151…d56a and `gzip -t` passes.
  * Meringer's regular-graph site returned 403. It was not retried.
* Registries (`outputs/registry-screen.json`), checked through GitHub `/commits/HEAD` only:
  * openai/math HEAD is 4eaee875… (unchanged).
  * Omega HEAD is now 0ef26ad5… (changed from 6e37b782…). No new tree listing was fetched because no candidate needs clearance.
  * A path screen of the cached preprint listing found nothing relevant.

## Dispositions

**Known in the literature (excluded):**

* 341752: proved by Gowers–Green–Manners–Tao (2311.05762, 2404.02244).
* 341753: counterexample in the source.
* 350410: disproved in the source (Haslegrave).
* 351476: proved by Altman (2210.17493, Corollary 1.4; Forum Math. Sigma 2025).
* 353123: counterexample in the source.
* 354292: counterexample in the source.
* 355966: Nambi–Kumar (2406.05960) prove trees and refute some unicyclic graphs.

**Open, parked after literature reading only:**

* 343949: Aharoni–Berger-type rainbow matching.
* 343968: the MathDB "disproved" parser label is wrong. Csirmaz refutes only the almost-perfect analogue, and the source says the original problem "remained unsolved".
* 344911, 346674, 352298 and 352675: analytic, geometric or infinite problems.
* 354889: the bounded-width version is still open per Hollom's Question 3.1. His counterexample to the FAC version has width ℵ0.

**Open, with sustained computational routes (all negative):**

* **345244 (hypergroup conjecture, strongest route).**
  * New ordinary lemma: under (S1) and (S2), the pointed graph produces a hypergroup if and only if the quotient matrices of the distance partition commute. So the conjecture holds when the eccentricity of v0 is at most 2, and every counterexample is non-vertex-transitive with eccentricity at least 3.
  * Searches: all connected graphs up to 10 vertices (exhaustive), a validated layered generator (complete for seven (n, r) cases including all cubic graphs on 18 vertices in BFS-layered form; sharded or partial up to n = 20), and bi-circulants with m ≤ 15 (complete).
  * Many non-distance-regular (S1)+(S2) pointed graphs were found; all produce hypergroups.
* **353625 (retract images of generalized Petersen graphs).**
  * Exact endomorphism-image enumeration for every non-core non-bipartite G(n,k) with n ≤ 40, except the G(3m,m) family and 7 cases, which hit the time or CPU caps.
  * An independent subset method for n ≤ 11 reproduces the source's G(8,3) bipartite counterexample. Prisms are proved directly.
  * No non-retract image was found.
* **353943 (orderable binary matroids).** Exhaustive for rank ≤ 6: every 3-connected orderable binary matroid of rank ≤ 6 is graphic. Rank 6 gives 104 classes without a spanning circuit, all graphic.
* **353422 (defective Goldberg–Seymour, odd d).** Exact ILP search over multigraphs with up to 5 vertices, within the stated multiplicity bounds. No counterexample. A 2026 follow-up (Chen–Fiujlaali 2608.00791) still treats it as open.
* **342072 (two-AP sum-dominance).** Reduced by Chu (2020) and Kumar–Mohan–Pandey (Integers 2026) to two residual cases. 2.0M general and 5.1M residual-case unions were searched, with no sum-dominant set.
* **353070 (quadratic spectral containment).** Random and adversarial numerical search for n ≤ 5 found no violation.

Exact search spaces, remaining lemmas and logs are listed per ID in `results.json` and in `mathematical-attempts.md`.

## Files

* Statements: `extracted.json`, `raw/`, `history-matches.txt`.
* Results and notes: `results.json`, `mathematical-attempts.md`.
* Code: `scripts/` (every search, self-test and builder).
* Logs: `logs/` (full logs plus a resource receipt for each capped run).
* Outputs: `outputs/` (summaries, self-tests, checkpoints, registry screen).
* Sources: `sources/` (receipts and bodies).

## Limits

* Every enumeration is a bounded diagnostic, not a proof.
* The lemmas in `mathematical-attempts.md` are ordinary arguments without Lean verification or independent review.
* Resource caps came from `scripts/limited.py`: 2 CPUs, 120 s CPU, 140 s wall, and a sampled 6 GiB RSS limit. They are not cgroup guarantees. Several runs hit the CPU cap and are labelled incomplete.
* No background job is left running at handback.
