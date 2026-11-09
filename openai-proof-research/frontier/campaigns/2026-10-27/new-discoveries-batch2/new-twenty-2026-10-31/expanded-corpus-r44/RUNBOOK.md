# Reproduction and evidence map

Run from this lane. All mathematical scripts internally constrain affinity to at most two CPUs, address space to6GiB, and process CPU to90–150 seconds. External wall caps are also required:

```
timeout 120s python diagnostics.py > diagnostics.log 2>&1
timeout 105s python spectral-schur.py > spectral-schur.log 2>&1
timeout 170s python hyperopic.py > hyperopic.log 2>&1
timeout 140s python finalize.py > finalize.log 2>&1
```

`diagnostics.py` requires NumPy. Its dependency-free graph implementation preserves edge lists in `edge_list_repr` (these strings are NOT graph6 encoding). The fixed RNG seed is4401. `spectral-schur.py` uses SymPy1.14.0. `hyperopic.py` uses only the standard library, exhaustively canonicalizes connected graphs through order5, and caps constructed game actions at2,000,000. The game solver is unformalized; no Python result is an accepted theorem.

`extract.py` scans the 20 corpus chunks and writes only this lane's exact40 lines, provenance and readable statements. Its initial run took under a second with2-CPU affinity and60s wall timeout; `finalize.py` subsequently verifies every manifest chunk and raw extraction with explicit memory/CPU/wall bounds. Preserve reservation.json. Do not rerun `fetch.py`, `fetch-more.py` or `registry.py` merely for offline reproduction: their URLs are live, and a rerun can change receipts. Existing downloaded PDF/JSON bytes and source-receipts.json are the dated evidence. No denied-route retry or access bypass was performed.

`fetch.py` used at most two HTTP workers with35s request deadlines and serial pdftotext calls; `fetch-more.py` and `registry.py` use sequential40s deadlines. All enforce two-CPU affinity,6GiB AS and100–180 CPU seconds, plus210–240s external wall bounds. Successful receipts include actual downloaded hashes; no invented hashes. PDF text was produced with `pdftotext -layout`.

`history-search-full.txt` is full rg output for exact numeric ID boundaries plus selected family title phrases, over campaign markdown/results/ledgers (including old copied reports already present, without creating any history copy). `history-id-matches.json` filters exact IDs and excludes this lane. `title-patterns.txt` and `history-title-search.txt` record a second fixed-string, case-insensitive search of all40 exact titles over the same report types. Empty output means only no hits in that bounded search. Administrative reservation/index files were not treated as primary technical reviews. Prior source reports and summaries remain inherited, not newly audited proofs.

`inherited-context.json` retains relevant fields and actual SHA256 hashes of the campaign/batch/first ledgers and prior context. It does not copy history directories. The first ledger hash matches4b2b8556921bb11448e76e0653060ab89d9b2107f3be0338c238ba66038bc385. Mutable ledger hashes are snapshots of administrative context, not immutable mathematics.

`environment.json` and `lean-version.log` record actual binary/package pins. No Lean mathematical process ran; no theorem extraction or axiom audit is represented. Version probe used8GiB AS,20 CPU seconds,25 wall seconds and2-CPU affinity. The first attempted diagnostics import failed because networkx was absent; captured error is retained in diagnostics-initial.log, after which graph utilities were implemented locally. No packages were installed.

`validation.json` binds exact raw provenance and reservation inputs. `artifact-manifest.json` hashes final lane files (except itself). Source scope and remaining proof obligations are in ATTEMPTS.md; dispositions are exactly40 numeric-string keys in results.json.
