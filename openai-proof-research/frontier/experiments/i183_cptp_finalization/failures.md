# Finalization attempt ledger

All attempts use exclusive names. capture.py snapshots all current owned
Python sources before launching each diagnostic or schema inspection;
it preserves stdout, stderr (including empty files), invocation metadata,
and return-code/runtime receipts. No old artifact was modified.

- `freeze-01`: authenticated and exclusively froze 1,153 strict paths.
- `schema-01` through `schema-08`: successful structured data inspections.
  These inspect retained data only, not graph populations.
- `indexed-01`: all twelve indexed controls passed with facial reconstruction.
- `calibration-01`: failed because C171 C0/N are incidence vectors, not edge
  lists. Corrected the reader, not the source data.
- `calibration-02`: failed because the nonbrace perfect_matchings field is
  a count, not a retained vector family. Fresh complete enumeration now
  verifies that count and exhaustively excludes the prescribed pair.
- `calibration-03`: first-P8 extensions use `[i,j,matching]`, unlike C171's
  dictionary records. Reader now checks both explicit formats.
- `calibration-04`: C171, G6/G10 and first-P8 passed.
- `uniform6-01`: k6 words, omitted edges, actual anchors and both minors passed.
- `adjacent-01`: retained product order is product traversal, not sorted
  incidence order. Comparison now canonicalizes both full families.
- `adjacent-02`: a list-versus-tuple comparison falsely rejected equal basis
  coordinates. Comparison now uses the same exact tuple representation.
- `adjacent-03`: the retained wy field is the three-vector selected basis,
  not every repeated within-state generator. Fresh code now checks that
  actual basis and separately proves equality of the full generated span.
- `adjacent-04`: I177 absorption and I178 complete presentation passed.
- `tail-01`: rejected helper q/v records store traced component words,
  not incidence vectors. Fresh edge-identity tracing now reconstructs
  their full word, cycle and pairing records before comparison.
- `tail-02`: all final seven stages passed, including all 626 reductions.
- `mandatory-01`: complete 23-stage run passed in mandated order after
  adding induced-boundary orientation and actual-old-cycle checks.
- `unit-01`, `incidences-01`, `proof-01`: 88 exact matrix tests, four
  primitive incidence cases, six formal stub attachments, two shore
  orientations and five endpoint partitions passed.
- `verifier-draft-01`: full guarded replay passed, eight live probes
  blocked and authentic-source positive control passed.
- `verifier-draft-02`: finalized seal-link validator passed the same full
  replay plus five in-memory forged control-link rejections. No seal file
  was created by these tests.
- `static-01`: owned Python parsed, JSON parsed, invocation source hashes
  and local report links checked; all passed.
- `verifier-draft-03`: final mathematical scripts passed all 23 stages,
  auxiliary checks, eight live probes, positive source control and five
  seal-link pretests. The additional arc-length assertion leaves the
  deterministic mandatory payload unchanged.

Each failed diagnostic has empty stdout and its full traceback. None is a
mathematical counterexample. Changes remained in this new scope.

Historical limitations remain: the original provider failed with no verdict;
the resumed checkpoint is incomplete and unsealed; its first two failed
freeze sources were not saved. I182's historical resealing and vacuous
forgery probe, and I175's historical context limitation, are not repaired
or concealed by this round.

The final preparation additionally archives exact sources for inventory,
prevalidation, sealing and the final read-only replay before inventory
creation. Prevalidation stdout and empty stderr are generated seal-bound
controls. Inventory/sealing receipts and the final read-only receipt go
to the caller; they do not create unbound post-seal package files.
