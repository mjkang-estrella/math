# Failures and disclosures — pi-mathdb-primary-qualified-breadth-r349

1. **Temporary corpus-row extract (deleted).** Early in the session, before the
   no-copy discipline was applied, a working extract of the 50 reserved corpus
   rows was written to `/tmp/reserved-records.json` for reading convenience. It
   was never referenced by any lane payload; it was deleted, and
   `work/build_dispositions.py` re-derives all record metadata strictly by
   reading the corpus chunks in place. No corpus bytes were copied into the
   lane or into any retained artifact. (This mirrors the pre-read-sequence
   disclosure pattern of r347: the extract happened after input verification
   but is delegate-reported, not independently witnessed.)

2. **ems.press not accessed.** The primary source page of 404067
   (OWR 2023/14 p.52) and of the resolved items was not fetched; PDFs were
   obtained from arXiv instead. The interpretation risk this leaves for 404067
   is flagged in proposals.json (objection 1).

3. **Abstract-level evidence only.** The three `publicly_resolved_reported`
   dispositions rest on retained arXiv PDFs and their abstracts; proof bodies
   were not read, and no chronology/subsumption comparison was performed.
   Negative search results are not exhaustive current-registry clearance.

4. **Deferred verifications.** The two planned exact verifications for 404067
   (self-contained m(3) >= 2 witness; m(4) determination) were not executed in
   this lane; they are specified in proposals.json as bounded exact
   computations well within caps.

No compute failures: every guard-wrapped run exited 0 (peak group RSS <= ~30 MiB,
wall < 1 s each). No 403/429/challenge responses encountered (only arXiv and
exa search were contacted).
