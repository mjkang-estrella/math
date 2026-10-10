# I88 evidence contract

The source pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All pinned statements and lower proof operations are accepted as premises. This record does not verify upstream truth.

Owned domain: the one I88 report plus every file recursively under the I88 source and experiment directories. `seal.json` lists every owned file except itself, with byte size and SHA-256; its own SHA-256 is returned at handoff. No generated output directory, unlisted fixture, or arbitrary path exclusion is allowed. No sealed file is to be changed in place.

`inputs.json` binds immutable snapshots of AGENTS, four ledgers, upstream/tree metadata, and prior I03/I04/I12/I13/I28 reports. Only the four ledger originals may drift. All four had drifted at the successful pre-seal replay; their frozen snapshots passed. I79's finalized two maps and the old catalogue are additional immutable references; the latter is context only and is not the inventory authority. Active I86/I87 artifacts are not dependencies.

The full source-domain manifest references existing I14/I79 bodies, not new copies. The offline verifier checks all 10,373 original Git blobs and the corresponding searchable-body hashes, including every PDF extraction. It checks exact provenance agreement with both I79 maps and complete equality with the full tree. Selected-family and read manifests narrow the mathematical reading claims without narrowing the integrity domain.

All seven corpus query-result files are replayed exactly, including the two failed query designs and their first repair. The verifier recomputes the ordered line records, so it also verifies their multisets. Search noise is not a proof-reading claim. Primary web search outputs and exact request terms are retained separately; only explicitly read primary statements are used.

`preseal-verification.txt` is the successful full preflight using a manifest constructed only in memory; it was produced before any seal existed. A final seal includes that log and all later completed evidence files. The verification program itself has no fetching, writing, repair or resealing path; its finite diagnostic subprocess also only prints. Run it from any directory by its absolute path, or use the command in the report. It emits final results to stdout without creating a new unsealed artifact.

Evidence PASS means artifact/provenance/search/finite-diagnostic consistency only. The author proposes no substantial finding. No independent original-proof verdict, independent contribution verdict, parent acceptance, count increment, commit or publication is implied.
