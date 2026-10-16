# Exact selected inventory and hash graph

`allowlist.json` has **184** exact project-relative records (path, SHA256, bytes). It selects existing material without copying it into this directory. `outputs.json` authenticates this edition's machinery and documentation, excluding itself. `inputs.json` records **229** actual authenticated preparation inputs, including the complete frozen old release and excluded historical dependencies; it is not a bundle membership list. No active round-2 review input is present.

The selected historical/corrected groups are:

- Corrected edition: 58 files (57 output-manifest members plus that manifest), including TeX, preserved PDF, nineteen QA renders, full correction diff, response, source maps/sections, licenses, validation and build/verification sources.
- Original manuscript: 28 files, including original TeX/PDF, its 46-output manifest and input manifest, sources, licenses, validation and textual evidence. Its nineteen page PNGs are omitted.
- Original manuscript review: 5 files (four actual `outputs` members plus its manifest). These include review, 12-control program/receipt and 50-input authentication; they bind only the original paper.
- Formal author support: 13 files; independent formal review: 22 files, retaining typed audit, coverage, four source mutations, logs and provenance. No Lean compiled binary/cache.
- Repaired proof: 17 files; original proof review: 2; proof-round-2: 11; contribution review: 4; initial candidate/provenance: 5.
- Historical parent dispositions/authentications: 11. They supply historical context and do not substitute for a new v2 final disposition.
- Four antecedent experiment/iteration records, campaign publication metadata, repository research/publication rules and upstream pin.

The two PDFs are distinct evidence. Small duplicate textual controls are retained to keep historical dependencies legible. Original PNGs are deliberately omitted; corrected PNGs are primary QA evidence. The old release itself is not selected as another full package: its exact source records live in this edition's preparation provenance and inputs.

Hash graph (no self-reference): `outputs.json` → each v2 file except `outputs.json`; `allowlist.json` → 184 selected external files. `outputs.json` includes `allowlist.json`, `inputs.json`, the pending gate and preparation receipts. No selected external file is edited to point back at this release. The future bundle manifest hashes both manifests and all selected files but never itself. The future actual parent disposition binds paper/review/identity; the config hashes the disposition. Neither parent record points to a hash of the eventual bundle. An optional external bundle-manifest hash anchors extraction verification.

`implementation-provenance.json` authenticates the reused Lean rebuild program and receipt against their exact old-release sources and lists the complete old release baseline. `preparation-checks.json` reports actual finite/mutation results. Preparation receipts do not hash themselves, the final output manifest or an archive containing themselves. ZIP determinism is checked by byte equality between two disposable preparation archives; no archive hash is presented as a final publication hash.

Exact hashes and byte lengths are machine-readable in these manifests. Do not replace them with dynamically expanded globs. `excluded-inputs.json` records omitted dependencies per historical input manifest and how to restore them. Final review files are admitted only through the actual authenticated v2 parent gate; no wildcard selects the active review directory.
