# Audit activity and retained findings

All work took place in `/home/mj-kang/Documents/Dev/math/factoring-research`.
Writes are limited to `research/findings/W032-sweep-assay-audit.md` and this
evidence directory. This is the independent assay review requested in brief.txt.

1. Read governing instructions, protocol context and the file inventory.
   The initial combined README/SPECIFICATION/STATE retrieval truncated STATE;
   a later bounded read supplies its coordination excerpt. No full STATE read
   is claimed or needed to change the explicit assignment.
2. Preserved the complete user brief and used `freeze_inputs.py` once to copy
   and hash 51 inputs, including all original assay evidence. Snapshot
   construction is byte copying and hashing only.
3. Read all three original Python sources in full, the full report/protocol,
   frozen mathematical targets and accepted review reports, METER/config,
   manifests and administrative records. No original script was imported or
   executed. Read-scope.json records partial contextual reads accurately.
4. Wrote and ran `inspect_records.py` once. It performed only byte-integrity,
   JSON parsing, record counts/links, stored-width metadata and interval
   coverage inspection. It did not recompute prime generation, coefficients,
   powers, gcds, inverses, quotient values, thresholds, ties or controls.
   All 129 results remain in integrity-and-structure.json. Three terminal
   grouping checks failed; no result file was replaced or suppressed.
5. Read the source cause and wrote/ran `terminal_attribution.py` once to
   inspect those same stored terminal records. It found outer group=17 for
   all three terminals, while nested result.b=9/13/17 and every nested object
   exactly equals status. The first two outer labels are defective. This
   explains the three initial check failures without changing originals,
   correcting the original meter, or rerunning numerical work.
6. Wrote the audit report accepting two finite negatives with that journal
   caveat. The b=17 setup stop stays censored; no third candidate result exists.
   Atomic multi-event ties and zero-net merging were only source-inspected.
   No accounting undercharge or mathematical implementation defect was found;
   arithmetic-event totals and finite probability/outcome claims reconcile.
7. `seal_audit.py` checks snapshot stability, records live-input drift without
   overwriting snapshots, and seals the report plus every evidence payload.
   Exclusions are only this directory's own delivery manifest and terminal
   sidecar; nested original manifests/sidecars remain sealed payloads.
   An external `sha256sum` call supplies the terminal anchor. No edits follow.

No project checks, candidate experiments, numerical replay, extra controls,
installs, commits, delegation, shared code, Lean, STATE or registry edits were
performed. The source of the assay was never repaired. Parent construction,
the independent arrangement review, and `scripts/check.sh` remain parent-owned.
