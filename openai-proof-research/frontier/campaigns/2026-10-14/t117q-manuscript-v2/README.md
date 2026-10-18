# T117Q manuscript v2

Myeongjin Kang, no affiliation. Author repair implementation only; independent manuscript review remains required. No acceptance, publication or campaign-count decision.

The final 16-page main.pdf is built from main.tex. This revision implements the sole required manuscript-r1 repair M1: the general-metric cardinality bound is credited to Bourgain's 1987 grid theorem and Tomczak-Jaegermann's 1974 cotype theorem through GMN §1.3, which also states GMN Theorem1.2 yields the grid bound. The original two bodies were not read. The JLW/MN chain and verified sqrt(d)/64 deduction remain; it improves grid side to order sqrt(d), while recovering the classical cardinality order. Optional O1 differential commas and O2 build pointers are fixed. All previous proof/contribution/formal limits and R2 corrections remain.

The full all-complex-Hilbert-space, genuine-negative-type, ordered uniform first-pair-average statement with exponent9/2 is unchanged. validation/repair-receipt.json records exact equality of the theorem and proof sections apart from the three punctuation corrections; validation/v1-to-v2.patch exposes every source change. This is author-side preservation checking, not a new proof review. The source pin remains fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Build and inspect

From this directory, using a previously nonexistent output directory:

    python3 -B build.py --output /var/tmp/NEW-T117Q-V2-BUILD --tectonic /path/to/tectonic

The default Tectonic location is /tmp/frontier-typeset/tectonic. The builder copies main.tex outside the packet, uses SOURCE_DATE_EPOCH1792281600, and records compiler identity, PDF identity, text extraction and metadata. Tectonic cache/network support is trusted; this is not hermetic. The final build is clean. All16 final pages were rendered and individually inspected; validation/visual-qa.json binds those renders to the final PDF. One earlier v2 build had an overfull command paragraph and is retained under build-history/v2-build1; the final display-command formatting resolves it.

The unchanged separate t117q-formal-v1/rebuild.py supports --output, --lean and --cache arguments as described in that packet's README. Its31 support and15 control declarations cover finite matrix support only; they do not formalize the full theorem. No Lean rebuild was repeated for this attribution edit.

## Integrity and provenance

Obtain the manifest anchor from the external parent message, then run:

    python3 -B verify.py --anchor EXTERNAL_SHA256
    python3 -B integrity_controls.py --anchor EXTERNAL_SHA256

These unchanged v1 scripts reject altered membership/bytes, links, hardlinks, nonregular files and wrong external anchors. Controls mutate disposable /var/tmp copies only. validation/integrity-controls.json binds the preliminary seal; final-seal controls are replayed externally. Identity is not a mathematical verdict.

input-provenance.json retains v1's selected input identities, all21 copies and9actual source blobs rechecked against the complete13223-entry canonical tree. inputs/t117q-manuscript-review-r1 is an exact copy of the independently sealed repair report. packaging-provenance.json records the v1 and review anchors. v1-history retains prior reading/validation/provenance records explicitly as history. Current personal reading is in reading-limits.md and external-read-inputs.json; earlier author/reviewer reads are not inherited.

Original prose is CC BY4.0 and original code MIT; see LICENSES.md. private/ includes ignored third-party bodies and QA renders and must never be publicly selected. Historic snapshots and copied reports retain their provenance. Public selection for any eventual release must be explicit; this whole local packet is not a public archive. v1 and the pending release preparation were not edited. No stage, commit, upload or nested agent was used.
