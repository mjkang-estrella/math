# Reproduction boundaries

All review gates have passed. The archive is r033-fourth-moment-sk-comparison-v1.zip. The separately retained parent acceptance receipt supplies external archive, bundle-manifest, final-gate and release-seal anchors.

The portable verifier checks an archive or clean extraction using externally supplied BUNDLE-MANIFEST and FINAL-GATE SHA256 values. Do not obtain expected anchors from the untrusted package being checked. The assembler rejects a pending review gate. These tools verify exact identities and inventories, not mathematics.

For the scoped Lean build, use a working copy of o217-formal-v1 and its documented rebuild.py command with a locally installed pinned Lean4.34.1 and the pinned dependency cache. The runner builds all own objects afresh and checks types, standard axioms and semantic controls. Historical workspace review verifiers may also require private inputs excluded here; their recorded manifests remain provenance, not a promise that every original private packet is bundled.

For the manuscript, use a working copy and support/build.py with the recorded Tectonic0.17.0 executable and cached TeX resources. SOURCE_DATE_EPOCH fixes the PDF metadata; Poppler renders pages. All final inspected page images must correspond to the final PDF hash. Final release checks reassemble deterministically and rebuild the PDF, comparing it and every page raster with the sealed inspected evidence. They do not claim a new visual review.

Uploads and publication are stopped. Reproduction operates locally.
