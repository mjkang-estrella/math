# Reproduction boundaries

This preparation remains gated until the final independent manuscript review is adopted. No final archive anchors are claimed here. Once assembled, expected archive, BUNDLE-MANIFEST and FINAL-GATE hashes must come from a separately trusted parent receipt, not from the package under test.

The portable verify_bundle.py checks an archive or clean extraction using --manifest-sha256 and --gate-sha256. assemble.py rejects a pending gate. Original private-packet verifiers may require excluded private source bodies and workspace-relative inputs; their manifests are retained for provenance, not a claim that the full private workspace is bundled.

For Lean use a working copy of agm063-formal-v1 with its documented rebuild.py command, installed pinned Lean 4.34.1 and the explicit pinned dependency cache. Own objects are built afresh. For the PDF use a working copy of agm063-manuscript-r1 and package-root build.py --tectonic PATH with cached TeX resources. SOURCE_DATE_EPOCH fixes PDF metadata. Poppler renders every page. Final release controls reassemble byte-identically and rebuild the PDF and compare all page rasters with sealed visual evidence; this comparison is not a new visual inspection.

Reproduction is local. Uploads and publication remain stopped.
