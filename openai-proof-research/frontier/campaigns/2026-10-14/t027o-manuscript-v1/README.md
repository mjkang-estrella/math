# T027O manuscript v1

Myeongjin Kang; no affiliation. Prose CC BY4, original code MIT. Full rigorous article for independent manuscript review, not an acceptance or count decision. Frozen r36 remains unchanged. The complete original all-g,r scope is retained.

- Final article: [16-page PDF](output/pdf/article.pdf).
- Portable source and build: [public/](public/README.md), [build.py](public/build.py).
- Exact proof and formal-support boundary: [proof-scope.md](proof-scope.md).
- All proof E1–E6, required credits R1–R4, formal F1–F4: [findings-crosswalk.md](findings-crosswalk.md).
- Actual reading/retrieval limits: [reading-limits.md](reading-limits.md).
- Final render inspection: [inspection/page-inspection.json](inspection/page-inspection.json); all16 page PNGs retained.
- Rebuild evidence: development/build04/build-receipt.json and development/copied-build-final/build-receipt.json; fresh copied-source PDF is byte-identical, recorded in rebuild-receipt.json.

Read-only authentication, with the external manifest SHA256 supplied separately:

    python3 -B verify.py --anchor EXTERNAL_MANIFEST_SHA256
    python3 -B integrity-controls.py --anchor EXTERNAL_MANIFEST_SHA256 --scratch /var/tmp

The second command makes disposable copies and checks expected rejection reasons; it removes its temporary tree. It does not verify the mathematics. Root and ancestor symlinks, hardlinks, FIFOs/nonregular entries, nested manifests, extra empty directories, omitted/extra/changed payloads and self-resealing under the old anchor are rejected. The verifier checks source Git blobs, primary/provenance receipts, exact file/directory inventory, final TeX-to-build source hashes, matching PDFs and every inspected page hash.

The public directory contains only original article/build materials, no private third-party body. All13 canonical non-PDF source027 blobs and15 primary body/extraction files are private and ignored; copying does not imply full reading. Source truth at the declared pin is stipulated. The source's SL_r irreducibility assertion is cited from inside the proof, not its GL_r proposition statement. Rank2, GT/Litt, Pickrell–Xia, Loewy/Mantelos, and the precise BKMS GL_n result are credited. MO pointers are explicitly not input theorems. Global priority is not claimed.

The scoped formal review passed and was adopted by the parent. The independent reviewer adds a derivative bridge in its own separate source. Neither the author support nor that review proves full T027O. All parent adoption records used here are copied with identity receipts in provenance/; their historical counts are not manuscript acceptance.
