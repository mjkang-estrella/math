# P3R proof review round 1

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. Third-party source rights retained privately.

`review.md` gives **PASS_FULL_P3R**, no required repairs, for the exact observed candidate and scope hashes. It explicitly answers P1–P5. This is not a final author handoff or a contribution/count decision. The live author paths changed during review; `receipt-after.json` records the discrepancy, and later parent reconciliation is required. All retained reviewed inputs remain fixed.

`source-reading.md` states actual reading extents. `source-verification.json` authenticates 14 pinned source blobs. `input-inventory.json` lists the retained inputs and provenance. `manifest.json` binds exact file/directory membership and output roles, with `seal.json` binding its bytes. The external SHA256 of seal.json is reported to the parent outside this package. These integrity checks do not prove mathematics.

Inspect `verify.py`, then run `python -B verify.py --anchor EXTERNAL_SHA256`. It reads only this package, requires the anchor before parsing the seal or manifest, rejects unlisted entries and symlinks, checks all file bytes, source Git identities and the two fixed candidate hashes, and checks receipt consistency. It does not require future live author files to remain at their old paths. No author or historical program was executed. There are no numerical spectral experiments or formal certificates in this gate.
