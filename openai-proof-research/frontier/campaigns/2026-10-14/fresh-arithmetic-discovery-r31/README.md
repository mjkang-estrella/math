# r31 bounded mathematical screen

Read screen-253.md and reading-limits.md. No target was frozen; no theorem nomination or count change follows. The area/norm calculations exclude a particular geometric normalization, not higher finiteness or abstract stabilizer isomorphism.

Verification, from any byte-identical copied packet:

    python verify.py EXTERNALLY_RECORDED_MANIFEST_SHA256
    python diagnostics.py

The manifest binds every file other than itself and the exact directory list, including private inputs. Its hash and the verifier hash are communicated to the parent outside this packet. The verifier rejects links, nonregular files, unexpected/missing files or directories, nested manifests, and source identity mismatches. controls.json records disposable copied controls against the pre-report snapshot. Running controls.py requires local scratch capacity and does not alter existing payloads; its temporary directory is removed before return. No local self-written seal can substitute for the external anchor.

Public/original files are the Markdown exposition, Python scripts and JSON metadata at packet root. All private/ contents are third-party source/primary bodies or page renderings and must be excluded from Git and releases. No public release is authorized. Original exposition: Myeongjin Kang, no affiliation, CC BY 4.0. Original code: MIT. The parent alone integrates results and changes campaign counts.
