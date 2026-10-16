# Selected inventory

The static allowlist contains 130 files, 743680 bytes. Each file has an exact project-relative destination, SHA256 and length in `allowlist.json`; the frozen copy is under `payload/`. No glob or recursive workspace discovery is used for packaging.

- `staircase-contribution-factory-r1/`: 7 selected files.
- `staircase-formal-review-r1/`: 42 selected files.
- `staircase-formal-v1/`: 18 selected files.
- `staircase-manuscript/`: 48 selected files.
- `staircase-parent/`: 5 selected files.
- `staircase-proof-r1/`: 10 selected files.

The paper selection includes main.tex/references.tex/main.pdf, original licenses/rights, metadata/source map/attribution response/formal-scope, source and historical manifests, the two finite programs and expected complete receipts, reproduction/build/verification utilities and historical compiler/visual-review metadata. Only eight pinned source/README files and their Apache-2.0 LICENSE are added from the source readings. The exact cited I21 note, candidate, candidate rights, upstream pin and source-contract provenance are included. Full page PNGs, preliminary ZIP and build temporaries are excluded.

The proof review includes its full authored nine-file output inventory and manifest, original checker and receipt. The contribution selection includes its six authored output members and manifest; none of external/. The full 18-file author formal package and full 42-file independent formal review package (including frozen author-copy, context/main.tex, accepted sources/checks, three rejected mutation sources/logs, receipts, dependency lock and original verifiers) are included. Parent formal/proof/contribution dispositions and implementation authentications supply the integrated state without editing old records.

All other files are excluded. In particular: every inputs/primary PDF/TXT, contribution external reading copy, catalogue tree/preprints listing, shared index, dependency source tree/cache, tool executable, olean/ilean, Python bytecode, TeX build temporary, preliminary public ZIP and active manuscript-review output. `excluded-inputs.json` records known manifest-referenced omissions, without copying their bytes.

Historical input/output manifests are delivered unmodified as provenance. They can name omitted copyrighted readings, toolchain paths, old counts, earlier pending states and larger experiments. They do not define this bundle's inventory and are not promises that their live-input verification succeeds in isolation. The selected bundle verifier checks all selected files against its exact inventory, checks historical output membership where applicable, and runs the full frozen formal-review verifier in default snapshot mode. It does not claim complete historical-input reproduction. I21's larger diagnostic suite is not a proof premise of this paper and is not reproduced here.

The final bundle additionally selects the top-level release files named by this preparation's output-manifest.json, that manifest itself, and the later actual gate config/disposition/review manifest and selected actual review members. No final-gate files currently exist in this preparation. BUNDLE-MANIFEST.json enumerates the final exact union and excludes itself from self hashing. A separately received archive digest is the external transport integrity check.
