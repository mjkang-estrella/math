# Reproduction boundaries

The manuscript review passed with no required findings. Obtain archive, BUNDLE-MANIFEST and FINAL-GATE hashes from the separately trusted parent release receipt. Parent acceptance remains a separate decision.

The portable verify_bundle.py accepts an archive or clean extraction, with --manifest-sha256 and --gate-sha256. assemble.py requires the final adopted independent gate. Private-packet verifiers may require excluded private bodies or workspace-relative inputs; their historical manifests do not promise those omitted files are bundled.

To rebuild the PDF, copy rcs128-manuscript-r1/public to a writable source directory and run python3 -B build.py --output NEW_EXTERNAL_DIRECTORY --tectonic PATH. The build requires Tectonic 0.17.0 and cached TeX resources, uses --only-cached and --untrusted, and fixes SOURCE_DATE_EPOCH. The result is article.pdf. Render with pdftoppm -png -r 110 to compare the 17 page rasters with validation/page-inspection.json. Matching page hashes are reproduction evidence, not a new visual inspection.

For scoped Lean support, copy rcs128-formal-v1 and run python3 -B rebuild.py --output NEW_EXTERNAL_DIRECTORY --lean PATH_TO_PINNED_LEAN --cache PATH_TO_PINNED_DEPENDENCY_PACKAGES. The script checks the compiler and dependency revisions before fresh own-source compilation; its defaults point to the original workspace and must be replaced on another machine. Read the limitations in FORMAL-COVERAGE.md. No dependency downloads or full mathlib rebuild are implied.

release_checks.py tests archive and extraction integrity, deterministic reassembly, refusal of pending or modified gates, symlink/hardlink/special-file rejection, and copied-source PDF/page reproduction. The external release-check receipt records the actual run and its bounds. Uploads remain stopped.
