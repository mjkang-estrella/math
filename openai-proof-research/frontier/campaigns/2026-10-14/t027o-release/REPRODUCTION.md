# Reproduction instructions

The manuscript review is pending. No release archive or final acceptance is asserted by these instructions. Once assembled, obtain the archive, BUNDLE-MANIFEST and FINAL-GATE hashes from the separately trusted parent release receipt. The portable verify_bundle.py accepts an archive or clean extraction with --manifest-sha256 and --gate-sha256. It checks exact bytes and the adopted gate bindings; it does not judge mathematics.

The selected files retain their paths under frontier/campaigns/2026-10-14. Private-packet verifiers may require excluded private inputs. Historical packet manifests therefore do not promise that every file they list is portable. The release's BUNDLE-MANIFEST is the inventory of the actual archive.

To reproduce the PDF, copy t027o-manuscript-v1/public to a working source directory, preserving sections/, and run:

    python3 -B build.py --tectonic /path/to/tectonic --output /absolute/NEW/output-directory

The build requires Tectonic 0.17.0 and its previously cached TeX resources. It uses --only-cached and --untrusted, SOURCE_DATE_EPOCH=1792281600 and TZ=UTC. The new output must be outside the source directory. The reviewed candidate PDF has SHA256 84d08097231e89cbcb5a0341cb044676568b2f0f03ee70e2e63b716bcf278cb9 and 16 pages. Render it with pdftoppm -png -r 110 and compare against t027o-manuscript-v1/inspection/page-inspection.json. Matching image hashes reproduce previously inspected pages; they are not an additional visual inspection.

To rebuild the author's scoped support from a copied t027o-formal-v1 directory, run:

    GIT_OPTIONAL_LOCKS=0 python3 -B rebuild.py --output /absolute/NEW/build-directory --lean /path/to/pinned/lean --cache /path/to/pinned/dependency/packages

To include the independent reviewer's additional derivative bridge and controls, use build_review.py from this release directory or the root of its extracted archive, with the same three arguments. This parent-authored adapter authenticates the frozen reviewer builder and source, then points its input to the copied formal package. The frozen reviewer builder otherwise retains its original absolute input path; invoking it directly from another location is not a portable rebuild. The adapter changes the input location, not the Lean sources, declarations, pins or axiom checks.

Both builds trust the pinned compiler and dependency objects described in FORMAL-COVERAGE.md. They compile the project modules afresh and do not download or rebuild mathlib. release_checks.py will verify archive/extraction identity, deterministic reassembly, refusal of modified gates, filesystem node controls, and copied-source PDF/page reproduction after the independent manuscript gate is adopted. Its actual execution belongs in the later parent release receipt.
