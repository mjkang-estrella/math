# Reproduce and authenticate the manuscript

The final output manifest seals this manuscript for independent manuscript review. The adopted scoped formal-audit identity is in dependency-anchors.json. The full human mathematical scope is unchanged.

Authenticate a sealed copy read-only with an externally supplied manifest SHA-256:

    python3 -B verify.py --anchor EXTERNALLY_SUPPLIED_SHA256

Do not obtain that trusted anchor from the package being authenticated. The verifier checks exact files/directories, hashes, build/source/PDF/page bindings and recorded scope. It does not compile Lean, prove the human theorem, or constitute independent manuscript review.

To rebuild, use a working copy; rebuilding changes local evidence:

    python3 -B support/build.py --tectonic /absolute/path/to/tectonic

The tested compiler is Tectonic 0.17.0 with SHA-256 a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da. The build sets SOURCE_DATE_EPOCH=1792195200 and uses cached TeX resources. It writes output/pdf/fourth-moment-sk-comparison.pdf, retains compiler/text/PDF metadata and renders every page at 110 dpi. Python 3 and Poppler pdftoppm, pdftotext and pdfinfo are required. No bibliography processor is needed. An explicit --allow-network option may populate missing TeX resources in a new environment; recorded builds use no network.

A visual receipt is valid only for its exact PDF and rendered page-image hashes. The final two builds and every page image must agree before sealing. Rebuilding is separate from the independent manuscript audit which follows the final seal.

Third-party primary/source bodies remain outside this payload as private inputs. Exact citations and read extents are metadata, not a redistribution of those bodies. Original prose is CC BY 4.0, original code MIT; Myeongjin Kang, no affiliation. No upload is authorized or performed.
