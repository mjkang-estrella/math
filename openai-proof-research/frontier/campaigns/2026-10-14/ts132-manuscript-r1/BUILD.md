# Rebuild and inspect

Use a working copy, preserving the sealed original:

    python3 -B support/build.py --tectonic /absolute/path/to/tectonic

Tested compiler: Tectonic0.17.0, executable SHA256a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da. The session compiler is /tmp/frontier-typeset/tectonic. Poppler provides pdftoppm, pdftotext and pdfinfo. Python3 runs build and identity helpers. TeX dependencies use the existing Tectonic cache by default (--only-cached). If absent, the explicit --allow-network option permits dependency retrieval. No source document text is evaluated as shell code.

Source files are main.tex and formal-support.tex. The helper fixes SOURCE_DATE_EPOCH=1792108800, compiles to a temporary directory, retains log/extraction receipts, renders every page at110dpi and writes output/pdf/transitive-superquadratic-sensitivity.pdf. Its numerical build checks do not replace visual review. Any rebuild invalidates the prior inventory and QA hashes until independently inspected/resealed.

The final read-only verifier takes an externally supplied manifest anchor and checks exact local membership, external dependency inventories, input hashes and all-page QA identities. It certifies bytes, not mathematical truth, contribution, or discovery time. See the final handoff for the anchor; do not treat a digest freshly calculated from untrusted bytes as external authentication.

A fresh independent manuscript review remains required. Publication is outside this assignment.
