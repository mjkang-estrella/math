# Reproduce the manuscript

Use an unsealed working copy:

    python3 -B support/build.py --tectonic /absolute/path/to/tectonic

Tested Tectonic0.17.0 at /tmp/frontier-typeset/tectonic, executable SHA256a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da. The default uses its existing cache with --only-cached. An empty installation can explicitly use --allow-network to fetch TeX dependencies. Poppler pdftoppm, pdftotext and pdfinfo are required. Python3 standard library runs the build/integrity helpers. Rebuilding writes only within this working copy; it invalidates its earlier seal and visual hashes until checked anew.

The two typesetting inputs are main.tex and formal-support.tex. SOURCE_DATE_EPOCH=1792108800 fixes PDF timestamps. Output is output/pdf/continuum-coulomb-qma.pdf; every page is rendered under checks/pages. Final visual review records exact PDF/page hashes, separately from compiler warnings and extracted text. No private primary source is needed for typesetting.

The independent manuscript gate and parent publication decision remain outside this implementation.
