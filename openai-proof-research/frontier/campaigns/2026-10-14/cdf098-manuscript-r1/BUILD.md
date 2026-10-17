# Build and verify

The publication artifact is the nine-page PDF under output/pdf. Source is main.tex plus formal-support.tex. No bibliography processor or network call is required once the Tectonic bundle is cached. Tested compiler: Tectonic 0.17.0; Poppler supplies pdftoppm, pdftotext and pdfinfo. Python 3 runs the helpers. No shell evaluation of document text is used.

Rebuild a **working copy** of this directory, preserving the sealed original:

```sh
python3 -I support/build.py --tectonic /absolute/path/to/tectonic
```

The script sets SOURCE_DATE_EPOCH=1792108800, compiles with --only-cached, retains the compiler/log receipts, renders every PDF page at 110 dpi, extracts text, records hashes and removes temporary build files. `--allow-network` is an explicit optional alternative for obtaining missing TeX dependencies. A rebuild changes local build evidence and invalidates the old package seal; the old visual-review record must not be reused without checking the rebuilt pages. Main.pdf is renamed to the stable descriptive output filename. There are no third-party source bodies in this package.

Read-only identity verification, in the repository arrangement with its three frozen upstream packets and cdf098-formal-v1:

```sh
python3 -I support/verify.py --seal-sha256 EXTERNALLY_SUPPLIED_SEAL_SHA256
```

Use the seal hash delivered outside this directory, not a freshly calculated hash treated as its own authority. The verifier rejects mismatched anchors, noncanonical paths, links, special files, duplicate JSON keys, missing/extra files or directories, changed payloads, source/QA mismatches and wrong external dependencies. It rechecks the two pinned text Git blobs, three dependency inventories, formal package and explicit input hashes. The formal package's documented .replays subtree is the sole external inventory exception and is not trusted as evidence. No mathematical program, external verifier or subprocess is executed. An audit hook prohibits writes, process execution and network access.

The verifier certifies identity only. The mathematical source premise, prior independent verdicts, formal scope and still-required independent manuscript gate remain distinct. The final visual review records each of the nine actual rendered pages. Two underfull-box notices are harmless spacing diagnostics; all final pages were inspected, with no clipped/overlapping text or missing glyphs. No overfull box, undefined reference, or rerun request remains.
