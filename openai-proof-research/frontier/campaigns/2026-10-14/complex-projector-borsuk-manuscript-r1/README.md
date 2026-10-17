# The Borsuk number of the complex projective plane is nine

Review-ready manuscript by Myeongjin Kang, no affiliation. The main theorem preserves the full frozen B8C scope. It awaits a separate independent manuscript gate. No self-awarded manuscript PASS, count change, or publication is made.

- `output/pdf/complex-projective-plane-borsuk-nine.pdf`: final 11-page manuscript.
- `main.tex`: complete LaTeX source, including bibliography; no BibTeX stage required.
- `response-matrix.md`: prior editorial and contribution comments mapped to manuscript locations.
- `provenance.md`, `formal-support.md`, `input-manifest.json`: exact source/review/formal identities, rights and scope.
- `support/example_10_2_bounds.py`: exact rational AppendixA.2 comparison only; not the main global-cover proof.
- `checks/`: compiler log, PDF text/metadata, exact scalar output, all page PNGs and visual inspection record.

## Build

Rebuild in a working copy of this directory so the sealed reviewed bytes remain intact:

    python -I -B support/build.py --tectonic /path/to/tectonic

Requires Python3, Tectonic and Poppler (`pdftoppm`, `pdftotext`, `pdfinfo`). This build used Tectonic0.17.0 at `/tmp/frontier-typeset/tectonic`, cached TeX packages and SOURCE_DATE_EPOCH=1792108800. `--allow-network` permits missing TeX-package downloads if provisioning a new environment. The script uses this package's temporary directory, removes it afterward, writes the PDF under output/pdf and renders every page under checks/pages. It rejects overfull boxes, unresolved references and rerun warnings. Rebuilding with another toolchain may change PDF bytes; inspect all newly rendered pages before release.

The separate formal package supplies the kernel-checked scalar/algebraic support described in formal-support.md. This manuscript build neither reruns Lean nor claims the full theorem is formalized.

## Integrity

    python -I -B support/verify.py --seal-sha256 EXTERNAL_SEAL_SHA256

Use the detached seal hash supplied in the reviewer's external receipt. The read-only verifier authenticates the manifest before payload parsing, checks exact local membership and bytes, checks the four frozen author/review inventories, and authenticates the separate formal manifest/payload (excluding only its explicitly designated future `.replays` directory). Input hashes and build/visual linkage are checked. It executes no mathematical or author code and changes no files. Integrity is not proof truth or independent manuscript acceptance.

Original prose CC BY4.0; original code MIT. Third-party source bodies remain private in their existing authenticated source packages and are not included in this packet.
