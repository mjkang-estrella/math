# T212M manuscript v1 — author preparation

The 19-page article is `public/manuscript.pdf`; its complete LaTeX is in `public/`. It preserves the full prospective target: every nonatomic law on finite nonnegative iid square-lattice weights, almost surely no bigeodesic, with no moment or direction restriction, conditional on the stipulated pinned source and its specified inputs.

This packet is an author manuscript, not a manuscript review or acceptance. `manuscript_review=null`, `accepted=false`, `published=false`, `count_change=0`. Parent adopted the independent proof result and conditional substantial contribution assessment; their exact reports and bounded reading limits are retained under `evidence/`. The independent manuscript gate must assess this exposition and its explicit proof-use mapping. No upload has occurred.

Source212 already pays every finite minimum-of-four second-moment law. Only the infinite-minimum-second-moment class is additional. The theorem scope agrees with the cited DH conjecture for finite-valued laws; this packet does not declare an unconditional conjecture resolution. See `editorial-crosswalk.md` for required attribution corrections and the explicitly generalized kernel statement requiring manuscript rechecking.

## Rebuild

Run from this packet with an installed Tectonic binary and its cached TeX bundle:

```sh
python3 build.py --tectonic /path/to/tectonic --output /var/tmp/t212m-fresh-build
```

The output must not exist. The builder copies only LaTeX into that directory and uses cached resources, untrusted mode and fixed `SOURCE_DATE_EPOCH=1792281600`. It records the compiler hash, source hashes, PDF hash and console log. Two clean builds were byte-identical. The compiler used here is `/tmp/frontier-typeset/tectonic`; the command does not install it or a TeX bundle. Build reproducibility depends on matching compiler/resources. All 19 pages were rendered and visually inspected; receipts are under `validation/`.

## Verification and limits

```sh
python3 verify.py --root . --anchor EXTERNAL_MANIFEST_SHA256 --repository-campaign /absolute/path/to/frontier/campaigns/2026-10-14
```

Supply the external seal separately; do not derive trust from a manifest's own contents. The verifier checks exact payload and directory identities, safe file types, status invariants and the selected frozen/parent evidence bytes. It gives no mathematical verdict. Controls operate only on temporary copies. No write-in-place upstream review drivers are selected.

The frozen Lean package is bound by its manifest and precise coverage record. Its 14 support declarations and 17 controls concern deterministic eventual all-walk minimality under specified finite-change hypotheses. The full theorem is not formalized; no Lean build was repeated for this manuscript. No third-party primary bodies, cached sources or PDFs are included. Source/primary receipts preserve identities and original authorship; their `private/` paths refer to the frozen author packet, not redistributable manuscript payloads.

Original article and original explanatory prose: Myeongjin Kang, CC BY 4.0. Original helper code: MIT. No affiliation is asserted. Copied review/provenance records retain their stated authorship and roles; this license statement does not relicense third-party primary works.
