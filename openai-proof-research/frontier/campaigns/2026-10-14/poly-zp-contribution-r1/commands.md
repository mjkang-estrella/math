# Command and evidence record

All relative paths below use root `/home/mj-kang/Documents/Dev/math/openai-proof-research`. The owned path is `frontier/campaigns/2026-10-14/poly-zp-contribution-r1`. Tool transcript contains the complete exploratory read calls; this file records consequential commands and replay receipts, including reading boundaries. No commands staged or committed anything, sent external messages, or changed author files.

The first local read after discovery omitted the workdir and returned `cat: AGENTS.md: No such file or directory`; it made no edits. All subsequent repository reads supplied the root workdir.

## Frozen package authentication

Actual successful commands:

```sh
sha256sum frontier/campaigns/2026-10-14/fresh-structural-discovery-r3/candidate.md frontier/campaigns/2026-10-14/fresh-structural-discovery-r3/seal.json
python3 -B frontier/campaigns/2026-10-14/fresh-structural-discovery-r3/verify.py
```

Candidate SHA256: `e3f4c65e5eb0f35e9d19090e0ba897b27219a223795a0569319a3114cb3babcc`.
Seal SHA256: `75df70d930c3ccd57287e76a082dab1885bb844b0691132201ce2d4a199684e4`.
Verifier stdout is preserved exactly in `candidate-verification.json`: PASS, 79 inputs / 12 outputs / 39 pinned Git blobs, receipt SHA256 `fa29613888a882122bfb65afbc7f0410a50c1b93b711361d06e5c8c4f6a68e32`, writes 0, network false. The command was repeated before snapshot creation and its stdout captured in memory, then written only to the owned review directory.

A Python `shutil.copytree` copied the complete frozen directory to `inputs/private/frozen-candidate`; `shutil.copy2` copied context AGENTS/upstream/catalogue/tree/campaign/ledger/finding records into `inputs/private/context`. Original manifests and seal are byte-identical. Unused author alternatives remain retained and authenticated, not newly claimed as read.

## Primary retrieval and extraction

The actual curl commands used `-L --fail --max-time 60` for Frankel and `-L --fail --max-time 45` for the other PDFs, writing only these destinations:

```sh
curl -L --fail --max-time 60 -o frontier/campaigns/2026-10-14/poly-zp-contribution-r1/inputs/private/literature/upenn-dissertation.pdf https://repository.upenn.edu/bitstreams/06a689f2-8398-4072-8b8b-1e398d8986ce/download
curl -L --fail --max-time 45 -o frontier/campaigns/2026-10-14/poly-zp-contribution-r1/inputs/private/literature/krattenthaler-mueller-1412.7014.pdf https://arxiv.org/pdf/1412.7014
curl -L --fail --max-time 45 -o frontier/campaigns/2026-10-14/poly-zp-contribution-r1/inputs/private/literature/mueller-schlage-puchta-2005.pdf https://nyjm.albany.edu/j/2005/11-11p.pdf
curl -L --fail --max-time 45 -o frontier/campaigns/2026-10-14/poly-zp-contribution-r1/inputs/private/literature/solomon-1969.pdf https://link.springer.com/content/pdf/10.1007/BF01899292.pdf
```

All four direct retrievals succeeded; each PDF's title was checked. Actual SHA256/byte lengths are in `retrieval-literature.json` and inputs-manifest.json. The arXiv URL resolved to a PDF marked v2, 2 Aug 2015; the bytes, rather than an assumed immutable unversioned URL, are the retained evidence.

Each PDF was extracted with `pdftotext -layout PDF TXT`, replacing the `.pdf` extension by `.txt` in the same owned literature directory. No inherited PDF or extraction was overwritten.

Selected PDF pages were rendered with `pdftoppm`, `-scale-to 1500`, `-png`, and these exact page settings: Frankel `-f 30 -l 30 -singlefile`, `-f 32 -l 33`; Solomon `-f 1 -l 1 -singlefile`; inherited GRV `-f 6 -l 6 -singlefile`. Outputs are in `inputs/private/rendered`. Every one of these five PNGs was inspected with the image-view tool. They confirm the theorem/proof typography and the GRV Euler-product formulas, not full-document visual QA.

## Reading and companion screen

Full `cat` reads: AGENTS.md; upstream.json; candidate.md; source-contracts.json; README.md; provenance.md; literature.md; verify.py; checks.py; retrieval-upstream.json; retrieval-literature.json; source family introduction, sections 04/05 and bibliography; Kisilevsky paper text; campaign and TWENTY ledger. Some early outputs were truncated, so the substantive interfaces were reread in focused chunks. Read boundaries, including repeated repair reads, are in read-extents.json.

Primary focused text reads included:

```sh
sed -n '1,190p' .../gordon-rodriguez-villegas-1105.6066v1.txt
sed -n '190,350p' .../gordon-rodriguez-villegas-1105.6066v1.txt
sed -n '340,400p' .../gordon-rodriguez-villegas-1105.6066v1.txt
sed -n '1410,1500p' .../tamanoi-2001.txt
sed -n '1880,2120p' .../tamanoi-2003.txt
sed -n '1195,1520p' .../upenn-dissertation.txt
sed -n '1520,1590p' .../upenn-dissertation.txt
sed -n '1,230p' .../solomon-1969.txt
sed -n '230,390p' .../solomon-1969.txt
sed -n '1,200p' .../mueller-schlage-puchta-2005.txt
sed -n '1,270p' .../krattenthaler-mueller-1412.7014.txt
sed -n '1380,1430p' .../krattenthaler-mueller-1412.7014.txt
sed -n '1530,1580p' .../krattenthaler-mueller-1412.7014.txt
sed -n '1660,1845p' .../krattenthaler-mueller-1412.7014.txt
sed -n '1710,1780p' .../krattenthaler-mueller-1412.7014.txt
```

Here `...` in this read log abbreviates the exact private literature directory specified in read-extents.json; it is not intended as executable shell syntax. The inherited files were read from the original frozen candidate before copying; new files from this review directory. `rg -n` found theorem labels/terms before these reads. The unused source sections 02/03/06/07 were searched with `a_j|subgroup|congruen|poly-|Z_p`; their complete proofs are not claimed read.

A Python JSON parse of sources/preprints-tree.json reported 13,223 entries and `truncated: false`, searched `Cyclic-Length`, `profinite`, `Profinite`, `Subgroup`, `subgroup`, and displayed the complete family-314 path set. The catalogue's complete family-314 entry was read. This is a bounded path/term companion screen, not reading the entire catalogue or every preprint. Accepted R006/R008-R022 opening/exact-theorem sections and current R023-R026 scopes were read; no group-count duplication was identified there. Their hashes are inventoried; this absence is not a substantiality argument.

## Independent comparison arithmetic

Actual command:

```sh
python3 -B frontier/campaigns/2026-10-14/poly-zp-contribution-r1/comparison_checks.py > frontier/campaigns/2026-10-14/poly-zp-contribution-r1/comparison-receipt.json
```

This first authoring command created a new own receipt; it did not overwrite or regenerate any candidate receipt. PASS: 34 twisted and 62 direct finite subgroups; actual counts 1,3,11 versus 1,7,19 at h=0,1,2; differences 0,-4,-8; 384 synthetic single-orbit cutoff controls. The code does not import the candidate and writes nothing itself.

## Review verification

After all prose, read metadata, code and receipts were finalized, a Python inventory step read every input/output byte, wrote the two manifests, and wrote seal.json binding those immutable manifests. Manifest/seal metadata is excluded from recursive self-inventory. This is initial sealing of the new review only; the candidate's manifests, receipt and seal were never repaired or rewritten.

Run from the owned directory:

```sh
python3 -B verify.py
```

It authenticates all manifests/files/receipts first, checks the original detached anchors, executes the original verifier against its private snapshot under write/network/process audit guards, and replays the independent checks in memory. Final stdout is returned in the tool transcript and the final handoff; the verifier creates no receipt file. Its PASS establishes authentication and finite support only.

The first assembly of this new review inventory failed the verifier's sorted-unique path assertion: Python Path ordering did not equal lexical ordering of the serialized relative path strings. No replay had begun. The assembly was corrected to sort the entries explicitly by `entry['path']`, and the review manifest/seal metadata was finalized again. No input bytes, original candidate metadata, or stored receipt was changed or regenerated. The discarded preliminary review seal is not a trust anchor; use only the final detached hash in the handoff.
