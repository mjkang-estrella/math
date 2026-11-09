# Reproduction and dossier map

This is an AI-assisted DRAFT, with zero accepted credit. Root alone accepts it.
All commands below are run from the extracted dossier root, which must remain
inside the assigned manuscript lane. No network is required. No command below
runs Lean, lake, leanchecker, a SAT solver or an ILP solver.

## Verify the supplied dossier

Use `python3 -I scripts/run.py verification-process.json python3 -I scripts/verify.py`
and then `python3 -I scripts/run.py numbers-process.json python3 -I scripts/numbers.py`.
The standard-library scripts independently reconstruct the graph and the
four-weight certificate, verify every label and adjacent pair, check all proof
arithmetic and elimination coefficients, recompute the saved audit statistics,
check the precise raw-line and Lean-archive hashes, and safely extract the
source-only packet into packet-test. They do not execute packet scripts.
Bibliographic numerals, DOI/arXiv/revision identifiers, dates, equation indices
and resource settings are separately classified as metadata or notation;
receipts/numbers.json records their source provenance and a numeral inventory.
The degree counts and all substantive numerical claims are recomputed.

The copied Lean packet is source-only.zip, SHA256
9b269351bf3dddcfd3e2c98e00ce50c60b9a8cf4edbb979011658c312e386d12.
Do not rewrite or repackage this ZIP. Its source and bundled instructions remain
byte-identical. In particular the archive's own replay instructions are archival
material; this manuscript task does not authorize executing them.
The extracted Antimagic.lean is compared directly to the discovery tar member;
AntimagicBasics.lean is checked against the accepted common-definition hash.

## Rebuild the editable manuscript and PDF

Run these sequentially, in the foreground:

```
python3 -I scripts/run.py author-process.json python3 -I scripts/author.py
python3 -I scripts/run.py numbers-process.json python3 -I scripts/numbers.py
python3 -I scripts/run.py source-render-process.json python3 -I scripts/render.py
XDG_CACHE_HOME="$PWD/tmp/cache" XDG_CONFIG_HOME="$PWD/tmp/config" XDG_DATA_HOME="$PWD/tmp/data" python3 -I scripts/run.py pdf-process.json libreoffice -env:UserInstallation="file://$PWD/tmp/lo-profile" --headless --convert-to pdf --outdir "$PWD" paper.fodt
python3 -I scripts/run.py pages-process.json pdftoppm -scale-to 1500 -png paper.pdf qa/page
python3 -I scripts/run.py pdf-text-process.json pdftotext -bbox-layout paper.pdf qa/text.html
```

Dependencies used here: system Python, LibreOffice, Poppler and system fonts
Liberation Serif, Liberation Mono and Noto Sans Math. ReportLab was unavailable;
no package was installed. render.py uses only the Python standard library to
write editable Flat ODF. paper.fodt is the document source; paper-content.json
and scripts/author.py supply editable prose. paper.md is the readable text
source and PROOF.md is the complete proof and certificate excerpt.
LibreOffice inserts export timestamps: binary-identical regenerated PDFs are
not promised. The supplied PDF's exact bytes are bound by the manifest.
Review all rendered pages after regeneration; a prior QA receipt is valid only
for its recorded PDF and image hashes.

## Evidence, limits and verification attribution

The exact MathDB line, including its final newline, is
`evidence/expanded-corpus-r159/raw/365453.jsonl`; its SHA256 is
 d0b1fc3125ecb4ec6e0e9bd289336635516fdfb00094e469d1b4867529b2f74d.
The source DOI and author names are verified in the cached publisher body.
The dossier preserves source PDFs, text, retrieval receipts, the independent
review, its bounded registry/citing coverage, the later publisher-reprint
side check, strict formalization replay logs and metadata audit.

Root's replay-result.json and registry-refresh.json were present at final
manuscript preparation and are copied under evidence/joinla-parent-final-r1.
Root reports PASS for the literal endpoint's fresh replay. Its registry screen
is path-based and bounded. The worker did not independently rerun Lean.
The producer audit counts 201 local declarations; root's separate audit reports
187. These are separately reported outputs, not silently interchangeable counts.
Only propext, Classical.choice and Quot.sound occur in the saved endpoint axiom
report. Upstream precompiled mathlib remains trusted. Exact chi_la = 4 is an
ordinary checked certificate, not a claimed Lean endpoint.

The resource wrapper sets MALLOC_ARENA_MAX=2, lane-local temporary directories,
at most two allowed CPUs, CPU 120 seconds and wall 140 seconds. It samples
process-group RSS every 0.1 seconds, kills above 6 GiB, and imposes an address
space cap no higher than the inherited hard limit. It waits for and reaps its
child. One heavy process runs at a time. Run it using python3 -I. No jobs remain
at handback. Initial read-only shell operations were brief; the numeric, PDF and
packaging processes use the saved resource wrapper receipts.

Development issues are disclosed: an initial wrapper setup attempted an
address-space limit above its inherited hard cap and was corrected to retain
that cap; an attempted ReportLab import failed because it was absent. The first
PDF review caught an overflowing union symbol and uneven table layout, which
were corrected before the final render. Successful final receipts supersede
those attempts; no claim of retaining full development diagnostic logs is made.

## Hashes and archives

inputs-before.json and inputs-after.json bind every frozen file in all three
input lanes, plus the brief, launch metadata and root ruling. The baseline was
taken after the mandatory initial instruction/source reads and before dossier
production; nothing in those input lanes was written. Parent reports are bound
separately before copying and after finalization. New parent-lane working files
are not frozen inputs and are not modified here.

MANIFEST.sha256 binds deliverable files, including receipts and the PDF. It
excludes itself, the final dossier ZIP, the outer ARCHIVES.sha256 and its own
post-packaging archive receipt; tmp and packet-test are reproducible working
outputs and are excluded. The full-dossier ZIP contains the manifest and all
listed deliverables. ARCHIVES.sha256 externally binds both ZIPs and the internal
manifest. receipts/dossier-zip.json verifies ZIP CRCs, safe relative member names
and byte equality to each member's supplied manifest digest without executing
any contents. The archive does not include its own outer receipt.
