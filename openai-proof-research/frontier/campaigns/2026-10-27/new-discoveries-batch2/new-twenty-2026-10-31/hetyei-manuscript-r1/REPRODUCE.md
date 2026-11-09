# Reproduce the manuscript dossier

Run from this lane directory. No network or Python third-party packages are needed. Dependencies: python3 standard library, groff with tbl/grops, Ghostscript ps2pdf, Poppler pdfinfo/pdftoppm/pdftotext. All outputs and scratch files stay here. Do not run the Lean packet under the manuscript task's restrictions.

The launcher scripts/capped.py sets a two-CPU affinity, RLIMIT_CPU=120 seconds, 140-second wall limit, 6 GiB sampled process-group RSS ceiling, an additional 6 GiB address-space limit, and MALLOC_ARENA_MAX=2. Sampling is every 0.05 seconds. Processes are joined in the foreground. TMPDIR and XDG_CACHE_HOME point to this lane's tmp/. Logs and resource receipts are local. Run calls sequentially:

```sh
python3 -I -B scripts/capped.py reproduce-arithmetic python3 -I -B scripts/recompute.py
python3 -I -B scripts/capped.py reproduce-source python3 -I -B scripts/build_groff.py
python3 -I -B scripts/capped.py reproduce-pdf bash scripts/typeset.sh
python3 -I -B scripts/capped.py reproduce-render pdftoppm -r 110 -png manuscript.pdf qa/reproduced-page
python3 -I -B scripts/capped.py reproduce-text pdftotext -layout manuscript.pdf qa/reproduced-text.txt
```

The executable content source is scripts/paper_content.py; build_groff.py emits manuscript.ms (standalone roff content) and manuscript.md (readable source). scripts/layout.roff plus manuscript.ms are the typesetting source; typeset.sh invokes groff and ps2pdf. These produce the six-page manuscript.pdf. PDF timestamps may differ; mathematical outputs are deterministic. The initial ReportLab attempt found no installed package; the completed route uses only installed command-line tools. Failed-attempt logs remain as provenance, not successful validation.

computations/matrix-N.json contains exact input matrices and complete rational reduced matrices with pivot traces. certificate-contributions.tsv has 20 signed input rows, 32 output columns, and a zero totals row. computations/results.json records every freshly calculated mathematical number used in the paper, including the companion examples, the misprint example, and the poset spanning tests. Bibliographic years, identifiers, theorem labels, hashes and tool versions are source metadata, not purported Python discoveries.

The packet source-only.zip is an unchanged copy of evidence/hetyei-formal-r1/source-only.zip. receipts/safe-extraction.json records member hashes and traversal/symlink rejection checks. packet-safe-extraction/ is inert. receipts/packet-manifest-check.json checks its original internal manifest. No archive member or driver was executed here. Formal replay instructions are preserved in evidence/hetyei-formal-r1/REPRODUCE.md for a separately authorized formal review; they are not part of the above manuscript reproduction.

inputs-before.json and inputs-after.json bind frozen original inputs by campaign-relative path. They must be identical. The copied evidence is separately hash-bound by MANIFEST.sha256. Exact MathDB raw lines remain byte-identical under evidence/expanded-corpus-r240/raw/, with hashes in receipts/mathdb-raw-hashes.json. Primary PDFs, TeX, extracted texts, web receipts, independent-review logs, formal audit logs and root replay/registry receipts are retained in evidence/. The unrelated cached source files from the discovery lane are included for provenance completeness, not cited as mathematical support.

receipts/visual-qa.json records inspection of every final PDF page and binds the PDF and six PNGs. A rerendered or changed PDF requires renewed visual inspection. MANIFEST.sha256 covers dossier payload files (excluding itself, the full ZIP, its external hash, and transient tmp). full-dossier.zip embeds the same payload plus the manifest. full-dossier.zip.sha256 binds the final ZIP. The ZIP is reopened and its member contents checked after creation; see receipts/dossier-package-check.json.

All final acceptance remains pending root review. No ledger update, external posting, or priority assertion is authorized or made.

Packaging clarification: PAYLOAD-MANIFEST.sha256 is the manifest embedded in the ZIP. Packaging logs/receipts and the ZIP's own hash/check receipt are external to that payload to avoid self-reference. After package.py finishes, seal.py creates the external MANIFEST.sha256 over all final files including the ZIP and its verification receipt; it excludes itself, tmp/, and the seal run's active log/receipt. The packaging receipt lists its exact exclusions.
