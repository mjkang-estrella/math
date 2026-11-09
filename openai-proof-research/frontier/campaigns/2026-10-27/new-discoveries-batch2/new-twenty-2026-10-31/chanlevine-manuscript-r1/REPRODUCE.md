# Reproduce this draft dossier

Status: DRAFT, zero accepted credit. Run only from this lane. No Lean, lake, or leanchecker was run here; the commands below do not run them. The independent root replay is a separate responsibility.

## Document and numerical checks

Python 3 and system Poppler (`pdftoppm`, `pdfinfo`) are required. `tmp/pdf-deps` preserves the local model dossier's ReportLab/Pillow dependency bundle; the renderer adds this directory to its import path. Fonts are included. This bundle was copied locally, without installation or network access; its provenance hashes are in dependency-inputs.json. Do not interpret third-party renderer code as part of the mathematical proof.

From this directory, run sequentially:

```
python3 -B scripts/cap.py python3 -B scripts/check_math.py
python3 -B scripts/cap.py python3 -B scripts/render.py
python3 -B scripts/cap.py pdftoppm -r 100 -png paper.pdf qa/page
```

The cap driver uses two available CPUs, a CPU limit of 120 seconds, wall limit of 140 seconds, sampled process-group RSS ceiling of 6 GiB, an additional 6 GiB address-space limit, and MALLOC_ARENA_MAX=2. It sets lane-local TMPDIR and XDG_CACHE_HOME. Each invocation retains a JSON receipt in logs/. Run only one heavy command at a time. Sampling cannot exclude sub-sample RSS transients. Re-rendering may alter PDF metadata; it must reproduce the mathematical text and layout, not a byte-identical PDF. Visually inspect every new page image. The supplied qa/receipt.json records the delivered version's actual inspection.

check_math.py independently enumerates natural chip/rotor configurations and compares them with an integer coefficient/Ramanujan-sum formula in 16 cases. It additionally enumerates the four Table 8.1 rows n=3..6, and compares the formula to all six source rows n=3..8. These checks are diagnostics, not a general proof.

## Frozen formal packet

chanlevine-assembly-source.zip must have SHA-256
9e685235e4d744adf9fdd5cafaccf874c6ef6fbccff4684003133df75da34bb0.
It is reused BYTE-IDENTICALLY. safe-extraction.json inventories a fresh path-checked extraction to proof-packet-safe/. All 75 .lean files are present, with no compiled Lean files. No archive member was executed. scripts/prepare.py documents the original copying/extraction; it intentionally refuses to reuse an existing extraction directory. Do not rerun it over the delivered tree.

The packet pins Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Endpoint: ChanLevine.mathdb_338887; corollary: ChanLevine.recurrent_count_depends_only_on_gcd. See the preserved assembly REPRODUCE.md and replay scripts inside the packet for root's separately authorized fresh replay. They depend on absolute local tool/cache paths and are not a self-contained mathlib distribution. This manuscript task explicitly forbids executing that replay. Root's separate replay-result.json subsequently arrived and reports PASS; it is preserved under evidence/chanlevine-parent-final-r1/. That reported result is distinguished from checks run here.

## Provenance and integrity

frozen-before.json and frozen-after.json bind every designated frozen input. optional-before.json and optional-after.json bind the available fidelity reports. input-integrity.json records equality. SOURCE-COPIES.json maps original paths to copied evidence, with hashes; the source texts and receipts retain their original bytes. The raw MathDB JSONL is preserved exactly (including its newline and historical metadata), not regenerated from parsed JSON. Its hash and original shard/line provenance are in raw-record-provenance.json.

DOSSIER-MANIFEST.json inventories every packaged member except itself and external delivery receipts. chanlevine-full-dossier.zip embeds that manifest; scripts/package.py creates and verifies all member bytes and safe names. package-validation.json and DELIVERY-SHA256.json sit outside the ZIP to avoid self-reference. A rerun of the packager updates these receipts. No root acceptance, fresh novelty clearance, or published-AMS full-body access is claimed.
