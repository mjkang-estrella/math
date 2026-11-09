# Offline reproduction

All commands must be run in this authorized lane or a complete copy explicitly
authorized by the operator. No network is needed. Never run the copied discovery,
review or replay scripts as part of this manuscript task: they are historical
evidence and some invoke programs prohibited for this lane.

The package is DRAFT, prepared with AI assistance, and awards zero credit.
Root alone accepts. The two substantive qualifications are stated in the paper.

## Fresh ordinary verification

From this directory, using the already included safe-extracted sources:

```sh
env MALLOC_ARENA_MAX=2 timeout 140s taskset -c 0,1 python3 -I -B verify.py
```

The script itself applies CPU and address-space limits and two-CPU affinity.
It performs no Lean execution and no SAT/ILP search. It regenerates every
pair subword, its two alternation tests, nonedge blockers, all mathematical
counts and numerical provenance coverage. `verification.json` is the full
machine-readable certificate; the paper prints all pair outcomes as a matrix.
`numerical-receipt.json` distinguishes recomputed values from source metadata.
Audit counts are recounted from the historical audit log, not newly kernel-checked.

## PDF generation and rendering

```sh
env MALLOC_ARENA_MAX=2 timeout 140s taskset -c 0,1 python3 -I -B build_paper.py
```

`build_paper.py` plus `pdf_engine.py` is the authoritative manuscript source.
It also generates readable `manuscript.md`. The dependency-free PDF writer
embeds local Liberation Serif regular and bold TrueType fonts. Fonts are read
from `/usr/share/fonts/liberation-serif-fonts/`; their hashes are in the build
receipt. No Python installation or network access is needed. The first attempted
ReportLab build failed because that library is absent; the final build uses
the self-contained writer. No incomplete PDF from the failed attempt is reused.

Render with Poppler, one foreground command at a time, under the same affinity
and timeout, CPU limit 120 s and virtual-memory limit below 2 GiB:

```sh
env MALLOC_ARENA_MAX=2 timeout 140s taskset -c 0,1 bash -c 'ulimit -t 120; ulimit -v 1850000; pdftoppm -r 110 -png manuscript.pdf qa/page'
```

Every rendered page was visually inspected. See `qa/visual-inspection.json`,
the six QA images, and the extracted PDF text. Rebuilding the PDF requires a
new visual inspection; the receipt binds the delivered bytes, not future builds.

## Packet safety and prior formal replays

`lean-packet.tar.gz` has the prescribed SHA-256 in `safe-extraction.json`.
`prepare.py` checks that hash and extracts only the three expected flat regular
files into a fresh directory using exclusive creation. It rejects links,
unexpected names and oversized members. This was actually run. To rerun its
extraction test without modifying the delivered extraction, use `check_package.py`,
which creates and removes a fresh lane-local test directory.

No Lean, lake, leanchecker or solver was run in this manuscript lane. Historical
formal commands and exact toolchain pins are documented in the copied independent
review and root replay scripts/logs. They are provided for later authorized
formal replay, not represented as a fresh replay by this implementation worker.
The independent review and root both report PASS; cached upstream oleans are
trusted. Their historic resource settings differ from this lane's tighter caps.

## Input and package integrity

`inputs-before.json` and `inputs-after.json` cover the complete frozen discovery,
review and root-final directories plus the ruling. `copy-receipt.json` binds
selected source copies back to those inputs. Administrative ancestor files have
a separate ancillary manifest; they are not claim evidence and were first
hashed after their initial read. No shared ledger was changed.

`MANIFEST.sha256` covers every packaged file except itself, ZIPs and archive
receipts. The full ZIP contains that manifest. `archives.sha256` binds both ZIPs;
it remains external to avoid a self-hash cycle. `archive-receipt.json` records
verified ZIP member bytes and CRC tests. `check_package.py` verifies manifest
contents and safe extraction without executing formal code. The paper ZIP is a
convenience subset; the full dossier ZIP includes all source evidence and receipts.

All work runs in the foreground; no jobs remain at handback. No delegation,
git, publishing, uploads, browser tabs, account changes, external messages or
cross-lane writes were used. The first brief-reading command was a short
unwrapped read-only cat; subsequent commands used explicit resource wrappers.
The wrappers bound CPU and address space; reported Python peak RSS is well
below the limit. No persistent watcher or service is used.
