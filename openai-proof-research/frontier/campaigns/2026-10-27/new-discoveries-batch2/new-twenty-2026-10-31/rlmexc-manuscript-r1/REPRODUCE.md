# Reproduction (DRAFT)

All paths are relative to this dossier. Use a writable copy of the whole dossier in the assigned lane. Nothing here needs the network. Do not run scripts from inputs/ or safe-extracted/ during manuscript reproduction. All fresh numerical computations use standard-library Python, not the supplied discovery scripts.

Run each command sequentially and wait for completion:

```
python3 -I scripts/cap.py family python3 -I scripts/recompute.py family
python3 -I scripts/cap.py small python3 -I scripts/recompute.py small
```

For each j from 1 through 10, in order, run the following command with j replaced by its integer value (one process at a time):

```
python3 -I scripts/cap.py n10-j python3 -I scripts/recompute.py chunk j
```

Then:

```
python3 -I scripts/cap.py aggregate python3 -I scripts/recompute.py aggregate
python3 -I scripts/cap.py safe-extract python3 -I scripts/safe_extract.py
```

The cap driver sets affinity to two allowed CPUs, CPU 120 s, wall kill at 135 s (below 140 s), address-space 6 GiB and sampled child RSS at 6 GiB, MALLOC_ARENA_MAX=2, no core dumps, lane-local HOME/TMPDIR/cache and explicit -B bytecode suppression. It waits for each child and retains command, return code, wall time and sampled RSS in receipts/. The memory address-space limit is an additional conservative bound. There is no solver or Lean invocation. Sampling covers the direct process; these numerical scripts do not spawn children. Do not invoke several cap drivers concurrently.

## PDF source and tools

manuscript.xml is the editable manuscript; scripts/build_pdf.py generates its tables directly from fresh outputs. It uses the installed read-only Codex runtime Python with ReportLab, plus Noto Serif, Noto Sans Math and Liberation fonts. The ordinary system Python lacks ReportLab; unsuccessful initial build receipts were replaced by the successful final build receipt. No dependency was downloaded. The renderer can be rerun with:

```
python3 -I scripts/cap.py build-pdf /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -I scripts/build_pdf.py
python3 -I scripts/cap.py render pdftoppm -r 110 -png manuscript.pdf qa/page
```

On another machine adapt the documented interpreter and font paths to an existing local installation. No generated Python environment is required for numerical reproduction. PDF timestamps can change; numerical JSON and the preserved Lean ZIP are the scientific reproducibility targets. After rendering, inspect every page again; the existing visual-qa receipt describes this delivered PDF only. scripts/finish.py checks the printed numerical claims and creates supporting text and raw-line receipts; it also writes the QA receipt and must only be used after the described actual visual inspection.

## Frozen inputs and Lean trust boundary

receipts/input-hashes-before.json and input-hashes-after.json bind the original read-only inputs. Their absolute paths identify this campaign's evidence. inputs/ contains copied primary PDF/text, v3 TeX, v1/v2 sources, nearby paper TeX, the review and its fetch receipts, root ruling/check and inherited replay/registry results. Copied inputs retain their original names and bytes. The exact raw line is also at mathdb-350721.jsonl.

lean-source.zip is byte-identical to rlmexc-formal-r1/source.zip; expected SHA-256:
82262a7aa3f6548ebe9e15c3d8f0fef0feb120c5f0f45cc4a6e31eb6a3840a75.
Safe extraction checks member paths, duplicate names, symlinks and total size, then compares the packet hash and module order without executing any packet code. safe-extracted/ is for inspection only. The nine-module endpoint is AK350721.conjecture_refuted. The infinite family is not formalized.

This lane did not run Lean, lake or leanchecker. The included parent replay-result.json reports PASS, and registry-refresh.json reports CLEAN with its explicit path-screen limits. The formal lane's original REPRODUCE.md describes a future Lean replay in a separately authorized environment; it is retained as evidence, not an instruction to run Lean under this task.

## Integrity and status

MANIFEST.sha256 covers the delivered files except itself, ZIPs and their checksum file. full-dossier.zip packages those files and the manifest. archives.sha256 binds both ZIP deliverables. paper-source.zip contains the editable source, renderer, fresh numerical inputs and this reproduction guide. No acceptance, publication or novelty adjudication is performed.

Process limitations: initial read-only inventory/source-reading commands and shell file edits were not launched through the numerical cap driver; they were small foreground operations. Input hashing began after initial source inspection, rather than before the first read. Thereafter the 242-file frozen set was copied and checked at handback. All numerical computation, PDF creation, rendering and packaging ran under the cap driver. The failed system-Python ReportLab import DID write bytecode caches outside the lane, because -I ignored PYTHONDONTWRITEBYTECODE. See receipts/outside-lane-bytecode-violation.json for the observed files. No cleanup outside the lane was attempted. The wrapper now explicitly inserts -B for Python child commands, and the PDF source sets sys.dont_write_bytecode=True. No child agents, git, network, prohibited solver or prohibited formal tool was used; the external bytecode-cache writes violate the write-only-in-lane requirement and require root assessment.

The late-written receipts/cap-package.json is also excluded from the internal manifest to avoid a packaging self-reference; it records the packaging command's successful completion. Scratch files under tmp/ are excluded. Both ZIPs were reopened and CRC-tested. The exact archive checksums reside alongside the archives rather than inside the full-dossier ZIP.
