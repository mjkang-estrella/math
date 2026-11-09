# Reproduce the contact refutation

The proof archive is `contact-source-only.zip`. Use a NEW empty extraction directory. Reject absolute paths, `..` components and symbolic links before extraction. Verify `SOURCE-MANIFEST.json` (SHA-256 of every source member). The dossier records the safe extraction used for this run in `receipts/extraction.json`.

Set `LEAN_BIN` to the Lean **executable**, e.g. `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, and `LEAN_PACKAGES` to `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`. Pins are in `pins.json`. A different installation must provide matching versions of all cached packages, with their `.lake/build/lib/lean` trees. Then run from the extraction:

```sh
python3 -I -B scripts/replay-r5.py
```

The driver refuses any existing `.olean`, `.ilean`, `.ir` or build directory, compiles all 28 modules serially with `-j1 -DwarningAsError=true`, and runs one leanchecker module per process. It audits all local declarations, including opaque bodies, unsafe/partial flags, `_unsafe_rec` names and transitive axioms. Only propext, Classical.choice and Quot.sound are allowed. The thirteen negative controls must each fail with exit 1, without watchdog termination. Successful replay ends with a PASS line and `replay-logs/complete.json`. This manuscript driver's watchdog samples aggregate process-group RSS (the inherited driver sampled private memory); its audit explicitly rejects compiler-generated unsafe recursion names. All Lean modules are unchanged.

Every Lean/checker call: at most 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB, MALLOC_ARENA_MAX=2. One heavy process runs at a time. The replay driver orchestrates many separately capped calls, so the complete replay takes longer than any individual cap. Leave no child processes running.

The fresh run is retained under `work/extracted-01/replay-logs` in the working lane; portable copies of its logs and receipts are under `receipts/fresh-replay` in the full dossier. Audit DAG logs can be large. The full ZIP intentionally omits compiled artifacts and the duplicate extraction tree, and contains the proof source archive, paper, sources, evidence, manifests and receipts.

To rebuild the paper, install ReportLab in an existing Python environment and run `python3 -B paper/build_paper.py`. It reads `paper/contact-draft.md` and uses Liberation Serif and Mono fonts (override FONT_DIR if necessary). Render all pages with `pdftoppm -r 110 -png paper/contact-draft.pdf qa/page`. The retained QA receipt documents visual inspection. Dependencies are external and are not bundled.

The source archive is a minimal Lean replay packet. The full dossier also contains the ordinary proof and manuscript source. Root alone decides acceptance. No priority or accepted-credit claim is made.
