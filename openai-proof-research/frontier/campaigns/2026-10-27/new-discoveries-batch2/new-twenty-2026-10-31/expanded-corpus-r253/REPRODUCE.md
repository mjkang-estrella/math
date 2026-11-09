# Reproduction

Run scripts by their actual absolute paths with `python -I -B`. Every output is relative to the script's own directory. No Lean installation/build is needed.

1. `intake.py` binds the reserved IDs to complete corpus chunk bytes and one-based raw lines. It writes the exact JSONL lines with their newline.
2. `prepare.py` computes literal statement hashes and the initial HTTP plan. `fetch.py PLAN.json` performs ordinary verified-TLS public HTTP requests and saves URL, time, status, final URL, headers and SHA256 receipts; inherited denied hosts are skipped. Do not rerun a failed/denied host to bypass its response. Its existing-output guard makes receipts reusable.
3. `texts.py` extracts PDF text with Poppler. `registry.py`, `targetplan.py`, `deepplan.py`, `narrow.py`, `finalscreen.py`, and `rawplan.py` record the registry search boundaries; they are discovery steps with sequential dependencies. The initial broad `registry-plan.json` and `deep-plan.json` were NOT executed wholesale. `narrow-plan.json` was the chosen smaller plan.
4. `report.py` regenerates results, source/text inventories and bounded historical/catalogue screens. It does not run mathematical searches or certify proofs. `final-check.py` verifies all 20 provenance bindings and writes the final manifest.

Use `cap.py NAME python -I -B ABSOLUTE_SCRIPT [arguments]` to cap an invoked script at 2 CPUs, CPU 120 seconds, wall 140 seconds and address space 6 GiB. Earlier collection runs used this hard address-space cap but did not sample RSS; this telemetry limitation is explicit. The final checker uses the revised sampled-RSS wrapper. All collection processes completed before handback. No background mathematical search was started.

The source PDF named `dendrimer2014.pdf` is actually a Yuan–Ding finite-field paper; never cite it as the missing 2014 dendrimer source. The guessed `spectrum2018-abs.html` is unrelated boundary-CFT literature and unused. `pool-raw.json` is a failed guessed path, superseded by actual tree-listed candidate indexes. Preserve these receipts to make mistakes visible.

HTTP receipts and hashes make the bounded review reproducible; they cannot certify global novelty or complete literature coverage.
