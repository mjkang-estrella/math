# Final source-only review packet

Independent final review completed; this is the root-prepared outcome36 acceptance edition. Final campaign acceptance and exact hashes are recorded in the separate acceptance receipt. One outcome only; no extra helper or formalization credit.

Extract `steiner-final-review-packet.zip` into a new directory. From there run:

```
python reproduce.py /absolute/new/replay-directory /absolute/original/steiner-final-review-packet.zip
```

The destination must not exist. This validates the payload manifest; asserts the exact Lean binary hash and version 4.34.1; rebuilds the PDF using pinned Tectonic with `--only-cached --untrusted` and fixed SOURCE_DATE_EPOCH; asserts PDF byte identity; regenerates and compares the final ZIP; then freshly extracts and replays the immutable original source-only formal component. All six mathematical modules and the exhaustive actual-origin audit are rebuilt serially. Its script checks all nine package revisions and imported upstream source/cache hashes before compilation. No Lake, dependency fetching or upstream mutation is performed. The actual audit log must be byte-identical to root's saved audit. Read both replay-receipt.json and final-packet-receipt.json and all seven stage logs. All six math logs must be empty.

The included component's six mathematical modules and OriginAudit.lean are byte-identical to root's immutable archive SHA256 7065840eed6aab457eb9e50e5c59e04aed5c8e37433d8063bc815f6c6707ba61. Nothing compiled from this candidate is included, even in the nested archive. Logs/receipts/PDF are review evidence, not Lean build inputs. `component/REPRODUCE.md` describes the original formal replay; the top-level instructions add manuscript and final-package checks. `package.py` rebuilds the final archive without consulting or rehashing mutable upstream caches. `component` is the implementation agent's own extraction of root's frozen archive.

This is a runner for the supplied pinned local environment, not a vendored standalone distribution of Lean/mathlib/TeX. Absolute local tool/package paths are explicit in component/pins.json and authoring-pins.json. A different machine must provision equivalent pinned caches and deliberately adapt paths; byte identity is tested in the supplied environment. Tectonic uses the existing offline TeX cache; the binary/version and fixed epoch are recorded, but this does not independently attest or rebuild the TeX cache. Lean imported source/olean hashes are recorded in component/dependency-hashes.json; this freezes reuse, not rebuilding upstream from public commits.

Resource policy: each Lean stage -j1, -M2700, warningAsError=true, autoImplicit=false; process-group RSS hard kill threshold 2800MiB at target .045-second sampling; CPU210s/wall230s per stage; file output64MiB. Python helpers AS soft512MiB, CPU210s/file64MiB and explicit wall alarms; only the separate Lean launch may reset AS, via an unlimited hard ceiling. BLAS/OMP/MKL thread counts are one. Sampling cannot exclude unsampled RSS transients. Split work rather than raise limits if a stage fails.

Inherited failure: the initial broad Mathlib.Tactic import was killed at sampled 2888552KiB above ceiling2867200KiB. Selective imports fixed it without raising caps. The original development log was overwritten and is unavailable; this is a disclosed inherited observation, not a retained raw-log measurement. The source worker's summaries and resource disclosures are preserved under evidence/. No resource failure occurred in this lane's fresh replay. Initial manuscript layout had a references-only fourth page; it was revised to three pages and every final page visually inspected. First layout renders remain outside the final packet as local work history.

Source arXiv v1 SHA2562475bf1990f404e2bd6bd7e5badf618aaa6dca55199b5648d405aa792c06bab5; metadata May15 versus internal June13,2025 retained. Inherited current-prior screen is preliminary; no journal version located, no claimed VoR comparison or worldwide priority. No external access or contact in this implementation lane. Final independent review must refresh these gates.
