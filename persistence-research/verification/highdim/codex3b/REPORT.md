# Codex3b final research report

**PROVED (checked certificate covers), COMPUTED (counts).**
Assigned: 332 configurations of t=14112; closed: 7; still open/BUDGET: 325.
7 ordinary nd certificates passed both checkers directly: 14 PASS verdicts. No new kill type and no checker changes.

Every closed configuration has an independently replayed E slice cover and complete far-digit ordering coverage. All generated certificates, including any partial configuration slices, were checked. Each closed configuration is covered from its original qmin=3 domain, so no finite exceptional placement is left. The prior E lattice enumeration through 600 digits is hashed for context and was not rerun.

Closed keys:
- `103|45,45,54,54`
- `112|18,54,54,63`
- `133|18,18,54,54`
- `37|54,54,72`
- `556|9,27,54`
- `676|9,18,45`
- `716|9,54,72`

Files:
- `summary.json`: exact closed/open lists.
- `share.json` and `baseline.json`: exact original assignment and source hash.
- `results_t14112.json`, `stage_*.json`, and logs: checkpointed attempts and diagnostics.
- `certs/t14112/`: complete certificate trees only.
- `checker_results.json`, `logs/checks/`: direct checker commands, hashes, verdicts and timings.
- `coverage_summary.json`, `independent_coverage.json`: slice/domain/order audit.
- `supply_search.json`, `supply_extended.json`, `period_strengths.json`: prime supply work.
- `manifest.json`: hashes.

All remaining configurations are BUDGET; no nonexistence claim follows. No files outside codex3b and notes/highdim_codex3b.md were written by this continuation. No git commit was made.
