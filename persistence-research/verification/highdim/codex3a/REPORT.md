# Codex 3a final report

**PROVED** denotes complete independently checked covers; **COMPUTED** denotes executed finite work.

| target | assigned | closed | still open |
|---:|---:|---:|---:|
| 32 | 2 | 1 | 1 |
| 14112 | 333 | 6 | 327 |

**COMPUTED.** 7 certificates pass BOTH checkers directly; verdicts: {'PASS': 14}. Commands run the copied `checkhd.py` and original `verification/v14_checknd_hd.py` with `python3 -I -B`, no wrapper or builtin changes. All exclusion kills are ordinary prime kills. No new kill type or checker acceptance change was introduced.

**COMPUTED.** The adopted certificates contain 1735570 nodes and 361415202 full partition lifts. No new actual member occurs in these closed configurations.

**PROVED.** Every closure passes an independent E/E2 slice and ordering audit. The maximum independent slice floor is 3. Every adopted certificate has the original K and all four far positions free with floor 3. A genuine placement therefore has L>=7 and there is no short-length gap. Existing finite-enumeration hashes are included for context; no new finite sweep was needed.

**COMPUTED.** The exact 333-key zero-based EVEN assignment, with original indices and input hash, is in `assignment.json` and `notes/highdim_codex3a.md`. Every assigned configuration was attempted. Search history, including completed records from interrupted exploratory passes, is checkpointed in `history.jsonl`. BUDGET means open: it is not a nonexistence proof. No claim about the general persistence conjecture follows.

Files: `results_t32.json`, `results_t14112.json`, `coverage_summary.json`, `checker_results.json`, `cert_stats.json`, `certs/`, `logs/checks/`, `depth_diagnosis.json`, `supply_scan.json`, and `manifest.json`. Direct replay commands and certificate hashes are recorded in `checker_results.json`.
