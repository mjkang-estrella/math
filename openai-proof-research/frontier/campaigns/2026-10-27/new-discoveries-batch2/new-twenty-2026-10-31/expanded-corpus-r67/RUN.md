# Reproduction

Run from this lane. Corpus and history inputs are read-only and bound by hash in `results.json` and `outputs/`.

```bash
RG_EXEC=$CLAUDE_CODE_EXECPATH python3 scripts/extract.py      # literal lines, history grep (rg is supplied via RG_EXEC)
python3 scripts/limited.py fetch1 python3 scripts/fetch.py 0 21   # registry HEADs + arXiv HTML (dated receipts)
python3 scripts/limited.py fetch2 python3 scripts/fetch.py 21 45
python3 scripts/textify.py
python3 scripts/limited.py panchromatic python3 scripts/panchromatic.py
PYTHONPATH=<dir containing vendored networkx 3.7> python3 scripts/limited.py tree-gap python3 scripts/tree_gap.py 19
python3 scripts/tour34_sat.py 8 /tmp/t8.cnf && python3 scripts/limited.py tour34-n8 <lean-bin>/cadical -q /tmp/t8.cnf
python3 scripts/limited.py tour34-local-n8 python3 scripts/tour34_local.py 8 110 1
python3 scripts/report.py && python3 scripts/validate.py
```

Lean (371639): from a new directory,

```bash
python3 lean/packet/safe_extract.py lean/source-only-proof.zip fresh
cd fresh
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 replay.py   # refuses existing oleans/receipts; result in replay-receipts/result.json
```

The replay verifies `source-manifest.json` and the binary and Mathlib.olean hashes in `pins.json`. It then builds the six modules with `-j1 -DwarningAsError=true`, runs leanchecker on each, and audits every local declaration (only propext, Classical.choice and Quot.sound are allowed; no unsafe or partial declarations; values must be present). It also checks the `#print axioms` output for both endpoints and runs three rejected `decide` mutations. Every subprocess is capped at 2 CPUs, CPU 120 s and wall 140 s, under a systemd user scope with MemoryMax=6G (probe succeeded) plus a sampled private-RSS guard.

Re-fetching network sources overwrites `sources/` receipts; keep the dated receipts if you replay. Validation (`outputs/validation.json`) checks artifact integrity only, not mathematical acceptance.
