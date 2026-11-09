# Reproduction

Run from this lane. All output paths are derived from each script's own location. Read-only corpus and history sources remain external and are bound in provenance. Preserve existing dated receipts before any fresh network run.

```bash
python scripts/extract.py
python scripts/limited.py fetch1 python scripts/fetch.py 0 12
python scripts/limited.py fetch2 python scripts/fetch.py 12 40
python scripts/textify.py
PYTHONPATH=vendor python scripts/limited.py graph-routes-replay python scripts/graph_routes.py
PYTHONPATH=vendor python scripts/limited.py corona-replay python scripts/corona_mutations.py
python scripts/limited.py interpolation-admissible-replay python scripts/interpolation_admissible.py
python scripts/report.py
python scripts/validate.py
```

Graph experiments use locally installed NetworkX 3.7, NumPy, SciPy and SymPy; interpolation uses NumPy and Python's standard library. The source and registry follow-ups have exact URLs in their receipts; replay them with `scripts/fetch.py`'s `get((filename,url))` function. Web search outputs 2–9 are saved verbatim as returned, with a separate dated hash manifest; search output is a lead, not a read primary proof. The first search's queries and primary links are recorded separately in `outputs/search1-notes.json`; its full tool result was not serialized. No failed access endpoint was retried.

`scripts/report.py` regenerates precisely 40 ID-keyed entries. `scripts/validate.py` checks reservation identity, raw newline and hashes, original corpus line and chunk hashes, source receipt bindings, and absence of claimed credit/Lean endpoints. Validation is artifact integrity only, not mathematical acceptance. No Lean compiler, leanchecker or axiom-audit replay is represented as completed.
