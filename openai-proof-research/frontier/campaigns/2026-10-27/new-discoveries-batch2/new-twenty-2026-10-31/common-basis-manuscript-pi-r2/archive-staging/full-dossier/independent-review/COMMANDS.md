# Commands and exits

All commands executed from the campaign batch directory, all outputs confined to common-basis-source-review-r1. Read-only shell `cat`, `sed`, `rg`, `head`, `tail`, `ls` inspected author, ancestor instructions, ledger, local family/exclusion data, and pinned Mathlib constructor. No git commands were run.

Python invocations (all actual file paths, all -I -B, all exit 0):

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 taskset -c 0,1 python3 -I -B common-basis-source-review-r1/check.py > common-basis-source-review-r1/math.log 2>&1
python3 -I -B common-basis-source-review-r1/fetch.py > common-basis-source-review-r1/fetch.log 2>&1
python3 -I -B common-basis-source-review-r1/literature.py > common-basis-source-review-r1/literature-fetch.log 2>&1
python3 -I -B common-basis-source-review-r1/registry-extra.py > common-basis-source-review-r1/registry-extra.log 2>&1
python3 -I -B common-basis-source-review-r1/analyze.py > common-basis-source-review-r1/analyze.log 2>&1
python3 -I -B common-basis-source-review-r1/followup.py > common-basis-source-review-r1/followup.log 2>&1
python3 -I -B common-basis-source-review-r1/deepen.py > common-basis-source-review-r1/deepen.log 2>&1
python3 -I -B common-basis-source-review-r1/parse-more.py
python3 -I -B common-basis-source-review-r1/finish-fetch.py > common-basis-source-review-r1/finish-fetch.log 2>&1
python3 -I -B common-basis-source-review-r1/final-registry.py > common-basis-source-review-r1/final-registry.log 2>&1
python3 -I -B common-basis-source-review-r1/run-capped.py
python3 -I -B common-basis-source-review-r1/objections.py
python3 -I -B common-basis-source-review-r1/finalize.py > common-basis-source-review-r1/finalize.log 2>&1
```

`run-capped.py` records its exact absolute child command, limits, exit and measured RSS in math-capped.receipt.json; full stdout/stderr is math-capped.log. No Lean command ran. Initial 0.1s ordinary check had CPU affinity but no rlimit wrapper; it was rerun with all guards. All other Python jobs are light I/O/parsing and exact hash comparisons. Fetch scripts store full bodies and per-request status, UTC and SHA256 receipts. Two registry processes partly reused the same lane-local read-only response cache; the stable same-URL bodies are retained, not authority over mutable author files.

`pdftotext -layout` converted lane-local blasiak.pdf, bonin.pdf, workshop.pdf, lason-michalek.pdf into corresponding lane-local .txt files (all exit 0). Source-reading extracts preserve Unicode; mathematical symbols split across lines in extracted HTML should be read with the retained original body. Public web searches used the web tool; final four-query returned data is search-results.json, with timestamp and exact queries. Earlier exploratory search results were used to locate primary bodies, not as missing-body clearance. No browser or server was started.

Sessions for fetch, literature, registry-extra, followup, deepen and final-registry were joined and exited before final handback. No uncontrolled background job remains.
