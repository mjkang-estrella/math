# Reproduction and limits

Run in this directory. Standard-library Python, Poppler pdftotext/pdftoppm. No downloaded Python dependencies. Each expensive process was confined to CPUs 0,1 with taskset and 1GiB per-process address space with prlimit; CPU and wall limits are explicit below. These are process limits, not a sampled aggregate-RSS guarantee. All source work was serial within its process. Full stdout/stderr logs are retained, including failures. Initial cheap file discovery/read commands were not resource-intensive sweeps.

```
taskset -c 0,1 prlimit --as=1073741824 --cpu=45 timeout 60s python -B intake.py > intake.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=45 timeout 140s python -B fetch.py > fetch.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=20 timeout 30s python -B registry.py > registry.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=35 timeout 55s python -B fetch-pme.py > fetch-pme.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=35 timeout 55s python -B fetch-pme-slides.py > fetch-pme-slides.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=40 timeout 50s python -B mst.py > mst.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=20 timeout 25s pdftoppm -f 9 -l 10 -scale-to 1300 -png sources/livingston.pdf sources/livingston-page > render.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=30 timeout 40s python -B finalize.py > finalize.log 2>&1
taskset -c 0,1 prlimit --as=1073741824 --cpu=45 timeout 60s python -B verify.py > verify.log 2>&1
```

For an offline read-only check run **only verify.py**. intake.py regenerates the initial per-ID skeleton and finalize.py then adds dispositions; do not run intake alone on a final packet. Do not rerun network acquisition after a denied route; compare retained source bytes instead. Scripts write only this directory. No no-hit search is a novelty proof.

Bounded web locator queries: random minimum spanning tree most likely grid tree probability maximizer; degenerate nonlinear diffusion concentration sphere hypersurface long time; stable four genus knot less than one half Livingston; exact Tapp paper title with arxiv; degenerate diffusion concentration on a sphere; porous medium equation Barenblatt solution explicit formula m 2 Vazquez pdf. Search-result snippets are not retained/hash-bound proof evidence. Main successful primary URLs and acquisition statuses are in sources/*.receipt.json; no hash invented for the failed TLS body.

Retained failures: one display helper assumed literal_statement for r398 (which uses statement) and failed before reading; corrected using explicit field fallback. Several broad display outputs were truncated; no full reading inferred from those displays. Compact forty-ID statement/objection display was complete. One source-reading filename used wrong case and was corrected. The combined mst/read command returned 1 because the PME text did not exist after its TLS failure; mst.py itself completed and its full output is retained. No mathematical conclusion was taken from a failed command. No increase of process limits or bypass occurred.
