# Acquisition and text-processing jobs

All scripts are actual files in this lane and were invoked with `python -I -B` and their full lane-relative paths from /home/mj-kang/Documents/Dev/math. No external caches were created. HTTP bodies live only in sources/. Python jobs set RLIMIT_CPU=120 seconds and RLIMIT_AS=6 GiB; network calls have18-second timeouts, pdftotext10–15seconds. No mathematical computation/search was executed.

- extract.py: completed, reported CPU0.652seconds and maxRSS558724KiB; extracted20 records. Terminal wall0.50seconds (CPU includes process accounting and is not an exact wall comparison).
- fetch.py abs:23 requests, all200; wall1.24seconds, CPU0.119seconds; completed.
- fetch.py pdf-urls.txt:42 requests, all200; wall3.29seconds, CPU0.218seconds; completed. Original text filename used with_suffix, colliding on arXiv decimal IDs. These ambiguous early .txt files remain as unused intermediate artifacts. passages.py regenerated42 uniquely named version texts from the preserved PDFs; receipts were corrected to point to the unique texts. No mathematical conclusion relies on ambiguous files.
- passages.py:42 serial pdftotext calls; wall2.61seconds, Python CPU0.074seconds; completed. version-passages.txt is an extraction inventory, not an assertion that every line was human/model reviewed.
- history.py first attempt: a per-term rg scan timed out after5seconds; subprocess.run killed and waited for it. No partial historical-search.json from this failed pass was used. Second pass restricted scope to 2026-10-27 campaigns, excluded large routing JSONL, timeout8seconds per term; all20 scans completed. Results include numeric noise explicitly.
- fetch.py extra-urls.txt: original Guo proof URL403; later primary arXiv paper and EMS paper200. Wall1.31seconds; completed. No retry or workaround for403.
- fetch.py registry-urls.txt:three raw HEAD docs200, wall0.23seconds; completed. No GitHub API call.
- report.py: wrote and checked exactly20 dispositions; completed.
- finalize.py: integrity/manifest-only, two-core affinity, completed; output in validation.json.

Resource qualification: early acquisition scripts had4 I/O worker threads and no explicit affinity pin. They were short, low-CPU jobs, but strict two-core instantaneous concurrency for those early calls is not certified. Subsequent script source includes two-core affinity for reproducibility; original runs are not retroactively claimed pinned. All reported RSS values are Python process reports, not whole-process-tree maxima. No job approached120 CPU seconds/140wallseconds/6GiB by observed output. No background job was launched; interactive exec session IDs were all reaped to exit. No solver, Lean, heavy enumeration or numerical execution occurred.
